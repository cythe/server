/*
   Copyright (c) 2009, 2021, MariaDB

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; version 2 of the License.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1335  USA */


#ifdef USE_PRAGMA_IMPLEMENTATION
#pragma implementation				// gcc: Class implementation
#endif

#include "mariadb.h"
#include "sql_priv.h"
#include <m_ctype.h>
#include "sql_select.h"
#include "opt_trace.h"

/**
  @file

  @brief
    Virtual Column Substitution feature makes the optimizer recognize
    and make use of virtual column expresions in the WHERE/ON clauses.
*/


/*
  == Virtual Column Substitution feature ==

  It makes the

  CREATE TABLE t1 (
     json_col BLOB,
     ...
     vcol1 varchar(100) AS (json_extract(json_col, '$.name')),
     INDEX idx1(vcol1)
  );

    SELECT * FROM t1 WHERE json_extract(json_col, '$.name')='foo'

  We'd like this query to use index idx1.
  In order to achieve that, we look through potentially sargable conditions
  to find the virtual column expression and replace it with a reference to
  virtual column field so the above becomes:

    SELECT * FROM t1 WHERE vcol1='foo'

  == Datatypes must match ==

  The type of vcol_field and vcol_expr may not match. Consider

  CREATE TABLE t1 (
    a varchar(10),
    vcol INT as CONCAT(a,'1')
  );

  and conditions

    concat(a,'1')=1.5  vs  vcol=1.5.

  == The same expression in multiple virtual columns ==

  What if there are multiple options to replace:

  CREATE TABLE t1 (
     col1 int,
     ...
     vcol1 INT as (col1 + 1),
     vcol2 INT as (col1 + 1),
     ...
     INDEX idx1( .. vcol1 ..)
     INDEX idx2( .. vcol2 ..)
  );

  Current patch will replace the expression with the first column, like MySQL
  does. Since we rely on the user defining the virtual columns, we can
  request that they define one virtual column instead of multiple identical
  ones.

*/

class Vcol_subst_context
{
 public:
  THD *thd;
  /* Indexed virtual columns that we can try substituting */
  List<Field> vcol_fields;

  /*
    How many times substitution was done. Used to determine whether to print
    the conversion info to the Optimizer Trace
  */
  uint subst_count;

  Vcol_subst_context(THD *thd_arg) : thd(thd_arg) {}
};


static
void collect_indexed_vcols_for_table(TABLE *table, List<Field> *vcol_fields)
{
  for (uint i=0; i < table->s->keys; i++)
  {
    // note: we could also support histograms here
    if (!table->keys_in_use_for_query.is_set(i))
      continue;

    KEY *key= &table->key_info[i];
    for (uint kp=0; kp < key->user_defined_key_parts; kp++)
    {
      Field *field= key->key_part[kp].field;
      if (field->vcol_info)
        vcol_fields->push_back(field);
    }
  }
}


/*
  Collect a list of indexed virtual columns in the JOIN's tables
*/

static
void collect_indexed_vcols_for_join(JOIN *join, List<Field> *vcol_fields)
{
  List_iterator<TABLE_LIST> ti(join->select_lex->leaf_tables);
  TABLE_LIST *tl;
  while ((tl= ti++))
  {
    if (!tl->table) // non-merged semi-join or something like that
      continue;
    collect_indexed_vcols_for_table(tl->table, vcol_fields);
  }
}


/* Substitute virtual columns in an Item tree */
static void subst_vcols_in_item(Vcol_subst_context *ctx, Item *item,
                                const char *location)
{
  uchar *yes= (uchar*) 1;
  ctx->subst_count= 0;

  item->top_level_compile(ctx->thd,
                          &Item::vcol_subst_analyzer, &yes,
                          &Item::vcol_subst_transformer, (uchar*)ctx);

  if (ctx->subst_count && unlikely(ctx->thd->trace_started()))
    trace_condition(ctx->thd, location, "virtual_column_substitution", item);
}


static
void subst_vcols_in_join_list(Vcol_subst_context *ctx,
                              List<TABLE_LIST> *join_list)
{
  TABLE_LIST *table;
  List_iterator<TABLE_LIST> li(*join_list);

  while ((table= li++))
  {
    if (NESTED_JOIN* nested_join= table->nested_join)
      subst_vcols_in_join_list(ctx, &nested_join->join_list);

    if (table->on_expr)
      subst_vcols_in_item(ctx, table->on_expr, "ON expression");
  }
}


/*
  Walk expressions and substitute virtual column references with
  virtual columns.
*/

void substitute_indexed_vcols_for_join(JOIN *join)
{
  Vcol_subst_context ctx(join->thd);
  collect_indexed_vcols_for_join(join, &ctx.vcol_fields);
  if (!ctx.vcol_fields.elements)
    return;

  if (join->conds)
    subst_vcols_in_item(&ctx, join->conds, "WHERE");
  if (join->join_list)
    subst_vcols_in_join_list(&ctx, join->join_list);
}


/*
  Entry-point for single-table UPDATE/DELETE.
*/

void substitute_indexed_vcols_for_table(TABLE *table, Item *item)
{
  Vcol_subst_context ctx(table->in_use);
  collect_indexed_vcols_for_table(table, &ctx.vcol_fields);

  if (!ctx.vcol_fields.elements)
    return;

  if (item)
    subst_vcols_in_item(&ctx, item, "WHERE");
}


/*
  @brief
    Check if passed item matches Virtual Column definition for some column in
    the Vcol_subst_context list.
*/

static Field *is_vcol_expr(Vcol_subst_context *ctx, const Item *item)
{
  table_map map= item->used_tables();
  if ((map!=0) && !(map & OUTER_REF_TABLE_BIT) &&
      !(map & (map - 1))) // has one bit set
  {
    List_iterator<Field> it(ctx->vcol_fields);
    Field *field;
    while ((field= it++))
    {
      if (field->vcol_info->expr->eq(item, true))
        return field;
    }
  }
  return NULL;
}


/*
  @brief
    Produce a warning similar to raise_note_cannot_use_key_part().
*/

void print_vcol_subst_warning(THD *thd, Field *field, Item *expr,
                              const char *cause)
{
  StringBuffer<128> expr_buffer;
  size_t expr_length;

  expr->print(&expr_buffer, QT_EXPLAIN);
  expr_length= Well_formed_prefix(expr_buffer.charset(),
                                  expr_buffer.ptr(),
                                  MY_MIN(expr_buffer.length(), 64)).length();

  push_warning_printf(thd, Sql_condition::WARN_LEVEL_NOTE,
                      ER_UNKNOWN_ERROR,
                      "Cannot substitute virtual column expression %*s -> %*s "
                      "due to %s",
                      expr_length, expr_buffer.c_ptr_safe(),
                      (int) field->field_name.length, field->field_name.str,
                      cause);
}


static
bool subst_vcol_if_compatible(Vcol_subst_context *ctx,
                              Item_bool_func *cond,
                              Item **vcol_expr_ref,
                              Field *vcol_field)
{
  Item *vcol_expr= *vcol_expr_ref;
  THD *thd= ctx->thd;
  /*
    Do not do the substitution if the datatypes do not match.
    Virtual column's datatype can be different from the expression, for
    example:

      col3 INT AS (CONCAT(col1, col2))

    Do not allow substitutions that change the semantics of comparison.
    At the moment, we require that datatypes are the same.
    This probably could be relaxed.

    For strings: we allow two cases:
    - vcol_expr and vcol_field have the same collation.
    - vcol_field has the same collation as the comparison collation.

    (Note: MySQL calls resolve_type() after it has done the substitution.
     This can potentially update the comparator. The idea is that this
     shouldn't be necessary as we do not want to change the comparator.
     Changing the comparator will change the semantics of the condition,
     our point is that this must not happen)
  */
  const char *fail_cause= NULL;
  if (vcol_expr->type_handler_for_comparison() !=
      vcol_field->type_handler_for_comparison() ||
      vcol_expr->maybe_null() != vcol_field->maybe_null())
    fail_cause="type mismatch";
  else
  if (vcol_expr->collation.collation != vcol_field->charset() &&
      cond->compare_collation() != vcol_field->charset())
    fail_cause="collation mismatch";

  if (fail_cause)
  {
    if (thd->give_notes_for_unusable_keys())
      print_vcol_subst_warning(thd, vcol_field, vcol_expr, fail_cause);
    return true;
  }
  Item_field *itf= new (thd->mem_root) Item_field(thd, vcol_field);
  if (!itf)
    return true;
  DBUG_ASSERT(itf->fixed());
  thd->change_item_tree(vcol_expr_ref, itf);
  ctx->subst_count++;
  return false;
}


Item* Item_bool_rowready_func2::vcol_subst_transformer(THD *thd, uchar *arg)
{
  DBUG_ASSERT(this->vcol_subst_analyzer(NULL));
  Vcol_subst_context *ctx= (Vcol_subst_context*)arg;
  Field *vcol_field;
  Item **vcol_expr;

  if (!args[0]->used_tables() && (vcol_field= is_vcol_expr(ctx, args[1])))
    vcol_expr= &args[1];
  else if (!args[1]->used_tables() && (vcol_field= is_vcol_expr(ctx, args[0])))
    vcol_expr= &args[0];
  else
    return this; /* No substitution */

  subst_vcol_if_compatible(ctx, this, vcol_expr, vcol_field);
  return this;
}


Item* Item_func_between::vcol_subst_transformer(THD *thd, uchar *arg)
{
  Vcol_subst_context *ctx= (Vcol_subst_context*)arg;
  Field *vcol_field;
  if (!args[1]->used_tables() &&
      !args[2]->used_tables() &&
      (vcol_field= is_vcol_expr(ctx, args[0])))
  {
    subst_vcol_if_compatible(ctx, this, &args[0], vcol_field);
  }
  return this;
}


Item* Item_func_null_predicate::vcol_subst_transformer(THD *thd, uchar *arg)
{
  Vcol_subst_context *ctx= (Vcol_subst_context*)arg;
  Field *vcol_field;
  if ((vcol_field= is_vcol_expr(ctx, args[0])))
  {
    subst_vcol_if_compatible(ctx, this, &args[0], vcol_field);
  }
  return this;
}


Item* Item_func_in::vcol_subst_transformer(THD *thd, uchar *arg)
{
  Vcol_subst_context *ctx= (Vcol_subst_context*)arg;

  /* Check that all arguments inside IN() are constants */
  if (!compatible_types_scalar_bisection_possible())
    return this;

  Field *vcol_field;
  if ((vcol_field= is_vcol_expr(ctx, args[0])))
  {
    subst_vcol_if_compatible(ctx, this, &args[0], vcol_field);
  }
  return this;
}

