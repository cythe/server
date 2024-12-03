INCLUDE(generate_submodule_info)
INCLUDE(ExternalProject)

# Remove all matches from a cmake list
FUNCTION (REMOVE_ALL_MATCHES list_var_name match_str)
  SET(new_list)
  FOREACH(el ${${list_var_name}})
    IF(NOT("${el}" MATCHES "${match_str}"))
      LIST(APPEND new_list ${el})
    ENDIF()
  ENDFOREACH()
  SET(${list_var_name} ${new_list} PARENT_SCOPE)
ENDFUNCTION()

# Extract user name and repository name from a github URL.
FUNCTION (EXTRACT_REPO_NAME_AND_USER repo_url repo_name_var repo_user_var)
  IF(repo_url MATCHES "^git@")
    # normalize to https-style URLs
    STRING(REGEX REPLACE "^git@([^:]+):(.*)$" "https://\\1/\\2" repo_url "${repo_url}")
  ENDIF()
  # Extract the repository user
  STRING(REGEX REPLACE "https://([^/]+)/([^/]+)/.*" "\\2" repo_user "${repo_url}")

  STRING(REGEX REPLACE ".*/([^/]*)$" "\\1" repo_name "${repo_url}")
  STRING(REGEX REPLACE "\\.git$" "" repo_name "${repo_name}")

  SET(${repo_name_var} ${repo_name} PARENT_SCOPE)
  SET(${repo_user_var} ${repo_user} PARENT_SCOPE)
ENDFUNCTION()

# Add a known 3rd party dependency for SBOM generation
# Currently used for "vendored" (part of our repository) source code we know about
# such as zlib, as well ExternalProject_Add() projects
MACRO(ADD_THIRD_PARTY_DEPENDENCY name url tag rev version description)
 LIST(FIND ALL_THIRD_PARTY ${name} idx)
 IF (idx GREATER -1)
   MESSAGE(FATAL_ERROR "${name} is already in ALL_THIRD_PARTY")
 ENDIF()
 SET(${name}_URL ${url})
 SET(${name}_TAG ${tag})
 SET(${name}_REVISION ${rev})
 SET(${name}_DESCRIPTION "${description}")
 SET(${name}_VERSION "${version}")
 LIST(APPEND ALL_THIRD_PARTY ${name})
ENDMACRO()

# Match third party component with supplier
# CyclonDX documentation says it is
#  "The organization that supplied the component.
#  The supplier may often be the manufacturer, but may also be a distributor or repackager."
#
# Perhaps it can always be "MariaDB", but security team recommendation is different
# more towards "author"
FUNCTION (sbom_get_supplier repo_name repo_user varname)
  IF("${repo_name_SUPPLIER}")
    SET(${varname} "${repo_name_SUPPLIER}" PARENT_SCOPE)
  ELSEIF (repo_name MATCHES "zlib|minizip")
    # stuff that is checked into out repos
    SET(${varname} "MariaDB" PARENT_SCOPE)
  ELSE()
    IF(repo_user MATCHES "mariadb-corporation|mariadb")
      set(repo_user "MariaDB")
    ENDIF()
    # Capitalize just first letter in repo_user
    STRING(SUBSTRING "${repo_user}" 0 1 first_letter)
    STRING(SUBSTRING "${repo_user}" 1 -1 rest)
    STRING(TOUPPER "${first_letter}" first_letter_upper)
    SET(${varname} "${first_letter_upper}${rest}" PARENT_SCOPE)
  ENDIF()
ENDFUNCTION()

# Generate sbom.json in the top-level build directory
FUNCTION(GENERATE_SBOM)
  IF(EXISTS ${PROJECT_SOURCE_DIR}/cmake/submodule_info.cmake)
    INCLUDE(${PROJECT_SOURCE_DIR}/cmake/submodule_info.cmake)
  ELSE()
    GENERATE_SUBMODULE_INFO(${PROJECT_BINARY_DIR}/cmake/submodule_info.cmake)
    INCLUDE(${PROJECT_BINARY_DIR}/cmake/submodule_info.cmake)
  ENDIF()
  # Remove irrelevant for the current build submodule information
  # That is, if we do not build say columnstore, do  not include
  # dependency info into SBOM
  IF(WITH_SSL AND NOT (WITH_SSL STREQUAL "bundled"))
    # using openssl, rather than wolfssl
    REMOVE_ALL_MATCHES(ALL_SUBMODULES wolfssl)
  ENDIF()
  IF(NOT WITH_WSREP)
    # wsrep is not compiled
    REMOVE_ALL_MATCHES(ALL_SUBMODULES wsrep)
  ENDIF()
  IF((NOT PLUGIN_COLUMNSTORE) OR (PLUGIN_COLUMNSTORE STREQUAL "NO"))
    REMOVE_ALL_MATCHES(ALL_SUBMODULES columnstore)
  ENDIF()
  IF((NOT PLUGIN_ROCKSDB) OR (PLUGIN_ROCKSDB STREQUAL "NO"))
    # Rocksdb is not compiled
    REMOVE_ALL_MATCHES(ALL_SUBMODULES rocksdb)
  ENDIF()
  IF((NOT PLUGIN_S3) OR (PLUGIN_S3 STREQUAL "NO"))
    # S3 aria is not compiled
    REMOVE_ALL_MATCHES(ALL_SUBMODULES storage/maria/libmarias3)
  ENDIF()
  # libmariadb/docs is not a library, so remove it
  REMOVE_ALL_MATCHES(ALL_SUBMODULES libmariadb/docs)

  # It is possible to provide  EXTRA_SBOM_DEPENDENCIES
  # and accompanying per-dependency data, to extend generared sbom
  # document.
  # Example below injects an extra "ncurses" dependency  using several
  # command line parameters for CMake.
  # -DEXTRA_SBOM_DEPENDENCIES=ncurses
  # -Dncurses_URL=https://github.com/mirror/ncurses
  # -Dncurses_TAG=v6.4
  # -Dncurses_VERSION=6.4
  # -Dncurses_DESCRIPTION="A fake extra dependency"
  SET(ALL_THIRD_PARTY ${ALL_SUBMODULES} ${EXTRA_SBOM_DEPENDENCIES})

  IF(TARGET libfmt)
    ExternalProject_GET_PROPERTY(libfmt URL)
    IF(NOT ("${URL}" MATCHES
      "https://github\\.com/fmtlib/fmt/releases/download/[0-9]+\\.[0-9]+\\.[0-9]+/fmt-[0-9]+\\.[0-9]+\\.[0-9]+.zip"))
      MESSAGE(FATAL_ERROR "Unexpected fmtlib URL")
    ENDIF()
    STRING(REGEX MATCH "[0-9]+\\.[0-9]+\\.[0-9]+" libmt_TAG "${URL}")
    ADD_THIRD_PARTY_DEPENDENCY(libfmt
      "https://github.com/fmtlib/fmt"
      "${libmt_TAG}" "${libmt_TAG}" "${libmt_TAG}"
      "header only library, used in server")
  ENDIF()

  IF(TARGET pcre2)
    ExternalProject_GET_PROPERTY(pcre2 URL)
    IF(NOT ("${URL}" MATCHES
       "https://github\\.com/PCRE2Project/pcre2/releases/download/pcre2-[0-9]+\\.[0-9]+/pcre2-[0-9]+\\.[0-9]+\\.zip"))
      MESSAGE(FATAL_ERROR "Unexpected pcre2 URL")
    ENDIF()
    STRING(REGEX MATCH "pcre2-[0-9]+\\.[0-9]+" pcre2_TAG "${URL}")
    STRING(REGEX MATCH "[0-9]+\\.[0-9]+" pcre2_VERSION "${pcre2_TAG}")
    ADD_THIRD_PARTY_DEPENDENCY(pcre2 "https://github.com/PCRE2Project/pcre2"
      "${pcre2_TAG}" "${pcre2_TAG}" "${pcre2_VERSION}" "")
  ENDIF()

  # ZLIB
  IF(TARGET zlib OR TARGET ha_connect OR TARGET connect)
    # Path to the zlib.h file
    SET(ZLIB_HEADER_PATH "${PROJECT_SOURCE_DIR}/zlib/zlib.h")
    # Variable to store the extracted version
    SET(ZLIB_VERSION "")
    # Read the version string from the file
    file(STRINGS "${ZLIB_HEADER_PATH}" ZLIB_VERSION_LINE REGEX "#define ZLIB_VERSION.*")
    # Extract the version number using a regex
    IF (ZLIB_VERSION_LINE)
      STRING(REGEX MATCH "\"([^\"]+)\"" ZLIB_VERSION_MATCH "${ZLIB_VERSION_LINE}")
      IF (ZLIB_VERSION_MATCH)
        STRING(REPLACE "\"" "" ZLIB_VERSION "${ZLIB_VERSION_MATCH}")
        IF(NOT ("${ZLIB_VERSION}" MATCHES "[0-9]+\\.[0-9]+\\.[0-9]+"))
          MESSAGE(FATAL_ERROR "Unexpected zlib version '${ZLIB_VERSION}' parsed from ${ZLIB_HEADER_PATH}")
        ENDIF()
      ELSE()
        MESSAGE(FATAL_ERROR "Could not extract ZLIB version from the line: ${ZLIB_VERSION_LINE}")
      ENDIF()
    ELSE()
      MESSAGE(FATAL_ERROR "ZLIB_VERSION definition not found in ${ZLIB_HEADER_PATH}")
    ENDIF()
    IF(TARGET zlib)
      ADD_THIRD_PARTY_DEPENDENCY(zlib "https://github.com/madler/zlib"
      "v${ZLIB_VERSION}" "v${ZLIB_VERSION}" "${ZLIB_VERSION}" "Vendored zlib included into server source")
    ENDIF()
    IF(TARGET ha_connect OR TARGET connect)
      SET(minizip_PURL "pkg:github/madler/zlib@${ZLIB_VERSION}?path=contrib/minizip")
      ADD_THIRD_PARTY_DEPENDENCY(minizip "https://github.com/madler/zlib?path=contrib/minizip"
      "v${ZLIB_VERSION}-minizip" "v${ZLIB_VERSION}-minizip" "${ZLIB_VERSION}" "Vendored zlib included into server source")
    ENDIF()
  ENDIF()

  SET(sbom_components "")
  SET(sbom_dependencies "\n    {
      \"ref\": \"${CPACK_PACKAGE_NAME}\",
      \"dependsOn\": [" )

  SET(first ON)
  FOREACH(dep ${ALL_THIRD_PARTY})
    # Extract the part after the last "/" from URL
    SET(revision ${${dep}_REVISION})
    SET(tag ${${dep}_TAG})
    SET(desc ${${dep}_DESCRIPTION})
    IF((tag STREQUAL "no-tag") OR (NOT tag))
     SET(tag ${revision})
    ENDIF()
    IF (NOT "${revision}" AND "${tag}")
      SET(revision ${tag})
    ENDIF()
    SET(version ${${dep}_VERSION})

    IF (version)
    ELSEIF(tag)
      SET(version ${tag})
    ELSEIF(revision)
      SET(version ${revision})
    ENDIF()

    EXTRACT_REPO_NAME_AND_USER("${${dep}_URL}"  repo_name repo_user)

    IF(first)
      SET(first OFF)
    ELSE()
      STRING(APPEND sbom_components ",")
      STRING(APPEND sbom_dependencies ",")
    ENDIF()
    SET(bom_ref "${repo_name}-${version}")
    IF(desc)
      SET(desc_line "\n      \"description\": \"${desc}\",")
    ELSE()
      SET(desc_line "")
    ENDIF()
    STRING(TOLOWER "${repo_user}" repo_user_lower)
    STRING(TOLOWER "${repo_name}" repo_name_lower)
    IF (${repo_name_lower}_PURL)
      SET(purl "${${repo_name_lower}_PURL}")
    ELSE()
      SET(purl "pkg:github/${repo_user_lower}/${repo_name_lower}@${revision}")
    ENDIF()
    SBOM_GET_SUPPLIER(${repo_name_lower} ${repo_user_lower} supplier)
    STRING(APPEND sbom_components "
    {
      \"bom-ref\": \"${bom_ref}\",
      \"type\": \"library\",
      \"name\": \"${repo_name}\",
      \"version\": \"${version}\",${desc_line}
      \"purl\": \"${purl}\",
      \"supplier\": {
          \"name\": \"${supplier}\"
       }
    }")
    STRING(APPEND sbom_dependencies "
        \"${bom_ref}\"")
  ENDFOREACH()
  STRING(APPEND sbom_dependencies "\n      ]\n    }\n")
  STRING(UUID UUID NAMESPACE ee390ca3-e70f-4b35-808e-a512489156f5 NAME SBOM TYPE SHA1)
  STRING(TIMESTAMP TIMESTAMP "%Y-%m-%dT%H:%M:%SZ" UTC)
  EXTRACT_REPO_NAME_AND_USER("${GIT_REMOTE_ORIGIN_URL}" GITHUB_REPO_NAME GITHUB_REPO_USER)
  #github-purl needs lowercased user and project names
  STRING(TOLOWER "${GITHUB_REPO_NAME}" GITHUB_REPO_NAME)
  STRING(TOLOWER "${GITHUB_REPO_USER}" GITHUB_REPO_USER)
  configure_file(${CMAKE_CURRENT_LIST_DIR}/cmake/sbom.json.in ${CMAKE_BINARY_DIR}/sbom.json)
ENDFUNCTION()
