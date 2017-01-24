project(soprano_rasqalqueryparser)

include_directories(
  ${soprano_SOURCE_DIR}
  ${REDLAND_INCLUDE_DIR}
  ${RASQAL_INCLUDE_DIR}
  ${CMAKE_INSTALL_PREFIX}/include
  ${soprano_SOURCE_DIR}
  ${soprano_core_SOURCE_DIR}
  ${soprano_core_SOURCE_DIR}/query
)

set(rasqalqueryparser_SRC
  rasqalqueryparser.cpp
  rasqalqueryparser.h
)

qi_create_lib(soprano_rasqalqueryparser
  SRC ${rasqalqueryparser_SRC}
    DEPENDS QI QT5_CORE RASQAL
  #  DEPENDS QI QT5_CORE
  SHARED
  )

configure_file(rasqalqueryparser.desktop.cmake ${QI_SDK_DIR}/${QI_SDK_SHARE}/rasqalqueryparser.desktop)

qi_install_data(
  ${QI_SDK_DIR}/${QI_SDK_SHARE}/dialog/rasqalqueryparser.desktop
  SUBFOLDER "dialog"
  )

