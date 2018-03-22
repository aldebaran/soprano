project(nquads_parser)

include_directories(HEADERS
  ${soprano_SOURCE_DIR}
  ${soprano_core_SOURCE_DIR}
)

set(nquadparser_SRC
  nquadparser.cpp)

qi_create_lib(nquads_parser
  SRC ${HEADERS}
  ${nquadparser_SRC}
  DEPENDS QT5_CORE
  SHARED
  )

qi_stage_lib(nquads_parser)

configure_file(nquadparser.desktop.cmake ${CMAKE_CURRENT_BINARY_DIR}/nquadparser.desktop)

install(FILES
  ${CMAKE_CURRENT_BINARY_DIR}/nquadparser.desktop
  DESTINATION ${DATA_INSTALL_DIR}/soprano/plugins
  )
