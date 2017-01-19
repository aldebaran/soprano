project(soprano_raptor_parser)

include_directories(HEADERS
  ${soprano_SOURCE_DIR}
  ${soprano_core_SOURCE_DIR}
)

set(raptor_parser_SRC
  raptorparser.cpp
)

qi_create_lib(soprano_raptor_parser
  SRC ${HEADERS}
  ${raptor_parser_SRC}
    DEPENDS QT5_CORE RAPTOR2
  SHARED
  )

qi_stage_lib(soprano_raptor_parser)

configure_file(raptorparser.desktop.cmake ${CMAKE_CURRENT_BINARY_DIR}/raptorparser.desktop)

install(FILES
  ${CMAKE_CURRENT_BINARY_DIR}/raptorparser.desktop
  DESTINATION ${DATA_INSTALL_DIR}/soprano/plugins
  )
