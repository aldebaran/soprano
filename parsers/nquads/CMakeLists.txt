project(nquads_parser)

include_directories(
  ${soprano_SOURCE_DIR}
  ${soprano_core_SOURCE_DIR}
  ${RAPTOR2_INCLUDE_DIRS}
)

set(nquadparser_SRC
  nquadparser.cpp)

add_library(soprano_nquadparser MODULE ${nquadparser_SRC})

target_link_libraries(soprano_nquadparser soprano ${RAPTOR2_LIBRARIES})

install(TARGETS soprano_nquadparser ${PLUGIN_INSTALL_DIR})

configure_file(nquadparser.desktop.cmake ${CMAKE_CURRENT_BINARY_DIR}/nquadparser.desktop)

install(FILES
  ${CMAKE_CURRENT_BINARY_DIR}/nquadparser.desktop
  DESTINATION ${DATA_INSTALL_DIR}/soprano/plugins
  )
