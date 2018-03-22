project(nquads_serializer)

include_directories(HEADERS
  ${soprano_SOURCE_DIR}
  ${soprano_core_SOURCE_DIR}
)

set(nquadserializer_SRC
  nquadserializer.cpp)

#add_library(soprano_nquadserializer MODULE ${nquadserializer_SRC})

#target_link_libraries(soprano_nquadserializer soprano)

#install(TARGETS soprano_nquadserializer ${PLUGIN_INSTALL_DIR})

qi_create_lib(nquads_serializer
  SRC ${HEADERS}
  ${nquadserializer_SRC}
  DEPENDS QT5_CORE
  SHARED
  )

  qi_stage_lib(nquads_serializer)

configure_file(nquadserializer.desktop.cmake ${CMAKE_CURRENT_BINARY_DIR}/nquadserializer.desktop)

install(FILES
  ${CMAKE_CURRENT_BINARY_DIR}/nquadserializer.desktop
  DESTINATION ${DATA_INSTALL_DIR}/soprano/plugins
  )
