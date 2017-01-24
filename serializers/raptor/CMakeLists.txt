project(soprano_raptor_serializer)

include_directories(
  ${soprano_SOURCE_DIR}
  ${soprano_core_SOURCE_DIR}
  ${RAPTOR2_INCLUDE_DIR}
)

set(CMAKE_REQUIRED_INCLUDES ${RAPTOR2_INCLUDE_DIR})
set(CMAKE_REQUIRED_LIBRARIES ${RAPTOR2_LIBRARIES})

set(raptor_serializer_SRC
  raptorserializer.cpp
)

qi_create_lib(soprano_raptor_serializer
  SRC ${HEADERS}
  ${raptor_serializer_SRC}
  DEPENDS QT5_CORE RAPTOR2
  SHARED
  )

qi_stage_lib(soprano_raptor_serializer)

configure_file(raptorserializer.desktop.cmake ${CMAKE_CURRENT_BINARY_DIR}/raptorserializer.desktop)

install(FILES
  ${CMAKE_CURRENT_BINARY_DIR}/raptorserializer.desktop
  DESTINATION ${DATA_INSTALL_DIR}/soprano/plugins
  )
