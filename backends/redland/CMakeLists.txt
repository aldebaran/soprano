project(soprano_redland)

set( CMAKE_VERBOSE_MAKEFILE ON )

include_directories(HEADERS
  ${soprano_SOURCE_DIR}
  ${soprano_core_SOURCE_DIR}
  ${RAPTOR2_INCLUDE_DIR}
  )

add_definitions(${REDLAND_CFLAGS})

# static libs do not get compiled with -fPIC which is needed on amd64
# when we link to a shared lib
# FIXME: do an amd64 check
if(NOT WIN32)
  add_definitions(-fPIC)
endif()

#if(BUILD_REDLAND_BACKEND OR BUILD_RAPTOR_SERIALIZER)
set(redland_core_SRC
  redlandworld.cpp
  redlandstatementiterator.cpp
  redlandqueryresult.cpp
  redlandmodel.cpp
  redlandnodeiteratorbackend.cpp
  multimutex.cpp
  )

qi_create_lib(soprano_redlandcore STATIC ${redland_core_SRC})

#qi_use_lib(soprano_redlandcore RAPTOR2 soprano ${REDLAND_LIBRARIES})
#qi_use_lib(soprano_redlandcore soprano ${REDLAND_LIBRARIES})
qi_use_lib(soprano_redlandcore soprano REDLAND)

qi_stage_lib(soprano_redlandcore)

set(redland_backend_SRC
  redlandbackend.cpp)

#CROSS-COMPILATION
qi_create_lib(soprano_redlandbackend
  SRC     ${HEADERS}
  ${redland_backend_SRC}
  DEPENDS QI QT5_CORE RAPTOR2 REDLAND soprano_redlandcore
  SHARED
  )

configure_file(redlandbackend.desktop.cmake ${QI_SDK_DIR}/${QI_SDK_SHARE}/dialog/redlandbackend.desktop)

qi_install_data(
  ${QI_SDK_DIR}/${QI_SDK_SHARE}/dialog/redlandbackend.desktop
  SUBFOLDER "dialog"
  )

qi_stage_lib(soprano_redlandbackend)

#endif()

