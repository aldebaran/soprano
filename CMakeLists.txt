cmake_minimum_required(VERSION 2.8.9 FATAL_ERROR)
project(soprano)
find_package(qibuild)
#qi_sanitize_compile_flags()
#find_package(aldebaran-settings)

include(qibuild/modules/qt5-tools)
include_directories(".")

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

option(QT5_BUILD "Build Soprano using the Qt5 framework" TRUE)

qi_add_optional_package(REDLAND)
qi_add_optional_package(RAPTOR)
qi_add_optional_package(RASQAL)


if(NOT (WITH_REDLAND AND
    WITH_RAPTOR AND
    WITH_RASQAL) )
return()
endif()


add_subdirectory(soprano)
add_subdirectory(backends)
add_subdirectory(queryparsers)
add_subdirectory(parsers)
add_subdirectory(serializers)
