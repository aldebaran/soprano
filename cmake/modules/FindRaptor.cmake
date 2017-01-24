# - Try to find the Raptor RDF parsing library (http://librdf.org/raptor/)
# Once done this will define
#
#  RAPTOR2_FOUND       - system has Raptor
#  RAPTOR2_LIBRARIES   - Link these to use Raptor
#  RAPTOR2_INCLUDE_DIR - Include directory for using Raptor
#  RAPTOR2_DEFINITIONS - Compiler switches required for using Raptor
#
#  Capabilities
#       RAPTOR2_HAVE_TRIG   - Set if raptor has TRIG

# (c) 2007-2011 Sebastian Trueg <trueg@kde.org>
# (c) 2011 Artem Serebriyskiy <v.for.vandal@gmail.com>
# (c) 2011 Michael Jansen <kde@michael-jansen.biz>
#
# Based on FindFontconfig Copyright (c) 2006,2007 Laurent Montel, <montel@kde.org>
#
# Redistribution and use is allowed according to the terms of the BSD license.
# For details see the accompanying COPYING-CMAKE-SCRIPTS file.


MACRO ( FIND_RAPTOR2 libname libhints includehints )
    find_library_with_debug(
        RAPTOR2_LIBRARIES
        WIN32_DEBUG_POSTFIX d
        NAMES ${libname}
        HINTS ${libhints})
    find_path(
        RAPTOR2_INCLUDE_DIR raptor.h
        HINTS ${includehints}
        PATH_SUFFIXES ${libname})
ENDMACRO ()

# Check if we have cached results in case the last round was successful.
if ( NOT ( RAPTOR2_INCLUDE_DIR AND RAPTOR2_LIBRARIES ) OR NOT RAPTOR2_FOUND )

    include(FindLibraryWithDebug)
    find_package(PkgConfig)

    # By default look for version 2.0
    if (NOT RAPTOR2_FIND_VERSION )
        set( RAPTOR2_FIND_VERSION "2.0")
        set( RAPTOR2_FIND_VERSION_MAJOR "2" )
        set( RAPTOR2_FIND_VERSION_MINOR "0" )
    endif()

    if ( RAPTOR2_FIND_VERSION_MAJOR EQUAL "2" )

        if ( NOT WIN32 )
            pkg_check_modules(PC_RAPTOR2 QUIET raptor2)
            if ( PC_RAPTOR2_FOUND )
                set(RAPTOR2_DEFINITIONS ${PC_RAPTOR2_CFLAGS_OTHER})
                set(RAPTOR2_VERSION ${PC_RAPTOR2_VERSION} CACHE STRING "Raptor Version found" )
            endif()
        endif()
        find_raptor2( raptor2 "${PC_RAPTOR2_LIBDIR};${PC_RAPTOR2_LIBRARY_DIRS}" "${PC_RAPTOR2_INCLUDEDIR};${PC_RAPTOR2_INCLUDE_DIRS}")

    elseif ( RAPTOR2_FIND_VERSION_MAJOR EQUAL "1" )

        if ( NOT WIN32 )
            pkg_check_modules(PC_RAPTOR2 QUIET raptor2)
            if ( PC_RAPTOR2_FOUND )
                set(RAPTOR2_DEFINITIONS ${PC_RAPTOR2_CFLAGS_OTHER})
                set(RAPTOR2_VERSION ${PC_RAPTOR2_VERSION} CACHE STRING "Raptor Version found" )
            endif()
        endif()
        find_raptor2( raptor2 "${PC_RAPTOR2_LIBDIR};${PC_RAPTOR2_LIBRARY_DIRS}" "${PC_RAPTOR2_INCLUDEDIR};${PC_RAPTOR2_INCLUDE_DIRS}")

    else()

        message( FATAL_ERROR "No idea how to check for version : ${RAPTOR2_FIND_VERSION}")

    endif()

    if (RAPTOR2_VERSION)
        if(NOT ${RAPTOR2_VERSION} VERSION_LESS 1.4.16)
            set(RAPTOR2_HAVE_TRIG TRUE)
        endif()
    endif()

    mark_as_advanced(RAPTOR2_INCLUDE_DIR RAPTOR2_LIBRARIES)

endif() # Check for cached values

include(FindPackageHandleStandardArgs)

find_package_handle_standard_args(
    Raptor2
    VERSION_VAR   RAPTOR2_VERSION
    REQUIRED_VARS RAPTOR2_LIBRARIES RAPTOR2_INCLUDE_DIR)

mark_as_advanced(RAPTOR2_VERSION)

if (NOT RAPTOR2_FOUND AND RAPTOR2_FIND_VERSION_MAJOR EQUAL "2" AND NOT RAPTOR2_FIND_QUIET )
    pkg_check_modules(PC_RAPTOR2 QUIET raptor2)
    if (PC_RAPTOR2_FOUND)
        message( STATUS "You have raptor1 version ${PC_RAPTOR2_VERSION} installed. Please update." )
    endif()
endif()

