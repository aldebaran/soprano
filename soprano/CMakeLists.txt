project(soprano_core)
find_package(qibuild)
include(qibuild/modules/qt5-tools)

# overriding QT_USE_FILE since that includes QT_INCLUDE_DIR before soprano headers
#set(CMAKE_INCLUDE_DIRECTORIES_BEFORE ON)
include_directories(BEFORE
  #  ${soprano_SOURCE_DIR}
  ${CMAKE_CURRENT_SOURCE_DIR}
  ${CMAKE_CURRENT_SOURCE_DIR}/util
  ${CMAKE_CURRENT_SOURCE_DIR}/query
  ${CMAKE_CURRENT_SOURCE_DIR}/vocabulary
  ${CMAKE_CURRENT_BINARY_DIR}
  )


configure_file(soprano-config.h.cmake ${CMAKE_CURRENT_BINARY_DIR}/soprano-config.h)
#configure_file(version.h.cmake ${CMAKE_CURRENT_BINARY_DIR}/version.h)
#configure_file(version.h.cmake ${CMAKE_CURRENT_SOURCE_DIR}/version.h)

add_definitions(-DUSING_SOPRANO_NRLMODEL_UNSTABLE_API)

set(soprano_HDRS
  backend.h
  bindingset.h
  datastream.h
  error.h
  filtermodel.h
  global.h
  graph.h
  inference/inferencemodel.h
  inference/inferencerule.h
  inference/inferenceruleparser.h
  inference/inferenceruleset.h
  inference/nodepattern.h
  inference/sil.h
  inference/statementpattern.h
  iterator.h
  iteratorbackend.h
  languagetag.h
  literalvalue.h
  locator.h
  model.h
  node.h
  nodeiterator.h
  nrlmodel.h
  parser.h
  plugin.h
  pluginmanager.h
  queryresultiterator.h
  queryresultiteratorbackend.h
  rdfschemamodel.h
  serializer.h
  soprano.h
  soprano_export.h
  sopranomacros.h
  sopranotypes.h
  statement.h
  statementiterator.h
  storagemodel.h
  util/asyncmodel.h
  util/asyncquery.h
  util/asyncresult.h
  util/dummymodel.h
  util/mutexmodel.h
  util/readonlymodel.h
  util/signalcachemodel.h
  util/simplenodeiterator.h
  util/simplestatementiterator.h
  vocabulary.h
  vocabulary/nao.h
  vocabulary/nrl.h
  vocabulary/owl.h
  vocabulary/rdf.h
  vocabulary/rdfs.h
  vocabulary/xesam.h
  vocabulary/xsd.h
)

set(soprano_SRCS
  ${soprano_HDRS}
  queryresultiterator.cpp
  queryresultiterator.h
  queryresultiteratorbackend.cpp
  queryresultiteratorbackend.h
  node.cpp
  node.h
  statement.cpp
  statement.h
  statementiterator.cpp
  statementiterator.h
  nodeiterator.cpp
  model.cpp
  model.h
  parser.cpp
  parser.h
  serializer.cpp
  serializer.h
  pluginmanager.cpp
  pluginstub.cpp
  plugin.cpp
  qhashqurlcompat.cpp
  backend.cpp
  backend.h
  global.cpp
  error.cpp
  error.h
  literalvalue.cpp
  literalvalue.h
  languagetag.cpp
  languagetag.h
  locator.cpp
  locator.h
  datetime.cpp
  #  version.cpp
  filtermodel.h
  filtermodel.cpp
  storagemodel.h
  storagemodel.cpp
  rdfschemamodel.cpp
  bindingset.cpp
  sopranotypes.cpp
  graph.cpp
  datastream.cpp
  vocabulary/rdf.cpp
  vocabulary/rdfs.cpp
  vocabulary/xsd.cpp
  vocabulary/nrl.cpp
  vocabulary/nao.cpp
  vocabulary/xesam.cpp
  vocabulary/owl.cpp
  query/query.cpp
  query/queryparser.cpp
  query/queryserializer.cpp
  inference/nodepattern.cpp
  inference/statementpattern.cpp
  inference/inferencerule.cpp
  inference/inferenceruleset.cpp
  inference/sil.cpp
  inference/inferencemodel.h
  inference/inferencemodel.cpp
  inference/inferenceruleparser.cpp
  nrlmodel.h
  nrlmodel.cpp
  inifile.cpp
  desktopfile.cpp
  sopranopluginfile.cpp
  sopranodirs.cpp
  n3nodeparser.cpp
  util/extreadwritelock.cpp
  util/mutexmodel.cpp
  util/mutexstatementiteratorbackend.cpp
  util/mutexnodeiteratorbackend.cpp
  util/mutexqueryresultiteratorbackend.cpp
  util/simplestatementiterator.cpp
  util/simplenodeiterator.cpp
  util/dummymodel.cpp
  util/signalcachemodel.cpp
  util/readonlymodel.cpp
  util/asyncmodel.cpp
  util/asyncresult.cpp
  util/asynccommand.cpp
  util/asynciteratorbackend.cpp
  util/asyncquery.cpp
  )

#CROSS-COMPILATION
qi_create_lib(soprano
  SRC     ${FILES}
  ${soprano_SRCS}
  DEPENDS QI QT5_CORE QT5_NETWORK QT5_DBUS QT5_XML REDLAND RASQAL
  SHARED
  )

qi_stage_lib(soprano)

qi_install_header(
  ${soprano_HDRS}
  SUBFOLDER soprano
  KEEP_RELATIVE_PATHS
)
