/*
 * This file is part of Soprano Project.
 *
 * Copyright (C) 2007 Sebastian Trueg <trueg@kde.org>
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Library General Public License for more details.
 *
 * You should have received a copy of the GNU Library General Public License
 * along with this library; see the file COPYING.LIB.  If not, write to
 * the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
 * Boston, MA 02110-1301, USA.
 */

#include "inferencemodel.h"
#include "rdf.h"
#include "sil.h"
#include "statement.h"
#include "inferencerule.h"
#include "statementpattern.h"
#include "nodepattern.h"
#include "queryresultiterator.h"
#include "literalvalue.h"
#include "bindingset.h"
#include "nodeiterator.h"
#include <iostream>

#include <QtCore/QString>
#include <QtCore/QUuid>
#include <QtCore/QDebug>
#include <QTime>

#include <qi/log.hpp>

qiLogCategory("inferencemodel");

QString learningDomain = "com.aldebaran.learning";

// FIXME: add error handling!

static Soprano::Node compressStatement( const Soprano::Statement& statement )
{
    // There should be some method Statement::toXXXString for this
    QString s = QString( "<%1> <%2> " ).arg( statement.subject().toString() ).arg( statement.predicate().toString() );
    if ( statement.object().isLiteral() ) {
        s.append( QString( "\"%1\"^^<%2>" ).arg( statement.object().toString() ).arg( statement.object().dataType().toString() ) );
    }
    else {
        s.append( '<' + statement.object().toString() + '>' );
    }
    return Soprano::LiteralValue( s );
}


static Soprano::Statement uncompressStatement( const Soprano::Node& compressedStatement )
{
  Soprano::Statement uncompressedStatement;
  QList<QString> stringNodes = compressedStatement.toString().remove(">").split("<");

  if(stringNodes.size() == 3)
  {
    uncompressedStatement.setSubject(Soprano::Node(stringNodes[0]));
    uncompressedStatement.setPredicate(Soprano::Node(stringNodes[1]));
    uncompressedStatement.setObject(Soprano::Node(stringNodes[2]));
  }
  return uncompressedStatement;
}

static QString createUuid()
{
    // FIXME: check if the uri already exists
     QString uid = QUuid::createUuid().toString();
    uid = uid.mid( 1, uid.length()-2 );

    return uid;
}

static QString createUuidFromStatement(const Soprano::Statement& statement)
{
  QUuid namespaceUuid = QUuid("00000000-0000-0000-0000-000000000000");
  QString string = statement.subject().toString() + statement.predicate().toString() + statement.object().toString();
  QString uid = QUuid::createUuidV3(namespaceUuid, QString(string)).toString();
  uid = uid.mid( 1, uid.length()-2 );

  return uid;
}


static QUrl createRandomUri()
{
    return QUrl( "inference://localhost#" + createUuid());
}

// this is stuff we only need for the temp implementation that is used due to the lack of proper SPARQL support in redland
// -----------------------------------------------------------------------------------------------------------------------
#include <QSet>
#include "statementiterator.h"
// -----------------------------------------------------------------------------------------------------------------------



class Soprano::Inference::InferenceModel::Private
{
public:
    QMap<QString, Rule> ruleMap;
    bool compressedStatements;
    bool optimizedQueries;
    QMap <QString, QString> bindingMapHistory;
};


Soprano::Inference::InferenceModel::InferenceModel( Model* parent )
    : FilterModel( parent ),
      d( new Private() )
{
    d->compressedStatements = true;
    d->optimizedQueries = false;
}

Soprano::Inference::InferenceModel::~InferenceModel()
{
  // Synchronise model with storage before destroying model
  parentModel()->synchroniseDatabase();
    delete d;
}


void Soprano::Inference::InferenceModel::setCompressedSourceStatements( bool b )
{
    d->compressedStatements = b;
}


void Soprano::Inference::InferenceModel::setOptimizedQueriesEnabled( bool b )
{
    d->optimizedQueries = b;
}


QString Soprano::Inference::InferenceModel::addRule( const Rule& rule )
{
  QString ruleId = rule.getId();
  if(rule.effectStyle() == "negation")
  {
    parentModel()->enableNegation(true);
  }
  d->ruleMap.insert(ruleId, rule);

  return ruleId;
}


void Soprano::Inference::InferenceModel::setRules( const QList<Rule>& rules )
{
  d->ruleMap.clear();
  Q_FOREACH(Rule rule, rules)
  {
    d->ruleMap.insert(rule.getId(), rule);
  }
}

void Soprano::Inference::InferenceModel::removeRule(const QString& ruleId)
{
  d->ruleMap.remove(ruleId);
}



QList<Soprano::Inference::Rule> Soprano::Inference::InferenceModel::getRules()
{
  return d->ruleMap.values();
}


Soprano::Error::ErrorCode Soprano::Inference::InferenceModel::addStatement( const Statement& statement )
{
    Error::ErrorCode error = FilterModel::addStatement( statement );
    if ( error == Error::ErrorNone || error==Error::ErrorNegation) {
        // FIXME: error handling for the inference itself
        if( inferStatement( statement, true ) ) {
            emit statementsAdded();
        }
    }
    return error;
}


Soprano::Error::ErrorCode Soprano::Inference::InferenceModel::removeAllStatements( const Statement& statement )
{
//  parentModel()->removeAllStatements(statement);
    // FIXME: should we check if the statement could match some rule at all and if not do nothing?

    // are there any rules that handle objects? Probably not.
//      QTextStream s( stdout );
      /////////////////////////
      /// IT'S NOT POSSIBLE TO REMOVE LITERAL NODE ???
      /////////////////////////
//    if ( !statement.object().isLiteral() ) {
        // we need to list statements first and then iterate over all that will be removed
        // since we change the model we also have to cache the statements

        QList<Statement> removedStatements = parentModel()->listStatements( statement ).allStatements();

        for ( QList<Statement>::const_iterator it2 = removedStatements.constBegin();
              it2 != removedStatements.constEnd(); ++it2 ) {

            Error::ErrorCode c = removeStatement( *it2 );

            if ( c != Error::ErrorNone ) {
                return c;
            }
        }
//    }

    return Error::ErrorNone;
}


Soprano::Error::ErrorCode Soprano::Inference::InferenceModel::removeStatement( const Statement& statement )
{
    Error::ErrorCode c = FilterModel::removeStatement( statement );
    if ( c != Error::ErrorNone ) {
        return c;
    }



    if(!getMetadataNode(statement).isEmpty())
    {

      Soprano::StatementIterator disabledStatements = parentModel()->listStatements(getMetadataNode(statement),
                                                                                    Vocabulary::RDF::isDisabled(),
                                                                                    Soprano::Node::createEmptyNode(),
                                                                                    Soprano::Node::createEmptyNode());


      QList<Soprano::Node> disablingMetadataNodes;
      QList<Soprano::Node> disabledMetadataNodes;

      while (disabledStatements.next())
      {
        Soprano::StatementIterator disablingStatements =  parentModel()->listStatements(Soprano::Node::createEmptyNode(),
                                                                                        Vocabulary::RDF::isDisabled(),
                                                                                        disabledStatements.current().object(),
                                                                                        Soprano::Node::createEmptyNode());

        QList<Statement> allDisablingStatements = disablingStatements.allStatements();

        if(allDisablingStatements.size() == 1)
        {
          disablingMetadataNodes.append(allDisablingStatements.first().subject());
        }
      }

      Q_FOREACH(Soprano::Node disablingMetadataNode, disablingMetadataNodes)
      {
        cleanMetadata(disablingMetadataNode);

//WARNING Only working when FilterModel is used, not working with parentModel->removeStatement
        FilterModel::removeStatements(parentModel()->listStatements(disablingMetadataNode,
                                                                    Vocabulary::RDF::isDisabled(),
                                                                    Soprano::Node::createEmptyNode(),
                                                                    Soprano::Node::createEmptyNode()).allStatements());


      }
    }

    QList<Node> graphs = inferedGraphsForStatement( statement );
    for ( QList<Node>::const_iterator it = graphs.constBegin(); it != graphs.constEnd(); ++it ) {
        Node graph = *it;

//        Soprano::StatementIterator statementsToAdd = parentModel()->listStatements(graph,
//                                                                                   Vocabulary::RDF::Statement(),
//                                                                                   Soprano::Node::createEmptyNode(),
//                                                                                   Vocabulary::SIL::InferenceMetaData());
//        while (statementsToAdd.next())
//        {

//      QTextStream s( stdout );
//      s << uncompressStatement(statementsToAdd.current().object()).subject().toString() << endl;
//      s << uncompressStatement(statementsToAdd.current().object()).predicate().toString() << endl;
//      s << uncompressStatement(statementsToAdd.current().object()).object().toString() << endl;
//          Soprano::Statement statementToAdd= uncompressStatement(statementsToAdd.current().object());
//          parentModel()->addStatement(statementToAdd);
//        }

        // Step 1: remove the source statements of the removed graph
        if ( !d->compressedStatements ) {
            QList<Node> graphSources = parentModel()->listStatements( Statement( graph,
                                                                                 Vocabulary::SIL::sourceStatement(),
                                                                                 Node(),
                                                                                 Vocabulary::SIL::InferenceMetaData() ) ).iterateObjects().allNodes();
            for( QList<Node>::const_iterator it = graphSources.constBegin();
                 it != graphSources.constEnd(); ++it ) {
                c = FilterModel::removeAllStatements( Statement( *it, Node(), Node(), Vocabulary::SIL::InferenceMetaData() ) );
                if ( c != Error::ErrorNone ) {
                    return c;
                }
            }
        }


        // Step 2: remove the graph metadata
        c = FilterModel::removeAllStatements( Statement( graph, Node(), Node(), Vocabulary::SIL::InferenceMetaData() ) );
        if ( c != Error::ErrorNone ) {
            return c;
        }

        // Step 3 remove the infered metadata (and trigger recursive removal) - can be slow
        c = removeContext( graph );
        if ( c != Error::ErrorNone ) {
            return c;
        }
    }

    return Error::ErrorNone;
}


QList<Soprano::Node> Soprano::Inference::InferenceModel::inferedGraphsForStatement( const Statement& statement ) const
{
    if ( d->compressedStatements ) {
        // get the graphs our statement was the source for
        StatementIterator it = parentModel()->listStatements( Statement( Node(),
                                                                         Vocabulary::SIL::sourceStatement(),
                                                                         compressStatement( statement ),
                                                                         Vocabulary::SIL::InferenceMetaData() ) );
        return it.iterateSubjects().allNodes();
    }
    else {
        QList<Soprano::Node> graphs;

        // sadly redland does not seem to support even the most simple queries :(
#if 0
        // check if our statement is source statement for any infered graph
        QString query = QString( "PREFIX rdf: <%1> "
                                 "SELECT ?s WHERE { "
                                 "?s rdf:type rdf:Statement . "
                                 "?s rdf:subject <%2> . "
                                 "?s rdf:predicate <%3> . "
                                 "?s rdf:object <%4> ." )
                        .arg( Vocabulary::RDF::NAMESPACE().toString() )
                        .arg( statement.subject().toString() )
                        .arg( statement.predicate().toString() )
                        .arg( statement.object().toString() );

        if ( statement.context().isValid() ) {
            query += QString( "?s <%1> <%2> ." )
                     .arg( Vocabulary::SIL::CONTEXT().toString() )
                     .arg( statement.context().toString() );
        }

        query += " }";

        QueryResultIterator it = parentModel()->executeQuery( query, Query::QueryLanguageSparql );
        while ( it.next() ) {
            // Step 2: Check for which graph it is source statement
            query = QString( "SELECT ?g WHERE { "
                             "GRAPH <%1> { "
                             "?g <%2> <%3> . "
                             "?g <%4> <%5> . } }" )
                    .arg( Vocabulary::SIL::InferenceMetaData().toString() )
                    .arg( Vocabulary::SIL::sourceStatements().toString() )
                    .arg( it.binding( 0 ).toString() )
                    .arg( Vocabulary::RDF::type().toString() )
                    .arg( Vocabulary::SIL::InferenceModel().toString() );

            QueryResultIterator it2 = parentModel()->executeQuery( query, Query::QueryLanguageSparql );
            while ( it2.next() ) {
                // Step 3: remove the whole infered graph and its metadata
                graphs += it2.binding( 0 );
            }
        }
#endif

        // since redland cannot handle our query we have to do it the ugly way
        QSet<Node> sourceStatements;
        StatementIterator it = parentModel()->listStatements( Statement( Node(), Vocabulary::RDF::subject(), statement.subject() ) );
        sourceStatements = it.iterateSubjects().allNodes().toSet();
        it = parentModel()->listStatements( Statement( Node(), Vocabulary::RDF::predicate(), statement.predicate() ) );
        sourceStatements &= it.iterateSubjects().allNodes().toSet();
        it = parentModel()->listStatements( Statement( Node(), Vocabulary::RDF::object(), statement.object() ) );
        sourceStatements &= it.iterateSubjects().allNodes().toSet();

        // now sourceStatements should contain what our nice first query above returns
        // and we use a siplyfied version of the query above to redland won't get confused :(
        Q_FOREACH( const Node &node, sourceStatements ) {
            // Step 2: Check for which graph it is source statement
            QString query = QString( "SELECT ?g WHERE { "
                                     "?g <%1> <%2> . }" )
                            .arg( Vocabulary::SIL::sourceStatement().toString() )
                            .arg( node.toString() );

            QueryResultIterator it2 = parentModel()->executeQuery( query, Query::QueryLanguageSparql );
            while ( it2.next() ) {
                // Step 3: remove the whole infered graph and its metadata
                graphs += it2.binding( 0 );
            }
        }

        return graphs;
    }
}


void Soprano::Inference::InferenceModel::performInference()
{
  QList<Rule> rules = d->ruleMap.values();
  for ( QList<Rule>::iterator it = rules.begin();
        it != rules.end(); ++it ) {
    d->bindingMapHistory.clear();
    // reset the binding statement, we want to infer it all
    Rule& rule = *it;
    rule.bindToStatement( Statement() );
    inferRule( rule, true );
  }
}


void Soprano::Inference::InferenceModel::clearInference()
{
    // remove all infered statements
    QString query( QString( "select ?g where { ?g <%1> <%2> . }" )
                       .arg( Vocabulary::RDF::type().toString() )
                       .arg( Vocabulary::SIL::InferenceGraph().toString() ) );

    QList<BindingSet> bindings = parentModel()->executeQuery( query, Query::QueryLanguageSparql ).allBindings();
    for ( QList<BindingSet>::const_iterator it = bindings.constBegin(); it != bindings.constEnd(); ++it ) {
        parentModel()->removeContext( it->value( 0 ) );
    }

    // remove disabling metadata
    FilterModel::removeStatements(parentModel()->listStatements(Soprano::Node::createEmptyNode(),
                                                                Vocabulary::RDF::isDisabled(),
                                                                Soprano::Node::createEmptyNode(),
                                                                Soprano::Node::createEmptyNode()).allStatements());

}


int Soprano::Inference::InferenceModel::inferStatement( const Statement& statement, bool recurse )
{
    int cnt = 0;
    QList<Rule> rules = d->ruleMap.values();
    for ( QList<Rule>::iterator it = rules.begin();
          it != rules.end(); ++it ) {
      d->bindingMapHistory.clear();

        Rule& rule = *it;
        if( rule.match( statement) ) {
            rule.bindToStatement( statement );
            qDebug() << "Subject " << statement.subject().toString();
            qDebug() << "Predicate " << statement.predicate().toString();
            qDebug() << "Object " << statement.object().toString();
            cnt += inferRule( rule, recurse );
        }
    }
    return cnt;
}


int recursiveCounter = 0;

int Soprano::Inference::InferenceModel::inferRule( const Rule& rule, bool recurse )
{
  bool inferedStatementFound = false;
  recursiveCounter ++;
  rule.setBindingAlreadyUsed(false);
  rule.clearBindingHistory();
  qDebug() << "COUNTER " << recursiveCounter;
      QTextStream s( stdout );
  QString q = rule.createSparqlQuery( d->optimizedQueries );
  if ( q.isEmpty() ) {
    return 0;
  }
  else {
//             qDebug() << "Applying rule:" << rule;
             qDebug() << "Rule query:" << q;

    int inferedStatementsCount = 0;

    // remember the infered statements to recurse later on
    QList<Statement> inferedStatements;

    // cache the bindings since we work recursively and Soprano would block in the addStatement calls otherwise
    QList<BindingSet> bindings = parentModel()->executeQuery( q, Query::QueryLanguageSparql ).allBindings();

//    for ( QList<BindingSet>::const_iterator it = bindings.constBegin(); it != bindings.constEnd(); ++it ) {
//      const BindingSet& bindingTest = *it;
//        qiLogError() << "________________";
//        Q_FOREACH(QString name, bindingTest.bindingNames())
//        {
//          qiLogError() << name.toStdString();
//          qiLogError() << bindingTest[name].toString().toStdString();
//        }
//        qiLogError() << "________________";

//      }



    for ( QList<BindingSet>::const_iterator it = bindings.constBegin(); it != bindings.constEnd(); ++it ) {
      const BindingSet& binding = *it;
      if(inferedStatementFound)
        return 0;

//      rule.bindPreconditions( binding );
      BindingSet mergedBinding = rule.mergeBindingStatement(binding);
      // To be sure that ?a is never equal to ?b

//        qiLogError() << "________________";
//      Q_FOREACH(QString name, binding.bindingNames())
//      {
//        qiLogError() << name.toStdString();
//        qiLogError() << binding[name].toString().toStdString();
//      }
//        qiLogError() << "________________";


      bool sameBinding = xCheckVariablesValues(mergedBinding);

      if(sameBinding)
      {
        qDebug() << "Same binding not infering";
        continue;
      }
//      else
//      {
//        inferedStatementFound = true;
//      }

      //            qDebug() << "Queried rule bindings for rule" << rule << "with rule query" << q << ":" << binding;

      Statement inferedStatement = rule.bindEffect( binding );

      qDebug() << "======== INFERED STATEMENTS =========";
      qDebug() << inferedStatement.subject().toString();
      qDebug() << inferedStatement.predicate().toString();
      qDebug() << inferedStatement.object().toString();
      qDebug() << "=====================================";

      // we only add infered statements if they are not already present (in any named graph, aka. context)
      if ( inferedStatement.isValid() ) {
        if(!rule.condition().isEmpty() && !parentModel()->executeQuery( rule.condition(), Query::QueryLanguageSparql ).allBindings().size())
        {
          qDebug() << parentModel()->executeQuery( rule.condition(), Query::QueryLanguageSparql ).allBindings().size();
          qDebug() << "CONDITION NOT FULFILLED";
          qDebug() << rule.condition();
          return 0;
        }
        if( !parentModel()->containsAnyStatement( inferedStatement ) || rule.effectStyle() == "negation")
        {
          ++inferedStatementsCount;

          QUrl inferenceGraphUrl = createRandomUri();

          // write the actual infered statement
          inferedStatement.setContext( inferenceGraphUrl );
          if(rule.effectStyle() == "update")
          {
            Soprano::StatementIterator matchingStatements = parentModel()->listStatements(inferedStatement.subject(),
                                                                                          inferedStatement.predicate(),
                                                                                          Soprano::Node::createEmptyNode(),
                                                                                          Soprano::Node::createEmptyNode());

            QList<Soprano::Node> inferedContexts;

            Soprano::NodeIterator matchContexts = matchingStatements.iterateContexts();
            while(matchContexts.next())
            {

              inferedContexts.append(matchContexts.current());
            }


            Q_FOREACH(Soprano::Node context, inferedContexts)
            {
              parentModel()->removeAllStatements(
                    context,
                    Soprano::Node::createEmptyNode(),
                    Soprano::Node::createEmptyNode(),
                    Soprano::Node::createEmptyNode());

              parentModel()->removeAllStatements(
                    Soprano::Node::createEmptyNode(),
                    Soprano::Node::createEmptyNode(),
                    Soprano::Node::createEmptyNode(),
                    context);
            }
          }
          else if(rule.effectStyle() == "xor")
          {
            Soprano::StatementIterator matchingStatements = parentModel()->listStatements(inferedStatement.subject(),
                                                                                          inferedStatement.predicate(),
                                                                                          inferedStatement.object(),
                                                                                          Soprano::Node::createEmptyNode());
            while (matchingStatements.next())
            {
              parentModel()->removeStatement(matchingStatements.current());
            }
            parentModel()->addStatement( Statement( inferenceGraphUrl,
                                                    Vocabulary::RDF::type(),
                                                    Vocabulary::SIL::InferenceGraph(),
                                                    Vocabulary::SIL::InferenceMetaData() ) );

            parentModel()->addStatement( Statement( inferenceGraphUrl,
                                                    Vocabulary::RDF::Statement(),
                                                    compressStatement(inferedStatement),
                                                    Vocabulary::SIL::InferenceMetaData() ) );

            parentModel()->removeStatement(inferedStatement);

            QList<Statement> sourceStatements = rule.bindPreconditions( binding );
            for ( QList<Statement>::const_iterator sit = sourceStatements.constBegin();
                  sit != sourceStatements.constEnd(); ++sit )
            {
              const Statement& sourceStatement = *sit;

              if ( d->compressedStatements )
              {
                // remember the statement through a checksum (well, not really a checksum for now ;)
                parentModel()->addStatement( Statement( inferenceGraphUrl,
                                                        Vocabulary::SIL::sourceStatement(),
                                                        compressStatement( sourceStatement ),
                                                        Vocabulary::SIL::InferenceMetaData() ) );
              }
            }

            return inferedStatementsCount;
          }
          else if(rule.effectStyle() == "negation")
          {
            Soprano::Node sourceMetaDataNode = createMetadataNode(rule.boundToStatement());

            Soprano::Node inferencedMetaDataNode = createMetadataNode(inferedStatement);


// WARNING: The inference is not working if we use    parentModel()->addStatement
            FilterModel::addStatement(sourceMetaDataNode,
                                      Vocabulary::RDF::isDisabled(),
                                      inferencedMetaDataNode,
                                      Vocabulary::SIL::InferenceMetaData());


//             parentModel()->addStatement(inferencedMetaDataNode,
//                                        Vocabulary::RDF::isDisabled(),
//                                        Vocabulary::RDF::createAldebaranRessource("True"));

//            parentModel()->removeStatement(Statement(inferedStatement.subject(),
//                                                     inferedStatement.predicate(),
//                                                     inferedStatement.object(),
//                                                     Soprano::Node::createEmptyNode()));

            removeStatement(Statement(inferedStatement.subject(),
                                      inferedStatement.predicate(),
                                      inferedStatement.object(),
                                      Soprano::Node::createEmptyNode()));


            return inferedStatementsCount;
          }
          else
          {
            // Create metadataStatement for inferedStatements
            createMetadataNode(inferedStatement);
            parentModel()->addStatement( inferedStatement );
          }


          // write the metadata about the new inference graph into the inference metadata graph
          // type of the new graph is sil:InferenceGraph
          parentModel()->addStatement( Statement( inferenceGraphUrl,
                                                  Vocabulary::RDF::type(),
                                                  Vocabulary::SIL::InferenceGraph(),
                                                  Vocabulary::SIL::InferenceMetaData() ) );

          // add sourceStatements
          QList<Statement> sourceStatements = rule.bindPreconditions( binding );

          for ( QList<Statement>::const_iterator sit = sourceStatements.constBegin();
                sit != sourceStatements.constEnd(); ++sit ) {
            const Statement& sourceStatement = *sit;

            if ( d->compressedStatements ) {
              // remember the statement through a checksum (well, not really a checksum for now ;)
              parentModel()->addStatement( Statement( inferenceGraphUrl,
                                                      Vocabulary::SIL::sourceStatement(),
                                                      compressStatement( sourceStatement ),
                                                      Vocabulary::SIL::InferenceMetaData() ) );
            }
            else {
              // remember the source statement as a source for our graph
              parentModel()->addStatement( Statement( inferenceGraphUrl,
                                                      Vocabulary::SIL::sourceStatement(),
                                                      storeUncompressedSourceStatement( sourceStatement ),
                                                      Vocabulary::SIL::InferenceMetaData() ) );
            }
          }

          // remember the infered statements to recurse later on
          if ( recurse ) {
            inferedStatements << inferedStatement;
          }
        }
      }
      //             else {
      //                 qDebug() << "Inferred statement is invalid (this is no error):" << inferedStatement;
      //             }
    }


    // We only recurse after finishing the loop since this will reset the bound statement
    // in the rule which leads to a lot of confusion
    if ( recurse && inferedStatementsCount ) {
      foreach( const Statement& s, inferedStatements ) {
        inferedStatementsCount += inferStatement( s, true );
      }
    }

    return inferedStatementsCount;
  }
}

bool Soprano::Inference::InferenceModel::xCheckVariablesValues(BindingSet binding)
{
  bool sameBinding = false;
    qDebug() << "###################";

    QMap <QString, QString> sortedBindingMap;

    Q_FOREACH(QString name, binding.bindingNames())
    {
      qDebug() << "-------------------";
      qDebug() << name;
      qDebug() << binding[name].toString();

      qDebug() << "-------------------";
      if(!sortedBindingMap.keys().contains(name) || sortedBindingMap[name] != binding[name].toString())
        sortedBindingMap[name] = binding[name].toString();
    }


//    if(sortedBindingMap.keys().size() == 0)
//      return false;

  Q_FOREACH(QString bindingName, sortedBindingMap.keys())
  {
//    qiLogError() << name.toStdString();
//    qiLogError() << binding[name].toString().toStdString();

    qDebug() << bindingName;
    qDebug() << sortedBindingMap[bindingName];

//    if (d->bindingMapHistory.values().contains(binding.value(name).toString()))
    if (d->bindingMapHistory.values().contains(sortedBindingMap[bindingName]))
    {
      if(d->bindingMapHistory[bindingName] != sortedBindingMap[bindingName])
      {
      sameBinding = true;
      }
    }
    else
    {
//      d->bindingMapHistory.insert(name, binding.value(name).toString());
      d->bindingMapHistory.insert(bindingName, sortedBindingMap[bindingName]);
    }
  }
    qDebug() << "###################";
  if(sameBinding)
  {
    d->bindingMapHistory.clear();
    return true;
  }
  else
  {
    return false;
  }
}


QUrl Soprano::Inference::InferenceModel::storeUncompressedSourceStatement( const Statement& sourceStatement )
{
    QUrl sourceStatementUri = createRandomUri();
    parentModel()->addStatement( Statement( sourceStatementUri,
                                            Vocabulary::RDF::type(),
                                            Vocabulary::RDF::Statement(),
                                            Vocabulary::SIL::InferenceMetaData() ) );

    parentModel()->addStatement( Statement( sourceStatementUri,
                                            Vocabulary::RDF::subject(),
                                            sourceStatement.subject(),
                                            Vocabulary::SIL::InferenceMetaData() ) );
    parentModel()->addStatement( Statement( sourceStatementUri,
                                            Vocabulary::RDF::predicate(),
                                            sourceStatement.predicate(),
                                            Vocabulary::SIL::InferenceMetaData() ) );
    parentModel()->addStatement( Statement( sourceStatementUri,
                                            Vocabulary::RDF::object(),
                                            sourceStatement.object(),
                                            Vocabulary::SIL::InferenceMetaData() ) );
    if ( sourceStatement.context().isValid() ) {
        parentModel()->addStatement( Statement( sourceStatementUri,
                                                Vocabulary::SIL::context(),
                                                sourceStatement.context(),
                                                Vocabulary::SIL::InferenceMetaData() ) );
    }
    return sourceStatementUri;
}

Soprano::Node Soprano::Inference::InferenceModel::getMetadataNode(const Statement& sourceStatement)
{
//  QTime timer;
//  timer.start();

  Soprano::Node metadataSubject = Soprano::Node::createResourceNode(Vocabulary::RDF::metadata("subject"));
//  Soprano::Node metadataPredicate = Soprano::Node::createResourceNode(Vocabulary::RDF::metadata("predicate"));
//  Soprano::Node metadataObject = Soprano::Node::createResourceNode(Vocabulary::RDF::metadata("object"));

//  QString subject = sourceStatement.subject().toString();
//  QString predicate = sourceStatement.predicate().toString();
//  QString object = sourceStatement.object().toString();

//    QString stringQuery =
//      "PREFIX al:<http://softbank.org/sharedKnowledge#> \n"
//      "select ?metadata where { \n"
//      "?metadata <" + metadataSubject.toString() +"> <"+ subject + "> . \n"
//      "?metadata <" + metadataPredicate.toString() +"> <"+ predicate+ "> . \n"
//      "?metadata <" + metadataObject.toString() +"> <"+ object + "> .}";


//QList<Soprano::BindingSet> allBindings = executeQuery(stringQuery, Soprano::Query::QueryLanguageSparql).allBindings();
//  Q_FOREACH(Soprano::BindingSet bs, allBindings)
//  {
//    if(bs.value("metadata").isValid())
//    {
//      return  bs.value("metadata");
//    }
//  }
//  return Soprano::Node();

// Soprano::QueryResultIterator it = executeQuery(stringQuery, Soprano::Query::QueryLanguageSparql);
// while(it.next())
// {
//   return it.binding("metadata");
// }
//  return Soprano::Node();


  Soprano::Node metaDomain = Soprano::Node::createResourceNode(Vocabulary::RDF::createAldebaranRessource("metaDomain"));

  Node metaDataNode = Soprano::Node::createResourceNode(Vocabulary::RDF::createAldebaranRessource(createUuidFromStatement(sourceStatement)));

//  if(containsStatement(metaDataNode, metadataSubject, sourceStatement.subject(),Soprano::Node::createEmptyNode()))
  if(containsStatement(metaDataNode, metadataSubject, sourceStatement.subject(), metaDomain))
  {
    return metaDataNode;
  }

//  Soprano::StatementIterator statements = parentModel()->listStatements(Soprano::Node::createEmptyNode(),
//                                                         metadataObject,
//                                                         sourceStatement.object(),
//                                                         Soprano::Node::createEmptyNode());
//  qiLogError("LIST META") << timer.elapsed();
////  timer.restart();

//  int metaCount = 0;
//  while(statements.next())
//  {
//  metaCount++;
//    if(
//    containsAnyStatement(statements.current().subject(), metadataPredicate,sourceStatement.predicate() , Soprano::Node::createEmptyNode()) &&
//    containsAnyStatement(statements.current().subject(), metadataSubject, sourceStatement.subject(), Soprano::Node::createEmptyNode()))
//    {
//     return statements.current().subject();
//    }
//  }
//    qiLogError("META TO CHECK") << metaCount;
//    qiLogError("CONTAINS META") << timer.elapsed();
//  timer.restart();



  return Soprano::Node();
}


QString Soprano::Inference::InferenceModel::xUrlConversion(const Soprano::Node& node)
{
  QStringList splitedNode = node.toString().split("http://softbank.org/sharedKnowledge#");

  if(splitedNode.size() < 2)
    return node.toString();

  QString nodeValue = "http://softbank.org/sharedKnowledge#" +QUrl::toPercentEncoding(splitedNode[1]);
  return nodeValue;
}

Soprano::Node Soprano::Inference::InferenceModel::createMetadataNode(const Statement& statement)
{
  if(!statement.object().isResource())
  {
    throw std::runtime_error("Only statement with object of type ResourceNode have a meta node");
  }

  Soprano::Node metaDataNode  = getMetadataNode(statement);
  if(!metaDataNode.isEmpty())
  {
    return metaDataNode;
  }

//  metaDataNode = Soprano::Node::createResourceNode(Vocabulary::RDF::createAldebaranRessource(createUuid()));
  metaDataNode = Soprano::Node::createResourceNode(Vocabulary::RDF::createAldebaranRessource(createUuidFromStatement(statement)));

  Soprano::Node metadataSubject = Soprano::Node::createResourceNode(Vocabulary::RDF::metadata("subject"));
  Soprano::Node metadataPredicate = Soprano::Node::createResourceNode(Vocabulary::RDF::metadata("predicate"));
  Soprano::Node metadataObject = Soprano::Node::createResourceNode(Vocabulary::RDF::metadata("object"));



//  time += timer.elapsed();
//  qiLogError("META") << timer.elapsed();

  Soprano::Node metaDomain = Soprano::Node::createResourceNode(Vocabulary::RDF::createAldebaranRessource("metaDomain"));

  parentModel()->addStatement(metaDataNode,
                              metadataSubject,
                              statement.subject(),
                              metaDomain);
//                              Soprano::Node::createEmptyNode());

  parentModel()->addStatement(metaDataNode,
                              metadataPredicate,
                              statement.predicate(),
                              metaDomain);
//                              Soprano::Node::createEmptyNode());

  parentModel()->addStatement(metaDataNode,
                              metadataObject,
                              statement.object(),
                              metaDomain);
//                              Soprano::Node::createEmptyNode());

  //  if(getMetadataNode(statement).isEmpty())
  //    std::cout << "WHAT THE FUCK" << std::endl;

//  metaDataNode  = getMetadataNode(statement);
//  if(metaDataNode.isEmpty())
//  {
//  }

//  time += timer.elapsed();
//  qiLogError("META") << timer.elapsed();

  return metaDataNode;
}

void Soprano::Inference::InferenceModel::cleanMetadata(Soprano::Node metadataNode)
{
  if(parentModel()->listStatements(metadataNode,
                                   Soprano::Node::createEmptyNode(),
                                   Soprano::Node::createEmptyNode(),
                                   Vocabulary::SIL::InferenceMetaData()).allStatements().size() == 0)
  {
    removeStatements(parentModel()->listStatements(metadataNode,
                                                   Vocabulary::RDF::metadata("subject"),
                                                   Soprano::Node::createEmptyNode(),
                                                   Soprano::Node::createEmptyNode()).allStatements());

    removeStatements(parentModel()->listStatements(metadataNode,
                                                   Vocabulary::RDF::metadata("predicate"),
                                                   Soprano::Node::createEmptyNode(),
                                                   Soprano::Node::createEmptyNode()).allStatements());

    removeStatements(parentModel()->listStatements(metadataNode,
                                                   Vocabulary::RDF::metadata("object"),
                                                   Soprano::Node::createEmptyNode(),
                                                   Soprano::Node::createEmptyNode()).allStatements());
  }
}

Soprano::Statement Soprano::Inference::InferenceModel::getStatementFromMetadataNode(Soprano::Node metadataNode)
{
  Soprano::Statement statement;

  QList<Statement> metadataSubjectStatement = listStatements(metadataNode,
                                                             Vocabulary::RDF::metadata("subject"),
                                                             Soprano::Node::createEmptyNode(),
                                                             Soprano::Node::createEmptyNode()).allStatements();

  QList<Statement> metadataPredicateStatement = listStatements(metadataNode,
                                                               Vocabulary::RDF::metadata("predicate"),
                                                               Soprano::Node::createEmptyNode(),
                                                               Soprano::Node::createEmptyNode()).allStatements();

  QList<Statement> metadataObjectStatement = listStatements(metadataNode,
                                                            Vocabulary::RDF::metadata("object"),
                                                            Soprano::Node::createEmptyNode(),
                                                            Soprano::Node::createEmptyNode()).allStatements();

  if(metadataSubjectStatement.size() == 1 &&
     metadataPredicateStatement.size() == 1 &&
     metadataObjectStatement.size() == 1)
  {
    statement.setSubject(metadataSubjectStatement[0].object());
    statement.setPredicate(metadataPredicateStatement[0].object());
    statement.setObject(metadataObjectStatement[0].object());
    return statement;
  }

  if(metadataSubjectStatement.size() < 1 ||
     metadataPredicateStatement.size() < 1 ||
     metadataObjectStatement.size() < 1)
  {
    qiLogInfo() << "This id does not correspond to any triplet";
  }
  else if (metadataSubjectStatement.size() > 1 ||
           metadataPredicateStatement.size() > 1 ||
           metadataObjectStatement.size() > 1)
  {
    qiLogInfo() << " More than 3 metadata nodes are linked to this node";
  }

  //Removing all incoherent triplets link to this metadaNode.
  removeAllStatements(metadataNode,
                      Soprano::Node::createEmptyNode(),
                      Soprano::Node::createEmptyNode(),
                      Soprano::Node::createEmptyNode());
  removeAllStatements(Soprano::Node::createEmptyNode(),
                      Soprano::Node::createEmptyNode(),
                      metadataNode,
                      Soprano::Node::createEmptyNode());

  return statement;
}
