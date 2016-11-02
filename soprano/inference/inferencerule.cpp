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

#include "inferencerule.h"
#include "statementpattern.h"
#include "nodepattern.h"
#include "bindingset.h"

#include <QtCore/QString>
#include <QtCore/QStringList>
#include <QtCore/QDebug>
#include <QtCore/QUuid>
#include <qi/log.hpp>

qiLogCategory("inferencerule");


class Soprano::Inference::Rule::Private : public QSharedData
{
public:
    QList<StatementPattern> preconditions;
    StatementPattern effect;
    Statement bindingStatement;
    QString effectStyle;
    QString condition;
    QString origin;
    QString ruleId;
    QString ruleString;

    // Map containing the historic of bindings during inference.
    // this allow to make sure that bindings are used on time
    // ?a != ?b
    mutable QMap<QString, QString> bindingHistory;
    // Boolean representing wether or no a a binding has already been used
    mutable bool bindingAlreadyUsed;
};


Soprano::Inference::Rule::Rule()
    : d( new Private() )
{
  d->bindingAlreadyUsed = false;
  d->ruleId = QUuid::createUuid().toString();
}


Soprano::Inference::Rule::Rule( const Rule& other )
{
    d = other.d;
}


Soprano::Inference::Rule::~Rule()
{
}


Soprano::Inference::Rule& Soprano::Inference::Rule::operator=( const Rule& other )
{
    d = other.d;
    return *this;
}


QList<Soprano::Inference::StatementPattern> Soprano::Inference::Rule::preconditions() const
{
    return d->preconditions;
}


void Soprano::Inference::Rule::addPrecondition( const StatementPattern& sp )
{
    d->preconditions.append( sp );
}


Soprano::Inference::StatementPattern Soprano::Inference::Rule::effect() const
{
    return d->effect;
}


void Soprano::Inference::Rule::setEffect( const StatementPattern& e )
{
    d->effect = e;
}


QString Soprano::Inference::Rule::effectStyle() const
{
    return d->effectStyle;
}


void Soprano::Inference::Rule::setEffectStyle(const QString& effectStyle)
{
    d->effectStyle = effectStyle;
}


QString Soprano::Inference::Rule::condition() const
{
    return d->condition;
}


void Soprano::Inference::Rule::setCondition(const QString& condition)
{
    d->condition = condition;
}


void Soprano::Inference::Rule::bindToStatement( const Statement& statement )
{
    d->bindingStatement = statement;
}


Soprano::Statement Soprano::Inference::Rule::boundToStatement() const
{
    return d->bindingStatement;
}


bool Soprano::Inference::Rule::match( const Statement& statement ) const
{


    for ( QList<StatementPattern>::const_iterator it = d->preconditions.constBegin();
          it != d->preconditions.constEnd(); ++it ) {
        if ( it->match( statement ) ) {
            return true;
        }
    }
    return false;
}


QString Soprano::Inference::Rule::createSparqlQuery( bool bindStatement ) const
{
    QString query;

    Soprano::Node node;

    if ( !bindStatement || !d->bindingStatement.isValid() ) {
        for ( QList<StatementPattern>::const_iterator it = d->preconditions.constBegin();
              it != d->preconditions.constEnd(); ++it ) {
            query += it->createSparqlGraphPattern( BindingSet() ) + " . ";
        }
    }
    else {
        QStringList subQueries;

        // bind the statement to the variables in the query. If multiple bindings are possible use a SPARQL UNION
//        for ( QList<StatementPattern>::const_iterator it = d->preconditions.constBegin();
//              it != d->preconditions.constEnd(); ++it ) {
//            const StatementPattern& p = *it;
//           preconditions.append(*it);
//        }

        QList<StatementPattern> preconditions = d->preconditions;

        for ( QList<StatementPattern>::iterator it = preconditions.begin();
              it != preconditions.end(); ++it ) {
           StatementPattern& p = *it;


            if ( p.match( d->bindingStatement ) ) {
                BindingSet bindings;
                if ( p.subjectPattern().isVariable() ) {
                    bindings.insert( p.subjectPattern().variableName(), d->bindingStatement.subject() );
                }
                if ( p.predicatePattern().isVariable() ) {
                    bindings.insert( p.predicatePattern().variableName(), d->bindingStatement.predicate() );
                }
                if ( p.objectPattern().isVariable() ) {
                    bindings.insert( p.objectPattern().variableName(), d->bindingStatement.object());
                }

                // create a whole new subquery
                QString subQuery;
                for ( QList<StatementPattern>::const_iterator it2 = d->preconditions.constBegin();
                      it2 != d->preconditions.constEnd(); ++it2 ) {
                    // skip the one that is fully bound
                    if ( it2 != it ) {
                        subQuery += it2->createSparqlGraphPattern( bindings ) + " . ";
                    }
                }
                qDebug() << subQuery;

                // ensure that we do not query for statements that cannot be valid anyway
                // because the current bindings already render the effect invalid
                if ( d->effect.subjectPattern().isVariable() &&
                     bindings.contains( d->effect.subjectPattern().variableName() ) &&
                     bindings[d->effect.subjectPattern().variableName()].isLiteral() ) {
                    continue;
                }
                if ( d->effect.predicatePattern().isVariable() &&
                     bindings.contains( d->effect.predicatePattern().variableName() ) &&
                     !bindings[d->effect.predicatePattern().variableName()].isResource() ) {
                    continue;
                }

                // ========================================================================================
                // The following code is deactivated but kept for informational purposes:
                // the additional filters make sure we never get invalid statements in InferenceModel::inferRule
                // but the computational overhead of applying the filter in the Model overshadows
                // the overhead of enumerating and checking invalid statements.
#if 0
                // optimize the query by filtering useless results, i.e. those that
                // would create invalid statements by applying the effect
                QStringList filters;
                if ( d->effect.subjectPattern().isVariable() &&
                     !bindings.contains( d->effect.subjectPattern().variableName() ) ) {
                    filters += QString( "!isLiteral(?%1)" ).arg( d->effect.subjectPattern().variableName() );
                }
                if ( d->effect.predicatePattern().isVariable() &&
                     !bindings.contains( d->effect.predicatePattern().variableName() ) ) {
                    filters += QString( "isURI(?%1)" ).arg( d->effect.predicatePattern().variableName() );
                }
                if ( !filters.isEmpty() ) {
                    subQuery += QString( "FILTER( %1 ) . " ).arg( filters.join( " && " ) );
                }
#endif
                // ========================================================================================

                subQueries.append( subQuery );
            }
        }

        if ( subQueries.count() > 1 ) {
            query += "{ " + subQueries.join( " } UNION { " ) + " }";
        }
        else if( subQueries.count() > 0 ) {
            query += subQueries[0];
        }
    }

    if ( !query.isEmpty() ) {
        query = "SELECT * WHERE { " + query + '}';
    }

    return query;
}


Soprano::Statement Soprano::Inference::Rule::bindStatementPattern( const StatementPattern& pattern, const BindingSet& bindings ) const
{
    // below we make sure that all binding are available (in case of optimized queries the bindingStatement must not have changed)

    Statement s;
    if ( pattern.subjectPattern().isVariable() ) {
        s.setSubject( bindings[pattern.subjectPattern().variableName()] );
    }
    else {
        s.setSubject( pattern.subjectPattern().resource() );
    }

    if ( pattern.predicatePattern().isVariable() ) {
        s.setPredicate( bindings[pattern.predicatePattern().variableName()] );
    }
    else {
        s.setPredicate( pattern.predicatePattern().resource() );
    }

    if ( pattern.objectPattern().isVariable() ) {
        s.setObject( bindings[pattern.objectPattern().variableName()] );
    }
    else {
        s.setObject( pattern.objectPattern().resource() );
    }

    return s;
}


Soprano::Statement Soprano::Inference::Rule::bindStatementPattern2( const StatementPattern& pattern, const BindingSet& bindings ) const
{
    // below we make sure that all binding are available (in case of optimized queries the bindingStatement must not have changed)

    Statement s;
    if ( pattern.subjectPattern().isVariable() ) {
        s.setSubject( bindings[pattern.subjectPattern().variableName()] );
//        QString subjectVariableName = pattern.subjectPattern().variableName();
//        QString subjectVariableValue = bindings[pattern.subjectPattern().variableName()].toString();


//                Q_FOREACH(QString key, d->bindingHistory.keys())
//        {
//          qDebug() << key << " ----- " << d->bindingHistory[key];
//        }

//       if((!d->bindingHistory.keys().contains(subjectVariableName)
//          && !d->bindingHistory.values().contains(subjectVariableValue))
//          || d->bindingHistory[subjectVariableName] == subjectVariableValue)
//       {
//            d->bindingHistory[subjectVariableName] = subjectVariableValue;
//            qDebug() << "ICI1";
//        setBindingAlreadyUsed(false);
//       }
//       else
//       {
//         qDebug() << "LA1";
//         setBindingAlreadyUsed(true);
//       }

//                Q_FOREACH(QString key, d->bindingHistory.keys())
//        {
//          qDebug() << key << " ----- " << d->bindingHistory[key];
//        }
    }
    else {
        s.setSubject( pattern.subjectPattern().resource() );
    }

    if ( pattern.predicatePattern().isVariable() ) {
        s.setPredicate( bindings[pattern.predicatePattern().variableName()] );
    }
    else {
//              qDebug() << "&&&&&&&&&&&&";
//        qDebug() << pattern.predicatePattern().resource();
//        qDebug() << "&&&&&&&&&&&&";

        s.setPredicate( pattern.predicatePattern().resource() );
    }

    if ( pattern.objectPattern().isVariable() ) {
        s.setObject( bindings[pattern.objectPattern().variableName()] );
        QString objectVariableName = pattern.objectPattern().variableName();
        QString objectVariableValue = bindings[pattern.objectPattern().variableName()].toString();
        qDebug() << "============";
        qDebug() << objectVariableName;
        qDebug() << objectVariableValue;
        qDebug() << "============";

//                        Q_FOREACH(QString key, d->bindingHistory.keys())
//        {
//          qDebug() << key << " ----- " << d->bindingHistory[key];
//        }




//        if((!d->bindingHistory.keys().contains(objectVariableName)
//            && !d->bindingHistory.values().contains(objectVariableValue))
//           || (d->bindingHistory.count(objectVariableName) && d->bindingHistory[objectVariableName] == objectVariableValue))
//        {
//          d->bindingHistory[objectVariableName] = objectVariableValue;
//          qDebug() << "ICI2";
//        }
//        else
//        {
//          qDebug() << "LA2";
//          setBindingAlreadyUsed(true);
//        }
//                Q_FOREACH(QString key, d->bindingHistory.keys())
//        {
//          qDebug() << key << " ----- " << d->bindingHistory[key];
//        }

    }
    else {
        s.setObject( pattern.objectPattern().resource() );
    }

    return s;
}

void Soprano::Inference::Rule::clearBindingHistory() const
{
  d->bindingHistory.clear();
}

void Soprano::Inference::Rule::setBindingAlreadyUsed(bool alreadyUsed ) const
{
  d->bindingAlreadyUsed = alreadyUsed;
}

bool Soprano::Inference::Rule::isBindingAlreadyUsed() const
{
  return d->bindingAlreadyUsed;
}


Soprano::BindingSet Soprano::Inference::Rule::mergeBindingStatement( const BindingSet& bindings ) const
{
    //
    // Here we regenerate the information (bindings) we "removed" for optimization purposes in createSparqlGraphPattern
    // This can simply be done by matching the bindingStatement which was used to optimize the query to the precondition
    // that has no binding yet. Because that is the one which was removed from the optmized query
    //
    BindingSet bs( bindings );

    for ( QList<StatementPattern>::const_iterator it = d->preconditions.constBegin();
          it != d->preconditions.constEnd(); ++it ) {
        const StatementPattern& pattern = *it;
        if ( pattern.subjectPattern().isVariable() && bindings[pattern.subjectPattern().variableName()].isValid() ) {
            continue;
        }
        if ( pattern.predicatePattern().isVariable() && bindings[pattern.predicatePattern().variableName()].isValid() ) {
            continue;
        }
        if ( pattern.objectPattern().isVariable() && bindings[pattern.objectPattern().variableName()].isValid() ) {
            continue;
        }

        // update bindings
        if ( pattern.subjectPattern().isVariable() ) {
            bs.insert( pattern.subjectPattern().variableName(), d->bindingStatement.subject() );
        }
        if ( pattern.predicatePattern().isVariable() ) {
            bs.insert( pattern.predicatePattern().variableName(), d->bindingStatement.predicate() );
        }
        if ( pattern.objectPattern().isVariable() ) {
            bs.insert( pattern.objectPattern().variableName(), d->bindingStatement.object() );
        }
    }

    return bs;
}


Soprano::Statement Soprano::Inference::Rule::bindEffect( const BindingSet& bindings ) const
{
    return bindStatementPattern( d->effect, mergeBindingStatement( bindings ) );
}


QList<Soprano::Statement> Soprano::Inference::Rule::bindPreconditions( const BindingSet& bindings ) const
{
    // 2 sweeps: 1. update bindings by matching the bindingStatement to the precondition we left out in the
    //              optimized query creation. That gives us the rest of the bindings we need.
    //           2. actually bind all vars

    QList<Statement> sl;
    for ( QList<StatementPattern>::const_iterator it = d->preconditions.constBegin();
          it != d->preconditions.constEnd(); ++it ) {
        sl.append( bindStatementPattern2( *it, mergeBindingStatement( bindings ) ) );
    }

    return sl;
}

bool Soprano::Inference::Rule::isValid() const
{
    return !d->preconditions.isEmpty() && d->effect.isValid();
}

void Soprano::Inference::Rule::setRuleOrigin(const QString& ruleOrigin)
{
  d->origin = ruleOrigin;
}

QString Soprano::Inference::Rule::getRuleOrigin() const
{
  return d->origin;
}

QString Soprano::Inference::Rule:: getId() const
{
  return d->ruleId;
}

 void Soprano::Inference::Rule::setString(const QString& ruleString)
 {
   d->ruleString = ruleString;
 }

 QString Soprano::Inference::Rule::getString() const
 {
   return d->ruleString;
 }

QDebug operator<<( QDebug s, const Soprano::Inference::Rule& rule )
{
    s.nospace() << "[";
    QList<Soprano::Inference::StatementPattern> cl = rule.preconditions();
    QList<Soprano::Inference::StatementPattern>::const_iterator it = cl.constBegin();
    while ( it != cl.constEnd() ) {
        s.nospace() << *it;
        ++it;
        if ( it != cl.constEnd() ) {
            s.nospace() << ", ";
        }
    }
    s.nospace() << " -> " << rule.effect() << "]";
    if ( rule.boundToStatement().isValid() ) {
        s.nospace() << " (bound to statement " << rule.boundToStatement() << ")";
    }
    return s;
}
