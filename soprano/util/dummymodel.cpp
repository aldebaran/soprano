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

#include "dummymodel.h"
#include "statement.h"
#include "queryresultiterator.h"
#include "statementiterator.h"
#include "nodeiterator.h"
#include "query/query.h"


class Soprano::DummyModel::Private
{
public:
    Private()
        : defaultError( "Invalid model", Error::ERROR_NOT_SUPPORTED ) {
    }
    Error::Error defaultError;
};

Soprano::DummyModel::DummyModel()
    : Model(),
      d( new Private() )
{
}


Soprano::DummyModel::~DummyModel()
{
    delete d;
}


Soprano::Error::ErrorCode Soprano::DummyModel::addStatement( const Statement &statement )
{
    setError( d->defaultError );
    return Error::ERROR_NOT_SUPPORTED;
}


bool Soprano::DummyModel::isEmpty() const
{
    setError( d->defaultError );
    return true;
}


Soprano::NodeIterator Soprano::DummyModel::listContexts() const
{
    setError( d->defaultError );
    return NodeIterator();
}


bool Soprano::DummyModel::containsStatement( const Statement &statement ) const
{
    setError( d->defaultError );
    return false;
}


bool Soprano::DummyModel::containsAnyStatement( const Statement &statement ) const
{
    setError( d->defaultError );
    return false;
}


Soprano::QueryResultIterator Soprano::DummyModel::executeQuery( const Query::Query& query ) const
{
    setError( d->defaultError );
    return QueryResultIterator();
}


Soprano::QueryResultIterator Soprano::DummyModel::executeQuery( const QString& query, Query::QueryLanguage language, const QString& userQueryLanguage ) const
{
    setError( d->defaultError );
    return QueryResultIterator();
}


Soprano::StatementIterator Soprano::DummyModel::listStatements( const Statement &partial ) const
{
    setError( d->defaultError );
    return StatementIterator();
}


Soprano::Error::ErrorCode Soprano::DummyModel::removeStatement( const Statement &statement )
{
    setError( d->defaultError );
    return Error::ERROR_NOT_SUPPORTED;
}


Soprano::Error::ErrorCode Soprano::DummyModel::removeAllStatements( const Statement &statement )
{
    setError( d->defaultError );
    return Error::ERROR_NOT_SUPPORTED;
}


int Soprano::DummyModel::statementCount() const
{
    setError( d->defaultError );
    return 0;
}


Soprano::Node Soprano::DummyModel::createBlankNode()
{
    setError( d->defaultError );
    return Node();
}


Soprano::Error::ErrorCode Soprano::DummyModel::write( QTextStream &os ) const
{
    setError( d->defaultError );
    return Error::ERROR_NOT_SUPPORTED;
}

#include "dummymodel.moc"