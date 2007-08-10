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

#include "indexfiltermodel.h"
#include "cluceneindex.h"

#include <soprano/statementiterator.h>


class Soprano::Index::IndexFilterModel::Private
{
public:
    bool deleteIndex;
    CLuceneIndex* index;
};


Soprano::Index::IndexFilterModel::IndexFilterModel( const QString& dir, Soprano::Model* model )
    : FilterModel( model ),
      d( new Private() )
{
    d->index = new CLuceneIndex();
    d->index->open( dir );
    d->deleteIndex = true;
}


Soprano::Index::IndexFilterModel::IndexFilterModel( CLuceneIndex* index, Soprano::Model* model )
    : FilterModel( model ),
      d( new Private() )
{
    d->index = index;
    d->deleteIndex = false;
}


Soprano::Index::IndexFilterModel::~IndexFilterModel()
{
    if ( d->deleteIndex ) {
        delete d->index;
    }
    delete d;
}


Soprano::Index::CLuceneIndex* Soprano::Index::IndexFilterModel::index() const
{
    return d->index;
}

Soprano::ErrorCode Soprano::Index::IndexFilterModel::addStatement( const Soprano::Statement &statement )
{
    d->index->addStatement( statement );
    return FilterModel::addStatement( statement );
}


Soprano::ErrorCode Soprano::Index::IndexFilterModel::removeStatements( const Soprano::Statement &statement )
{
    // since we use backends that directly implement this method we don't know which
    // statements are actually removed (there is no signal for that)
    // so we have to check that up front
    // FIXME: can we handle this is the CLuceneIndex?
    Soprano::StatementIterator it = parentModel()->listStatements( statement );
    while ( it.next() ) {
        d->index->removeStatement( *it );
    }

    return FilterModel::removeStatements( statement );
}