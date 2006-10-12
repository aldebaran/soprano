/* This file is part of QRDF
 *
 * Copyright (C) 2006 Duncan Mac-Vicar <duncan@kde.org>
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

#include <redland.h>
#include "model.h"
#include "world.h"
#include "statement.h"

using namespace RDF;

struct Model::Private
{
  Private() : model(0L)
  {}
  librdf_model* model;
  World world;
};

Model::Model( const Model &rhs )
{
  d = new Private;
  d->model = librdf_new_model_from_model( rhs.modelPtr() );
  Q_ASSERT(d->model != NULL);
}

Model::Model( Storage *storage, const QString &options )
{
  d = new Private;
  d->model = librdf_new_model(d->world.worldPtr(), storage->storagePtr(), options.toLatin1().data());
  Q_ASSERT(d->model != NULL);
   
}

Model::~Model()
{
  librdf_free_model(d->model);
}

bool Model::containsStatement( Statement *s ) const
{
  return ( librdf_model_contains_statement(d->model, s->statementPtr()) != 0 );
}

void Model::add( Node *subject, Node *predicate, Node *object )
{
  librdf_model_add( d->model, subject->nodePtr(), predicate->nodePtr(), object->nodePtr() );
}

void Model::addStringLiteralStatement( Node *subject, Node *predicate, const QString &literal )
{
  librdf_model_add_string_literal_statement ( d->model, subject->nodePtr(), predicate->nodePtr(), (const unsigned char*) literal.toLatin1().constData(), NULL, 0);
}

int Model::size() const
{
  return librdf_model_size(d->model);
}

void Model::addStatement( Statement *s )
{
  librdf_model_add_statement( d->model, s->statementPtr() );
}

void Model::removeStatement( Statement *s )
{
  librdf_model_remove_statement( d->model, s->statementPtr() );
}

librdf_model* Model::modelPtr() const
{
  return d->model;
}
