/* This file is part of QRDF
 *
 * Copyright (C) 2006 Daniele Galdi <daniele.galdi@gmail.com>
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
 * You should have received a copy of the GNU Library General Public
 * License
 * along with this library; see the file COPYING.LIB.  If not, write
 * to
 * the Free Software Foundation, Inc., 51 Franklin Street, Fifth
 * Floor,
 * Boston, MA 02110-1301, USA.
 */

#ifndef REDLAND_QUERY_RESULT_H
#define REDLAND_QUERY_RESULT_H

#include <QString>
#include <redland.h>
#include "QueryResult.h"

namespace RDF {

class Node;

class RedlandQueryResult: public QueryResult
{
public:
  RedlandQueryResult( librdf_query_results *result );

  virtual ~RedlandQueryResult();
    
  int size() const;
  
  bool hasNext() const;

  bool next();
    
  Node *get( const QString &name ) const;

  bool isBoolean() const;

  bool boolean() const;
private:
  class Private;
  Private *d;
};
 
}

#endif //REDLAND_QUERY_RESULT_H

