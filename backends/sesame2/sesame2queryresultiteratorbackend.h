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

#ifndef _SOPRANO_SESAME2_QUERY_RESULT_ITERATOR_BACKEND_H_
#define _SOPRANO_SESAME2_QUERY_RESULT_ITERATOR_BACKEND_H_

#include <soprano/queryresultiteratorbackend.h>

#include <jni.h>

#include "jobjectref.h"

class QString;
class QStringList;

namespace Soprano {

    class Node;
    class Statement;

    namespace Sesame2 {

    class Model;

    class QueryResultIteratorBackend : public Soprano::QueryResultIteratorBackend
    {
    public:
        QueryResultIteratorBackend( const JObjectRef& result, const Model* );
        QueryResultIteratorBackend( bool result, const Model* );
        ~QueryResultIteratorBackend();

        bool next();

        Statement currentStatement() const;

        Node binding( const QString &name ) const;

        Node binding( int offset ) const;

        int bindingCount() const;

        QStringList bindingNames() const;

        bool isGraph() const;

        bool isBinding() const;

        bool isBool() const;

        bool boolValue() const;

        void close();

    private:
        class Private;
        Private* const d;
    };
    }
}

#endif
