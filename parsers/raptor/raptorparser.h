/* 
 * This file is part of Soprano Project
 *
 * Copyright (C) 2006 Duncan Mac-Vicar <duncan@kde.org>
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

#ifndef _SOPRANO_RAPTOR_PARSER_H_
#define _SOPRANO_RAPTOR_PARSER_H_

#include <QtCore/QUrl>
#include <QtCore/QObject>
#include <QtCore/QMutex>

#include "parser.h"

#include <raptor.h>

namespace Soprano {
    namespace Raptor {
      class Parser : public QObject, public Soprano::Parser { 
        Q_OBJECT
        Q_INTERFACES(Soprano::Parser)
#if QT_VERSION >= QT_VERSION_CHECK(5, 0, 0)
        Q_PLUGIN_METADATA(IID "org.soprano.plugins.Parser/1.0")
#endif

    public:
        Parser();
        ~Parser();

	RdfSerializations supportedSerializations() const;

        StatementIterator parseFile( const QString& filename, 
                     const QUrl& baseUri, 
                     RdfSerialization serialization,
                     const QString& userSerialization = QString() ) const;
        StatementIterator parseString( const QString& data, 
                       const QUrl& baseUri, 
                       RdfSerialization serialization,
                       const QString& userSerialization = QString() ) const;
        StatementIterator parseStream( QTextStream&, 
                       const QUrl& baseUri, 
                       RdfSerialization serialization,
                       const QString& userSerialization = QString() ) const;

        void setError( const Soprano::Error::Error& error ) const;

    private:
        raptor_parser* createParser( RdfSerialization serialization,
                     const QString& userSerialization = QString() ) const;

	class Private;
	Private * d;


    };
    }
}

#endif
