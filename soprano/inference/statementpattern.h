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

#ifndef _SOPRANO_STATEMENT_PATTERN_H_
#define _SOPRANO_STATEMENT_PATTERN_H_

#include <QtCore/QSharedDataPointer>

#include "soprano_export.h"


namespace Soprano {

    class Statement;

    namespace Inference {

	class NodePattern;

	class SOPRANO_EXPORT StatementPattern
	{
	public:
	    StatementPattern();
	    StatementPattern( const NodePattern&, const NodePattern&, const NodePattern& );
	    StatementPattern( const StatementPattern& );
	    ~StatementPattern();

	    StatementPattern operator=( const StatementPattern& );

	    NodePattern subjectPattern() const;
	    NodePattern predicatePattern() const;
	    NodePattern objectPattern() const;

	    bool match( const Statement& ) const;

	    QString createSparqlGraphPattern() const;

	private:
	    class Private;
	    QSharedDataPointer<Private> d;
	};
    }
}

#endif