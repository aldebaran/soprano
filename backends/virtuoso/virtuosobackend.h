/*
 * This file is part of Soprano Project
 *
 * Copyright (C) 2008 Sebastian Trueg <trueg@kde.org>
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

#ifndef _SOPRANO_VIRTUOSO_BACKEND_H_
#define _SOPRANO_VIRTUOSO_BACKEND_H_

#include "backend.h"

#include <QtCore/QObject>
#include <QtCore/QMutex>


namespace Soprano {
    namespace ODBC {
        class Environment;
    }

    namespace Virtuoso {
        class BackendPlugin : public QObject, public Soprano::Backend
        {
            Q_OBJECT
            Q_INTERFACES(Soprano::Backend)

        public:
            BackendPlugin();
            ~BackendPlugin();

            StorageModel* createModel( const BackendSettings& settings = BackendSettings() ) const;
            bool deleteModelData( const BackendSettings& settings ) const;
            BackendFeatures supportedFeatures() const;
            bool isAvailable() const;

#ifndef Q_OS_WIN
        private:
            static QString findVirtuosoDriver();
#endif
        };
    }
}

#endif
