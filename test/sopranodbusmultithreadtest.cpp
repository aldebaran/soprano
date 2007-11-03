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

#include "sopranodbusmultithreadtest.h"
#include "../server/dbus/dbusclient.h"
#include "../server/dbus/dbusmodel.h"
#include "../soprano/storagemodel.h"

#include <QtTest/QtTest>


using namespace Soprano;
using namespace Soprano::Client;


SopranoDBusMultiThreadingTest::SopranoDBusMultiThreadingTest()
{
    m_client = new DBusClient();
    m_modelCnt = 0;
}


SopranoDBusMultiThreadingTest::~SopranoDBusMultiThreadingTest()
{
    delete m_client;
}


Soprano::Model* SopranoDBusMultiThreadingTest::createModel()
{
    return m_client->createModel( QString( "Testmodel%1" ).arg( m_modelCnt++ ) );
}

QTEST_MAIN( SopranoDBusMultiThreadingTest )

#include "sopranodbusmultithreadtest.moc"