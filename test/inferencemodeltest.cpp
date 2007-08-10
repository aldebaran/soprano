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

#include "inferencemodeltest.h"
#include <soprano/soprano.h>
#include <soprano/vocabulary/rdfs.h>
#include <soprano/inference/inferencemodel.h>
#include <soprano/inference/statementpattern.h>
#include <soprano/inference/nodepattern.h>
#include <soprano/inference/inferencerule.h>

#include <QtTest/QTest>
#include <QtCore/QDebug>
#include <QtCore/QTime>


void InferenceModelTest::initTestCase()
{
    m_model = Soprano::createModel();
    QVERIFY( m_model );
    m_infModel = new InferenceModel( m_model );

    // create a simple rule
    Rule rule;
    rule.addPrecondition( StatementPattern( NodePattern( "x" ), NodePattern( Vocabulary::RDFS::SUBCLASSOF() ), NodePattern( "y" ) ) );
    rule.addPrecondition( StatementPattern( NodePattern( "y" ), NodePattern( Vocabulary::RDFS::SUBCLASSOF() ), NodePattern( "z" ) ) );
    rule.setEffect( StatementPattern( NodePattern( "x" ), NodePattern( Vocabulary::RDFS::SUBCLASSOF() ), NodePattern( "z" ) ) );

    m_infModel->addRule( rule );
}


void InferenceModelTest::cleanupTestCase()
{
    delete m_infModel;
    delete m_model;
}


void InferenceModelTest::init()
{
    m_model->removeAllStatements();
}


void InferenceModelTest::testAddStatementSingle()
{
    Statement s1( QUrl( "test#A" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#B" ) );
    Statement s2( QUrl( "test#B" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#C" ) );

    Statement s3( QUrl( "test#A" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#C" ) );

    m_infModel->addStatement( s1 );

    // at this point nothing should be infered
    StatementIterator it = m_model->listStatements();
    QVERIFY( it.next() );
    QCOMPARE( s1, *it );
    QVERIFY( !it.next() );

    m_infModel->addStatement( s2 );

    // now some inference should have been done

    // first check the actual triple we want to be infered
    QVERIFY( m_model->containsStatements( s3 ) );
}


void InferenceModelTest::testAddStatementMulti()
{
    // F -> E -> D -> C -> B -> A
    Statement fe( QUrl( "test#F" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#E" ) );
    Statement ed( QUrl( "test#E" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#D" ) );
    Statement dc( QUrl( "test#D" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#C" ) );
    Statement cb( QUrl( "test#C" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#B" ) );
    Statement ba( QUrl( "test#B" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#A" ) );

    // X -> B
    // X -> A
    Statement xb( QUrl( "test#X" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#C" ) );
    Statement xa( QUrl( "test#X" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#A" ) );

    // we throw them all in adn check the inference afterwards
    m_infModel->addStatement( fe );
    m_infModel->addStatement( ed );
    m_infModel->addStatement( dc );
    m_infModel->addStatement( cb );
    m_infModel->addStatement( ba );
    m_infModel->addStatement( xa );
    m_infModel->addStatement( xb );

    // now check that we have all the inferred statements
    QVERIFY( m_model->containsStatements( Statement( QUrl( "test#F" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#A" ) ) ) );
    QVERIFY( m_model->containsStatements( Statement( QUrl( "test#F" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#B" ) ) ) );
    QVERIFY( m_model->containsStatements( Statement( QUrl( "test#F" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#C" ) ) ) );
    QVERIFY( m_model->containsStatements( Statement( QUrl( "test#F" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#D" ) ) ) );

    QVERIFY( m_model->containsStatements( Statement( QUrl( "test#E" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#A" ) ) ) );
    QVERIFY( m_model->containsStatements( Statement( QUrl( "test#E" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#B" ) ) ) );
    QVERIFY( m_model->containsStatements( Statement( QUrl( "test#E" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#C" ) ) ) );

    QVERIFY( m_model->containsStatements( Statement( QUrl( "test#D" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#A" ) ) ) );
    QVERIFY( m_model->containsStatements( Statement( QUrl( "test#D" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#B" ) ) ) );

    QVERIFY( m_model->containsStatements( Statement( QUrl( "test#C" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#A" ) ) ) );

    QVERIFY( m_model->containsStatements( Statement( QUrl( "test#X" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#B" ) ) ) );
}


void InferenceModelTest::testRemoveStatementsSingle()
{
    Statement s1( QUrl( "test#A" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#B" ) );
    Statement s2( QUrl( "test#B" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#C" ) );
    m_infModel->addStatement( s1 );
    m_infModel->addStatement( s2 );

    m_infModel->removeStatements( s1 );

    // now we should only have a single statement left
    StatementIterator it = m_model->listStatements();
    QVERIFY( it.next() );
    QCOMPARE( s2, *it );
    QVERIFY( !it.next() );
}


void InferenceModelTest::testRemoveStatementsMulti()
{
    // F -> E -> D -> C -> B -> A
    Statement fe( QUrl( "test#F" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#E" ) );
    Statement ed( QUrl( "test#E" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#D" ) );
    Statement dc( QUrl( "test#D" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#C" ) );
    Statement cb( QUrl( "test#C" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#B" ) );
    Statement ba( QUrl( "test#B" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#A" ) );

    // we throw them all in adn check the inference afterwards
    m_infModel->addStatement( fe );
    m_infModel->addStatement( ed );
    m_infModel->addStatement( dc );
    m_infModel->addStatement( cb );
    m_infModel->addStatement( ba );

    // now let's remove one in the middle
    m_infModel->removeStatements( cb );

    // now nothing should be based on A anymore, except for B
    QVERIFY( !m_model->containsStatements( Statement( QUrl( "test#F" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#A" ) ) ) );
    QVERIFY( !m_model->containsStatements( Statement( QUrl( "test#F" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#B" ) ) ) );
    QVERIFY( m_model->containsStatements( Statement( QUrl( "test#F" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#C" ) ) ) );
    QVERIFY( m_model->containsStatements( Statement( QUrl( "test#F" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#D" ) ) ) );

    QVERIFY( !m_model->containsStatements( Statement( QUrl( "test#E" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#A" ) ) ) );
    QVERIFY( !m_model->containsStatements( Statement( QUrl( "test#E" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#B" ) ) ) );
    QVERIFY( m_model->containsStatements( Statement( QUrl( "test#E" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#C" ) ) ) );

    QVERIFY( !m_model->containsStatements( Statement( QUrl( "test#D" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#A" ) ) ) );
    QVERIFY( !m_model->containsStatements( Statement( QUrl( "test#D" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#B" ) ) ) );
}


void InferenceModelTest::testPerformInference()
{
    Statement s1( QUrl( "test#A" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#B" ) );
    Statement s2( QUrl( "test#B" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#C" ) );
    m_model->addStatement( s1 );
    m_model->addStatement( s2 );

    m_infModel->performInference();

    Statement s3( QUrl( "test#A" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#C" ) );
    QVERIFY( m_model->containsStatements( s3 ) );
}


void InferenceModelTest::testPerformance()
{
    // F -> E -> D -> C -> B -> A
    Statement fe( QUrl( "test#F" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#E" ) );
    Statement ed( QUrl( "test#E" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#D" ) );
    Statement dc( QUrl( "test#D" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#C" ) );
    Statement cb( QUrl( "test#C" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#B" ) );
    Statement ba( QUrl( "test#B" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#A" ) );

    // X -> B
    // X -> A
    Statement xb( QUrl( "test#X" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#C" ) );
    Statement xa( QUrl( "test#X" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#A" ) );

    // we just do some performance comparision
    QTime timer;
    timer.start();

    m_infModel->addStatement( fe );
    m_infModel->addStatement( ed );
    m_infModel->addStatement( dc );
    m_infModel->addStatement( cb );
    m_infModel->addStatement( ba );
    m_infModel->addStatement( xa );
    m_infModel->addStatement( xb );

    qDebug() << "Time for adding with inferencing: " << timer.elapsed();

    m_model->removeAllStatements();


    timer.start();
    m_model->addStatement( fe );
    m_model->addStatement( ed );
    m_model->addStatement( dc );
    m_model->addStatement( cb );
    m_model->addStatement( ba );
    m_model->addStatement( xa );
    m_model->addStatement( xb );

    qDebug() << "Time for adding without inferencing: " << timer.elapsed();
}


void InferenceModelTest::testClearInference()
{
    Statement s1( QUrl( "test#A" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#B" ) );
    Statement s2( QUrl( "test#B" ), Vocabulary::RDFS::SUBCLASSOF(), QUrl( "test#C" ) );
    m_infModel->addStatement( s1 );
    m_infModel->addStatement( s2 );

    m_infModel->clearInference();

    StatementIterator it = m_model->listStatements();
    QVERIFY( it.next() );
    QVERIFY( it.current() == s1 || it.current() == s2 );
    QVERIFY( it.next() );
    QVERIFY( it.current() == s1 || it.current() == s2 );
    QVERIFY( !it.next() );
}

QTEST_MAIN( InferenceModelTest );

#include "inferencemodeltest.moc"