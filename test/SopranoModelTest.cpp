/*
 * This file is part of Soprano Project.
 *
 * Copyright (C) 2006 Sebastian Trueg <strueg@mandriva.com>
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

#include "SopranoModelTest.h"
#include <soprano/soprano.h>

#include <QtTest/QTest>
#include <QtCore/QList>
#include <QtCore/QDebug>
#include <QtCore/QFile>
#include <QtCore/QTextStream>


// FIXME: Use the QTest framework to create data tables

using namespace Soprano;

SopranoModelTest::SopranoModelTest()
    : m_model( 0 )
{
}

void SopranoModelTest::cleanup()
{
    delete m_st1;
    delete m_st2;
    delete m_st3;
    delete m_st4;
    delete m_model;
}

void SopranoModelTest::init()
{
    m_model = createModel( "testmodel" );
    QVERIFY( m_model != 0 );

    Node subject1( QUrl("http://soprano.sf.net#init:test1") );
    Node subject2( QUrl("http://soprano.sf.net#init:test2") );

    Node predicate1( QUrl( "http://soprano.sf.net#predicate1" ) );
    Node predicate2( QUrl( "http://soprano.sf.net#predicate2" ) );

    Node object1( "Literal value1" );
    Node object2( "Literal value2" );

    m_st1 = new Statement(subject1, predicate1, object1);
    m_st2 = new Statement(subject2, predicate1, object1);
    m_st3 = new Statement(subject1, predicate2, object2);
    m_st4 = new Statement(subject2, predicate2, object2);

    m_model->addStatement( *m_st1 );
    m_model->addStatement( *m_st2 );
    m_model->addStatement( *m_st3 );
    m_model->addStatement( *m_st4 );
}

void SopranoModelTest::testAddModel()
{
    Node subject1( QUrl("http://soprano.sf.net#add:model") );

    Node predicate1( QUrl( "http://soprano.sf.net#predicate1" ) );
    Node predicate2( QUrl( "http://soprano.sf.net#predicate2" ) );
    Node predicate3( QUrl( "http://soprano.sf.net#predicate3" ) );

    Node object1( "Literal value1" );

    Statement st1(subject1, predicate1, object1);
    Statement st2(subject1, predicate2, object1);
    Statement st3(subject1, predicate3, object1);

    Model *memory = createModel( "memory" );
    QVERIFY( memory );

    memory->addStatement( st1 );
    memory->addStatement( st2 );

    m_model->addModel( *memory );

    QVERIFY( m_model->containsStatements( st1 ) );
    QVERIFY( m_model->containsStatements( st2 ) );
    QVERIFY( !m_model->containsStatements( st3 ) );

    // partial statement match
    Statement stPartial1( subject1, Node(), object1 );
    Statement stPartial2( subject1, Node(), Node() );
    Statement stPartial3;
    Statement stPartial4( subject1, Node(), QUrl( "http://soprao.sf.net#notInTheStore" ) );

    QVERIFY( m_model->containsStatements( stPartial1 ) );
    QVERIFY( m_model->containsStatements( stPartial2 ) );
    QVERIFY( m_model->containsStatements( stPartial3 ) );
    QVERIFY( !m_model->containsStatements( stPartial4 ) );

    delete memory;
}

void SopranoModelTest::testAddListOfStatement()
{
    Node subject1( QUrl("http://soprano.sf.net#add:model") );

    Node predicate1( QUrl( "http://soprano.sf.net#predicate1" ) );
    Node predicate2( QUrl( "http://soprano.sf.net#predicate2" ) );
    Node predicate3( QUrl( "http://soprano.sf.net#predicate3" ) );

    Node object1( "Literal value1" );

    Statement st1(subject1, predicate1, object1);
    Statement st2(subject1, predicate2, object1);
    Statement st3(subject1, predicate3, object1);

    QList<Statement> statements;
    statements.append( st1 );
    statements.append( st2 );
    statements.append( st3 );

    m_model->addStatements( statements );

    QVERIFY( m_model->containsStatements( st1 ) );
    QVERIFY( m_model->containsStatements( st2 ) );
    QVERIFY( m_model->containsStatements( st3 ) );
}

void SopranoModelTest::testAddStatementIterator()
{
    Node subject1( QUrl("http://soprano.sf.net#add:model") );

    Node predicate1( QUrl( "http://soprano.sf.net#predicate1" ) );
    Node predicate2( QUrl( "http://soprano.sf.net#predicate2" ) );
    Node predicate3( QUrl( "http://soprano.sf.net#predicate3" ) );

    Node object1( "Literal value1" );

    Statement st1(subject1, predicate1, object1);
    Statement st2(subject1, predicate2, object1);
    Statement st3(subject1, predicate3, object1);

    Model *memory = createModel( "memory" );
    QVERIFY( memory );

    memory->addStatement( st1 );
    memory->addStatement( st2 );

    m_model->addStatements( memory->listStatements() );

    QVERIFY( m_model->containsStatements( st1 ) );
    QVERIFY( m_model->containsStatements( st2 ) );
    QVERIFY( !m_model->containsStatements( st3 ) );

    delete memory;
}

void SopranoModelTest::testAddStatements()
{
    Node subject1( QUrl("http://soprano.sf.net#soprano:test1") );
    Node subject2( QUrl("http://soprano.sf.net#soprano:test2") );

    Node predicate1( QUrl( "http://soprano.sf.net#predicate1" ) );
    Node predicate2( QUrl( "http://soprano.sf.net#predicate2" ) );

    Node object1( "Literal value1" );
    Node object2( "Literal value2" );

    Statement st1(subject1, predicate1, object1);
    Statement st2(subject2, predicate1, object1);
    Statement st3(subject1, predicate2, object2);
    Statement st4(subject2, predicate2, object2);

    QVERIFY( m_model->addStatement( st1 ) == Soprano::ERROR_NONE );
    QVERIFY( m_model->addStatement( st2 ) == Soprano::ERROR_NONE );
    QVERIFY( m_model->addStatement( st3 ) == Soprano::ERROR_NONE );
    QVERIFY( m_model->addStatement( st4 ) == Soprano::ERROR_NONE );
}

void SopranoModelTest::testListStatements()
{
    QList<Statement> statements;
    Node resource_1( QUrl("http://soprano.sf.net#list:resource1") );
    Node resource_2( QUrl("http://soprano.sf.net#list:resource2") );
    Node resource_3( QUrl("http://soprano.sf.net#list:resource3") );

    for (int i=0; i<50; i++)
    {
        QString property = "predicate" + QString::number(i);
        QString literal = "Literal value" + QString::number(i);

        Node predicate( QUrl( "http://soprano.sf.net#" + property) );
        Node object = LiteralValue( literal );

        Statement st(resource_1, predicate, object);
        statements.append( st );
    }

    for (int i=0; i<50; i++)
    {
        QString property = "predicate" + QString::number(i + 50);
        QString literal = "Literal value" + QString::number(i + 50);

        Node predicate( QUrl( "http://soprano.sf.net#" + property) );
        Node object = LiteralValue( literal );

        Statement st(resource_2, predicate, object);
        statements.append( st );
    }

    for (int i=0; i<20; i++)
    {
        QString property = "predicate" + QString::number(i + 100);
        QString literal = "Literal value" + QString::number(i + 100);

        Node predicate( QUrl( "http://soprano.sf.net#" + property) );
        Node object = LiteralValue( literal );

        Statement st(resource_3, predicate, object);
        statements.append( st );
    }

    m_model->addStatements( statements );

    /* Resource 1 */

    StatementIterator it1 = m_model->listStatements( Statement( resource_1, Node(), Node() ) );

    QFile f( "/tmp/testdump" );
    f.open( QIODevice::WriteOnly );
    QTextStream fs( &f );

    int cnt = 0;
    while( it1.next() ) {
        ++cnt;
        Statement st = *it1;

        if ( st.subject() != resource_1 ) {
            qDebug() << st.subject() << "vs." << resource_1;
        }
        QCOMPARE( st.subject(), resource_1 );

        fs << st << endl;
    }

    QCOMPARE( cnt, 50 );

    /* Resource 2 */

    StatementIterator it2 = m_model->listStatements( Statement( resource_2, Node(), Node() ) );

    cnt = 0;
    while( it2.next() ) {
        ++cnt;
        Statement st = *it2;

        QCOMPARE( st.subject(), resource_2 );
    }

    QCOMPARE( cnt, 50 );

    /* Resource 3 */

    StatementIterator it3 = m_model->listStatements( Statement( resource_3, Node(), Node() ) );

    cnt = 0;
    while( it3.next() ) {
        ++cnt;
        Statement st = *it3;

        QCOMPARE( st.subject(), resource_3 );
    }

    QCOMPARE( cnt, 20 );

    /* All */

    StatementIterator it4 = m_model->listStatements();

    cnt = 0;
    while( it4.next() ) {
        ++cnt;
        Statement st = *it4;

        QVERIFY( statements.indexOf( st ) != -1 || st == *m_st1 || st == *m_st2 || st == *m_st3 || st == *m_st4 );
    }

    QCOMPARE( cnt, 124 );
}

void SopranoModelTest::testListStatementsWithContext()
{
    // we do not want the normal test statements
    m_model->removeAllStatements();

    QList<Statement> statements;
    Node context1( QUrl("http://soprano.sf.net#list:resource1") );
    Node context2( QUrl("http://soprano.sf.net#list:resource2") );
    Node context3( QUrl("http://soprano.sf.net#list:resource3") );

    for (int i=0; i<10; i++)
    {
        QUrl subject = "http://soprano.sf.net#subject" + QString::number(i);
        QUrl predicate = "http://soprano.sf.net#predicate" + QString::number(i);
        LiteralValue object = "Literal value" + QString::number(i);

        statements.append( Statement( subject, predicate, object, context1 ) );
        statements.append( Statement( subject, predicate, object, context2 ) );
        statements.append( Statement( subject, predicate, object, context3 ) );
    }

    QVERIFY( m_model->addStatements( statements ) == ERROR_NONE );

    // list all of them
    StatementIterator it = m_model->listStatements( Statement() );
    int cnt = 0;
    while( it.next() ) {
        ++cnt;
        Statement st = *it;
        QVERIFY( st.context().isValid() );
    }

    QCOMPARE( cnt, 30 );

    // with context as wildcard
    it = m_model->listStatements( Statement( Node(), Node(), Node(), context1 ) );
    cnt = 0;
    while( it.next() ) {
        ++cnt;
        Statement st = *it;
        QCOMPARE( st.context(), context1 );
    }

    QCOMPARE( cnt, 10 );


    // and the full context
    it = m_model->listStatementsInContext( context2 );
    cnt = 0;
    while( it.next() ) {
        ++cnt;
        Statement st = *it;
        QCOMPARE( st.context(), context2 );
    }

    QCOMPARE( cnt, 10 );
}

void SopranoModelTest::testRemoveStatement()
{
    Node subject( QUrl("http://soprano.sf.net#remove:3") );
    Node predicate( QUrl( "http://soprano.sf.net#predicate" ) );
    Node object( QUrl("http://soprano.sf.net#soprano:2") );

    Statement st(subject, predicate, object);
    m_model->addStatement( st );

    QVERIFY( m_model->containsStatements(st) );

    m_model->removeStatements( st );

    QVERIFY( !m_model->containsStatements(st) );
}

void SopranoModelTest::testRemoveAllStatement()
{
    m_model->removeStatements( Statement( m_st1->subject(), Node(), Node() ) );

    QVERIFY( !m_model->containsStatements( *m_st1 ) );
    QVERIFY( m_model->containsStatements( *m_st2 ) );
    QVERIFY( !m_model->containsStatements( *m_st3 ) );
    QVERIFY( m_model->containsStatements( *m_st4 ) );

    m_model->removeStatements( Statement( Node(), m_st3->predicate(), Node() ) );

    QVERIFY( !m_model->containsStatements( *m_st1 ) );
    QVERIFY( m_model->containsStatements( *m_st2 ) );
    QVERIFY( !m_model->containsStatements( *m_st3 ) );
    QVERIFY( !m_model->containsStatements( *m_st4 ) );

    m_model->removeStatements( Statement( Node(), Node(), m_st2->object() ) );

    QVERIFY( !m_model->containsStatements( *m_st1 ) );
    QVERIFY( !m_model->containsStatements( *m_st2 ) );
    QVERIFY( !m_model->containsStatements( *m_st3 ) );
    QVERIFY( !m_model->containsStatements( *m_st4 ) );
}

void SopranoModelTest::testGraphQuery()
{
    QueryLegacy query("CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o . }", QueryLegacy::SPARQL);

    QueryResultIterator rs = m_model->executeQuery( query );
    QVERIFY( rs.isGraph() );
    QVERIFY( !rs.isBinding() );
    QVERIFY( !rs.isBool() );

    int cnt = 0;
    while ( rs.next() ) {
        ++cnt;
        Statement st = rs.currentStatement();
    }
    QCOMPARE ( cnt, 4 );
}

void SopranoModelTest::testBooleanQuery()
{
    QueryLegacy query("ASK where {?a ?b ?c}", QueryLegacy::SPARQL);

    QueryResultIterator res = m_model->executeQuery( query );
    QVERIFY( !res.next() );

    QVERIFY( !res.isGraph() );
    QVERIFY( !res.isBinding() );
    QVERIFY( res.isBool() );

    QVERIFY( res.boolValue() );

    QVERIFY( !res.next() );
}

void SopranoModelTest::testQuery()
{
    /* SPARQL */
    QueryLegacy sparql("select ?b ?c where {?a ?b ?c .}", QueryLegacy::SPARQL);

    QueryResultIterator rs1 = m_model->executeQuery( sparql );

    int cnt = 0;
    while ( rs1.next() )
    {
        QVERIFY( !rs1.isGraph() );
        QVERIFY( rs1.isBinding() );
        QVERIFY( !rs1.isBool() );

        ++cnt;
    }

    QVERIFY( cnt == 4 );

    // test bindings
    rs1 = m_model->executeQuery( sparql );
    qDebug() << rs1.bindingNames();
    while ( rs1.next() ) {
        QCOMPARE( rs1.bindingCount(), 2 );
        QCOMPARE( rs1.binding( 0 ), rs1.binding( "b" ) );
        QCOMPARE( rs1.binding( 1 ), rs1.binding( "c" ) );
        QCOMPARE( rs1.bindingNames().count(), 2 );
        QCOMPARE( rs1.bindingNames()[0], QString( "b" ) );
        QCOMPARE( rs1.bindingNames()[1], QString( "c" ) );
    }

    /* RDQL */

    QueryLegacy rdql("select ?b ?c where (<http://soprano.sf.net#init:test1>, ?b, ?c)", QueryLegacy::RDQL);

    QueryResultIterator rs2 = m_model->executeQuery( rdql );

    int cnt2 = 0;
    while ( rs2.next() )
    {
        QVERIFY( !rs2.isGraph() );
        QVERIFY( rs2.isBinding() );
        QVERIFY( !rs2.isBool() );

        ++cnt2;
    }

    QVERIFY( cnt2 == 2 );
}

void SopranoModelTest::testCloseStatementIteratorOnModelDelete()
{
    Node subject1( QUrl("http://soprano.sf.net#add:model") );

    Node predicate1( QUrl( "http://soprano.sf.net#predicate1" ) );
    Node predicate2( QUrl( "http://soprano.sf.net#predicate2" ) );
    Node predicate3( QUrl( "http://soprano.sf.net#predicate3" ) );

    Node object1( "Literal value1" );

    Statement st1(subject1, predicate1, object1);
    Statement st2(subject1, predicate2, object1);
    Statement st3(subject1, predicate3, object1);

    Model *model = Soprano::createModel();
    QVERIFY( model );

    model->addStatement( st1 );
    model->addStatement( st2 );

    StatementIterator it = model->listStatements();
    QVERIFY( it.next() );

    delete model;

    QVERIFY( !it.current().isValid() );
    QVERIFY( !it.next() );
}

static bool checkSingleIt( StatementIterator it, const Statement& st )
{
    if ( it.next() ) {
        if ( *it != st ) {
            return false;
        }
        else {
            return !it.next();
        }
    }
    else {
        return false;
    }
}

static bool check3It( StatementIterator it, const Statement& s1, const Statement& s2, const Statement& s3 )
{
    int cnt = 0;
    bool haveS1 = false;
    bool haveS2 = false;
    bool haveS3 = false;
    while ( it.next() ) {
        Statement s = *it;
        if ( s == s1 )
            haveS1 = true;
        else if ( s == s2 )
            haveS2 = true;
        else if ( s == s3 )
            haveS3 = true;
        ++cnt;
    }

    return ( cnt == 3 && haveS1 && haveS2 && haveS3 );
}


void SopranoModelTest::testContexts()
{
    Node subject1( QUrl( "http://soprano.sf.net#subject1" ) );
    Node subject2( QUrl( "http://soprano.sf.net#subject2" ) );
    Node subject3( QUrl( "http://soprano.sf.net#subject3" ) );

    Node predicate1( QUrl( "http://soprano.sf.net#predicate1" ) );
    Node predicate2( QUrl( "http://soprano.sf.net#predicate2" ) );
    Node predicate3( QUrl( "http://soprano.sf.net#predicate3" ) );

    Node object1( "literal 1" );
    Node object2( "literal 2" );
    Node object3( "literal 3" );

    Node context1( QUrl( "http://soprano.sf.net/contexts/context1" ) );
    Node context2( QUrl( "http://soprano.sf.net/contexts/context2" ) );
    Node context3( QUrl( "http://soprano.sf.net/contexts/context3" ) );

    Statement s1_c1( subject1, predicate1, object1, context1 );
    Statement s2_c1( subject1, predicate2, object1, context1 );
    Statement s3_c1( subject1, predicate3, object1, context1 );

    Statement s1_c2( subject1, predicate1, object2, context2 );
    Statement s2_c2( subject1, predicate2, object2, context2 );
    Statement s3_c2( subject1, predicate3, object2, context2 );

    Statement s1_c3( subject1, predicate1, object3, context3 );
    Statement s2_c3( subject1, predicate2, object3, context3 );
    Statement s3_c3( subject1, predicate3, object3, context3 );

    Statement s1_c0( subject1, predicate1, object3 );
    Statement s2_c0( subject1, predicate2, object3 );
    Statement s3_c0( subject1, predicate3, object3 );

    // add all the statements (do not add context3 yet, it is used below)
    QVERIFY( m_model->addStatement( s1_c1 ) == ERROR_NONE );
    QVERIFY( m_model->addStatement( s2_c1 ) == ERROR_NONE );
    QVERIFY( m_model->addStatement( s3_c1 ) == ERROR_NONE );

    QVERIFY( m_model->addStatement( s1_c2 ) == ERROR_NONE );
    QVERIFY( m_model->addStatement( s2_c2 ) == ERROR_NONE );
    QVERIFY( m_model->addStatement( s3_c2 ) == ERROR_NONE );

    QVERIFY( m_model->addStatement( s1_c0 ) == ERROR_NONE );
    QVERIFY( m_model->addStatement( s2_c0 ) == ERROR_NONE );
    QVERIFY( m_model->addStatement( s3_c0 ) == ERROR_NONE );

    // check containsStatements plain
    QVERIFY( m_model->containsStatements( s1_c1 ) );
    QVERIFY( m_model->containsStatements( s2_c1 ) );
    QVERIFY( m_model->containsStatements( s3_c1 ) );

    QVERIFY( m_model->containsStatements( s1_c2 ) );
    QVERIFY( m_model->containsStatements( s2_c2 ) );
    QVERIFY( m_model->containsStatements( s3_c2 ) );

    QVERIFY( m_model->containsStatements( s1_c0 ) );
    QVERIFY( m_model->containsStatements( s2_c0 ) );
    QVERIFY( m_model->containsStatements( s3_c0 ) );

    // check containsStatements with wildcard for context
    QVERIFY( m_model->containsStatements( Statement( s1_c1.subject(), s1_c1.predicate(), s1_c1.object() ) ) );
    QVERIFY( m_model->containsStatements( Statement( s2_c1.subject(), s2_c1.predicate(), s2_c1.object() ) ) );
    QVERIFY( m_model->containsStatements( Statement( s3_c1.subject(), s3_c1.predicate(), s3_c1.object() ) ) );

    QVERIFY( m_model->containsStatements( Statement( s1_c2.subject(), s1_c2.predicate(), s1_c2.object() ) ) );
    QVERIFY( m_model->containsStatements( Statement( s2_c2.subject(), s2_c2.predicate(), s2_c2.object() ) ) );
    QVERIFY( m_model->containsStatements( Statement( s3_c2.subject(), s3_c2.predicate(), s3_c2.object() ) ) );

    // check listStatements single
    checkSingleIt( m_model->listStatements( s1_c1 ), s1_c1 );
    checkSingleIt( m_model->listStatements( s2_c1 ), s2_c1 );
    checkSingleIt( m_model->listStatements( s3_c1 ), s3_c1 );

    checkSingleIt( m_model->listStatements( s1_c2 ), s1_c2 );
    checkSingleIt( m_model->listStatements( s2_c2 ), s2_c2 );
    checkSingleIt( m_model->listStatements( s3_c2 ), s3_c2 );

    checkSingleIt( m_model->listStatements( s1_c0 ), s1_c0 );
    checkSingleIt( m_model->listStatements( s2_c0 ), s2_c0 );
    checkSingleIt( m_model->listStatements( s3_c0 ), s3_c0 );

    // check listStatements with wildcard for object (one context)
    checkSingleIt( m_model->listStatements( Statement( s1_c1.subject(), s1_c1.predicate(), Node(), s1_c1.context() ) ), s1_c1 );
    checkSingleIt( m_model->listStatements( Statement( s2_c1.subject(), s2_c1.predicate(), Node(), s2_c1.context() ) ), s2_c1 );
    checkSingleIt( m_model->listStatements( Statement( s3_c1.subject(), s3_c1.predicate(), Node(), s3_c1.context() ) ), s3_c1 );

    checkSingleIt( m_model->listStatements( Statement( s1_c2.subject(), s1_c2.predicate(), Node(), s1_c2.context() ) ), s1_c2 );
    checkSingleIt( m_model->listStatements( Statement( s2_c2.subject(), s2_c2.predicate(), Node(), s2_c2.context() ) ), s2_c2 );
    checkSingleIt( m_model->listStatements( Statement( s3_c2.subject(), s3_c2.predicate(), Node(), s3_c2.context() ) ), s3_c2 );

    // the one without the context should return all three variants, i.e. 3 statements (different contexts)
    check3It( m_model->listStatements( Statement( s1_c0.subject(), s1_c0.predicate(), Node(), s1_c0.context() ) ),
              s1_c1, s1_c2, s1_c0 );
    check3It( m_model->listStatements( Statement( s2_c0.subject(), s2_c0.predicate(), Node(), s2_c0.context() ) ),
              s2_c1, s2_c2, s2_c0 );
    check3It( m_model->listStatements( Statement( s3_c0.subject(), s3_c0.predicate(), Node(), s3_c0.context() ) ),
              s1_c0, s3_c2, s3_c0 );

    // check remove context
    QVERIFY( m_model->removeContext( context1 ) == ERROR_NONE );
    QVERIFY( !m_model->containsStatements( s1_c1 ) );
    QVERIFY( !m_model->containsStatements( s2_c1 ) );
    QVERIFY( !m_model->containsStatements( s3_c1 ) );

    QVERIFY( m_model->containsStatements( s1_c2 ) );
    QVERIFY( m_model->containsStatements( s2_c2 ) );
    QVERIFY( m_model->containsStatements( s3_c2 ) );

    QVERIFY( m_model->containsStatements( s1_c0 ) );
    QVERIFY( m_model->containsStatements( s2_c0 ) );
    QVERIFY( m_model->containsStatements( s3_c0 ) );

    // check remove with context
    QVERIFY( m_model->removeStatements( s1_c2 ) == ERROR_NONE );
    QVERIFY( !m_model->containsStatements( s1_c2 ) );
    QVERIFY( m_model->containsStatements( s2_c2 ) );
    QVERIFY( m_model->containsStatements( s3_c2 ) );

    QVERIFY( m_model->containsStatements( s1_c0 ) );
    QVERIFY( m_model->containsStatements( s2_c0 ) );
    QVERIFY( m_model->containsStatements( s3_c0 ) );

    // check remove without context
    QVERIFY( m_model->addStatement( s1_c3 ) == ERROR_NONE );
    QVERIFY( m_model->addStatement( s2_c3 ) == ERROR_NONE );
    QVERIFY( m_model->addStatement( s3_c3 ) == ERROR_NONE );

    QVERIFY( m_model->containsStatements( s1_c3 ) );
    QVERIFY( m_model->containsStatements( s2_c3 ) );
    QVERIFY( m_model->containsStatements( s3_c3 ) );

    QVERIFY( m_model->removeStatements( s1_c0 ) == ERROR_NONE );

    QVERIFY( !m_model->containsStatements( s1_c0 ) );
    QVERIFY( !m_model->containsStatements( s1_c3 ) );
}


void SopranoModelTest::testListContexts()
{
    // add some statements with contexts

    QList<Statement> statements;
    Node context1( QUrl("http://soprano.sf.net#list:resource1") );
    Node context2( QUrl("http://soprano.sf.net#list:resource2") );
    Node context3( QUrl("http://soprano.sf.net#list:resource3") );

    for (int i=0; i<10; i++)
    {
        QUrl subject = "http://soprano.sf.net#subject" + QString::number(i);
        QUrl predicate = "http://soprano.sf.net#predicate" + QString::number(i);
        LiteralValue object = "Literal value" + QString::number(i);

        statements.append( Statement( subject, predicate, object, context1 ) );
        statements.append( Statement( subject, predicate, object, context2 ) );
        statements.append( Statement( subject, predicate, object, context3 ) );
    }

    QVERIFY( m_model->addStatements( statements ) == ERROR_NONE );

    NodeIterator it = m_model->listContexts();

    QList<Node> allContexts = it.allNodes();
    QCOMPARE( 3, allContexts.count() );

    QVERIFY( allContexts.contains( context1 ) );
    QVERIFY( allContexts.contains( context2 ) );
    QVERIFY( allContexts.contains( context3 ) );
}

#include "SopranoModelTest.moc"
