/*
 * This file has been generated by the onto2vocabularyclass tool
 * copyright (C) 2007-2008 Sebastian Trueg <trueg@kde.org>
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

#include "rdf.h"
#include <QThreadStorage>

class RdfPrivate
{
public:
    RdfPrivate()
        : rdf_namespace( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#", QUrl::StrictMode ) ),
          rdf_Alt( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#Alt", QUrl::StrictMode ) ),
          rdf_Bag( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#Bag", QUrl::StrictMode ) ),
          rdf_List( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#List", QUrl::StrictMode ) ),
          rdf_Property( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property", QUrl::StrictMode ) ),
          rdf_Seq( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#Seq", QUrl::StrictMode ) ),
          rdf_Statement( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#Statement", QUrl::StrictMode ) ),
          rdf_XMLLiteral( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral", QUrl::StrictMode ) ),
          rdf_first( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#first", QUrl::StrictMode ) ),
          rdf_nil( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil", QUrl::StrictMode ) ),
          rdf_object( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#object", QUrl::StrictMode ) ),
          rdf_predicate( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#predicate", QUrl::StrictMode ) ),
          rdf_rest( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest", QUrl::StrictMode ) ),
          rdf_subject( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#subject", QUrl::StrictMode ) ),
          rdf_type( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#type", QUrl::StrictMode ) ),
          rdf_value( QUrl::fromEncoded( "http://www.w3.org/1999/02/22-rdf-syntax-ns#value", QUrl::StrictMode ) ),
          rdf_metadataPredicate( QUrl::fromEncoded( "http://aldebaran.org/learning#metadata", QUrl::StrictMode ) ),
          rdf_isDisabled( QUrl::fromEncoded( "http://aldebaran.org/learning#isDisabled", QUrl::StrictMode ) )
    {
    }

    QUrl rdf_namespace;
    QUrl rdf_Alt;
    QUrl rdf_Bag;
    QUrl rdf_List;
    QUrl rdf_Property;
    QUrl rdf_Seq;
    QUrl rdf_Statement;
    QUrl rdf_XMLLiteral;
    QUrl rdf_first;
    QUrl rdf_nil;
    QUrl rdf_object;
    QUrl rdf_predicate;
    QUrl rdf_rest;
    QUrl rdf_subject;
    QUrl rdf_type;
    QUrl rdf_value;
    QUrl rdf_metadataPredicate;
    QUrl rdf_isDisabled;
};

QThreadStorage<RdfPrivate*> qts_rdf;
RdfPrivate* s_rdf() {
    if( !qts_rdf.hasLocalData() )
        qts_rdf.setLocalData( new RdfPrivate );
    return qts_rdf.localData();
}

QUrl Soprano::Vocabulary::RDF::rdfNamespace()
{
    return s_rdf()->rdf_namespace;
}

QUrl Soprano::Vocabulary::RDF::Alt()
{
    return s_rdf()->rdf_Alt;
}

QUrl Soprano::Vocabulary::RDF::Bag()
{
    return s_rdf()->rdf_Bag;
}

QUrl Soprano::Vocabulary::RDF::List()
{
    return s_rdf()->rdf_List;
}

QUrl Soprano::Vocabulary::RDF::Property()
{
    return s_rdf()->rdf_Property;
}

QUrl Soprano::Vocabulary::RDF::Seq()
{
    return s_rdf()->rdf_Seq;
}

QUrl Soprano::Vocabulary::RDF::Statement()
{
    return s_rdf()->rdf_Statement;
}

QUrl Soprano::Vocabulary::RDF::XMLLiteral()
{
    return s_rdf()->rdf_XMLLiteral;
}

QUrl Soprano::Vocabulary::RDF::first()
{
    return s_rdf()->rdf_first;
}

QUrl Soprano::Vocabulary::RDF::nil()
{
    return s_rdf()->rdf_nil;
}

QUrl Soprano::Vocabulary::RDF::object()
{
    return s_rdf()->rdf_object;
}

QUrl Soprano::Vocabulary::RDF::predicate()
{
    return s_rdf()->rdf_predicate;
}

QUrl Soprano::Vocabulary::RDF::rest()
{
    return s_rdf()->rdf_rest;
}

QUrl Soprano::Vocabulary::RDF::subject()
{
    return s_rdf()->rdf_subject;
}

QUrl Soprano::Vocabulary::RDF::type()
{
    return s_rdf()->rdf_type;
}

QUrl Soprano::Vocabulary::RDF::value()
{
    return s_rdf()->rdf_value;
}

QUrl Soprano::Vocabulary::RDF::metadataPredicate()
{
    return s_rdf()->rdf_metadataPredicate;
}

QUrl Soprano::Vocabulary::RDF::isDisabled()
{
    return s_rdf()->rdf_isDisabled;
}

QUrl Soprano::Vocabulary::RDF::createAldebaranRessource(QString ressourceName)
{
  return QUrl("http://aldebaran.org/learning#"+ressourceName);
}

//QString Soprano::Vocabulary::RDF::getMetadataQuery(const QString& subject,
//                                                const QString& predicate,
//                                                const QString& object)
//{
//  return "PREFIX al:<"+Vocabulary::RDF::createAldebaranRessource("").toString()+"> \n"
//      "select ?sourceStatement where {"
//      + "<" + subject + ">" + " al:metadata ?metadata . \n"
//      + "<" + predicate + ">" + " al:metadata ?metadata . \n"
//      + "<" + object + ">" + " al:metadata ?metadata . \n"
//      "?sourceStatement al:isDisabled ?metadata .} ";
//}

