/*
 *
 * $Id: sourceheader 511311 2006-02-19 14:51:05Z trueg $
 *
 * This file is part of the Soprano project.
 * Copyright (C) 2007 Sebastian Trueg <trueg@kde.org>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * See the file "COPYING" for the exact licensing terms.
 */

#include <QtCore/QCoreApplication>
#include <QtCore/QTime>
#include <QtCore/QTextStream>
#include <QtCore/QDebug>
#include <QtCore/QList>
#include <QtCore/QDir>
#include <QtCore/QRegExp>

#include "../soprano/statementiterator.h"
#include "../soprano/queryresultiterator.h"
#include "../soprano/nodeiterator.h"
#include "../soprano/version.h"
#include "../soprano/pluginmanager.h"
#include "../soprano/parser.h"
#include "../soprano/node.h"
#include "../soprano/model.h"
#include "../soprano/global.h"
#include "../soprano/vocabulary/rdfs.h"
#include "../soprano/vocabulary/rdf.h"
#include "../soprano/vocabulary/owl.h"


using namespace Soprano;

static const char* LGPL_HEADER = "/*\n"
                                 " * This file has been generated by the onto2vocabularyclass tool\n"
                                 " * copyright (C) 2007-2008 Sebastian Trueg <trueg@kde.org>\n"
                                 " *\n"
                                 " * This library is free software; you can redistribute it and/or\n"
                                 " * modify it under the terms of the GNU Library General Public\n"
                                 " * License as published by the Free Software Foundation; either\n"
                                 " * version 2 of the License, or (at your option) any later version.\n"
                                 " *\n"
                                 " * This library is distributed in the hope that it will be useful,\n"
                                 " * but WITHOUT ANY WARRANTY; without even the implied warranty of\n"
                                 " * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU\n"
                                 " * Library General Public License for more details.\n"
                                 " *\n"
                                 " * You should have received a copy of the GNU Library General Public License\n"
                                 " * along with this library; see the file COPYING.LIB.  If not, write to\n"
                                 " * the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,\n"
                                 " * Boston, MA 02110-1301, USA.\n"
                                 " */\n";


#define VERSION "0.2"

int version()
{
    QTextStream s( stderr );
    s << "onto2vocabularyclass " << VERSION << " (using Soprano " << Soprano::versionString() << ")" << endl;
    s << "   Copyright (C) 2007-2008 Sebastian Trueg <trueg@kde.org>" << endl;
    s << "   This program is free software; you can redistribute it and/or modify" << endl
      << "   it under the terms of the GNU General Public License as published by" << endl
      << "   the Free Software Foundation; either version 2 of the License, or" << endl
      << "   (at your option) any later version." << endl;

    return 0;
}


int usage( const QString& error = QString() )
{
    version();

    QTextStream s( stderr );
    s << endl;
    s << "Usage:" << endl
      << "   onto2vocabularyclass --name <name> --encoding <encoding> [--namespace <ns>] [--export-module <module>] [--no-visibility-export] <ontologyfile>" << endl;

    if ( !error.isEmpty() ) {
        s << endl << error << endl;
        return 0;
    }
    else {
        return 1;
    }
}


QString createIndent( int indent )
{
    QString s;
    for ( int i = 0; i < indent; ++i ) {
        s += "    ";
    }
    return s;
}


QString writeComment( const QString& comment, int indent )
{
    static const int maxLine = 50;

    QString s;

    if( !comment.isEmpty() ) {
        s += createIndent( indent );
        s += "/**\n";

        QStringList paragraphs = comment.split( '\n', QString::KeepEmptyParts );
        Q_FOREACH( const QString &paragraph, paragraphs ) {
            s += createIndent( indent ) + " * ";
            QStringList words = paragraph.split( QRegExp("\\s"), QString::SkipEmptyParts );
            int cnt = 0;
            for( int i = 0; i < words.count(); ++i ) {
                if( cnt >= maxLine ) {
                    s += '\n'
                         + createIndent( indent ) + " * ";
                    cnt = 0;
                }

                s += words[i] + ' ';
                cnt += words[i].length();
            }
            s += '\n';
        }


        s += createIndent( indent ) + " */";
    }

    return s;
}


QString normalizeName( const QString& name )
{
    // TODO: add more invalid characters here
    return QString( name ).replace( '-', QString() );
}


int main( int argc, char *argv[] )
{
    QCoreApplication app( argc, argv );

    QStringList args = app.arguments();
    QString fileName;
    QString className;
    QString namespaceName;
    QString encoding;
    QString exportModule = "soprano";
    bool visibilityExport = true;
    int i = 1;
    while ( i < args.count() ) {
        if ( args[i] == "--encoding" ) {
            ++i;
            if ( i < args.count() ) {
                encoding = args[i];
            }
            else {
                return usage();
            }
        }
        else if ( args[i] == "--name" ) {
            ++i;
            if ( i < args.count() ) {
                className = args[i];
            }
            else {
                return usage();
            }
        }
        else if ( args[i] == "--namespace" ) {
            ++i;
            if ( i < args.count() ) {
                namespaceName = args[i];
            }
            else {
                return usage();
            }
        }
        else if ( args[i] == "--export-module" ) {
            ++i;
            if ( i < args.count() ) {
                exportModule = args[i];
            }
            else {
                return usage();
            }
        }
        else if ( args[i] == "--no-visibility-export" ) {
            visibilityExport = false;
        }
        else if ( i == args.count()-1 ) {
            fileName = args[i];
        }
        else {
            QTextStream s( stderr );
            s << "Unknown argument:" << args[i] << endl << endl;
            return usage();
        }
        ++i;
    }

    if ( fileName.isEmpty() ) {
        return usage();
    }
    if ( encoding.isEmpty() ) {
        return usage();
    }

    if ( !QFile::exists( fileName ) ) {
        QTextStream s( stderr );
        s << "Could not find file" << fileName << endl;
        return 1;
    }

    const Parser* parser = PluginManager::instance()->discoverParserForSerialization( mimeTypeToSerialization( encoding ), encoding );
    if ( !parser ) {
        QTextStream s( stderr );
        s << "Could not find parser plugin for encoding " << encoding << endl;
        return 1;
    }

    StatementIterator it = parser->parseFile( fileName, QUrl( "http://dummybaseuri.org" ), mimeTypeToSerialization( encoding ), encoding );
    if ( parser->lastError() ) {
        QTextStream s( stderr );
        s << "Failed to parse file" << fileName << "(" << parser->lastError() << ")" << endl;
        return 1;
    }

    // try using the sesame2 backend for graph queries
    Soprano::setUsedBackend( Soprano::discoverBackendByName( "sesame2" ) );
    Model* model = Soprano::createModel( BackendSettings() << BackendSetting( BackendOptionStorageMemory ) );
    if ( !model ) {
        QTextStream s( stderr );
        s << "Failed to create memory model. No Soprano backend installed?" << endl;
        return 1;
    }
    while ( it.next() ) {
        model->addStatement( *it );
    }

    QFile headerFile( className.toLower() + ".h" );
    QFile sourceFile( className.toLower() + ".cpp" );

    if ( !headerFile.open( QIODevice::WriteOnly ) ) {
        QTextStream s( stderr );
        s << "Failed to open file" << headerFile.fileName() << endl;
        return 1;
    }

    if ( !sourceFile.open( QIODevice::WriteOnly ) ) {
        QTextStream s( stderr );
        s << "Failed to open file" << sourceFile.fileName() << endl;
        return 1;
    }

    QTextStream headerStream( &headerFile );
    QTextStream sourceStream( &sourceFile );

    // select all relevant resource, try to be intelligent about it...
    QList<Node> allResources = model->executeQuery( QString( "select distinct ?r where { "
                                                             "graph ?g { ?r a ?rt . } . "
                                                             "OPTIONAL { ?g a ?gt . "
                                                             "FILTER(?gt = <http://www.semanticdesktop.org/ontologies/2007/08/15/nrl#GraphMetadata>) . } . "
                                                             "FILTER(!BOUND(?gt)) . "
                                                             "}" ),
                                                    Query::QueryLanguageSparql ).iterateBindings( "r" ).allNodes();

    // stupid sparql has no way of saying: "empty graph" so we need to do that manually for
    // the case where no graph is defined
    if ( allResources.isEmpty() ) {
        allResources = model->executeQuery( QString( "select distinct ?r where { "
                                                     "?r a ?t . }" ),
                                            Query::QueryLanguageSparql ).iterateBindings( "r" ).allNodes();
    }

    // create entries
    // ----------------------------------------------------
    QMap<QString, QPair<QString, QString> > normalizedResources;
    QStringList done;
    foreach( const Node &resource, allResources ) {
        QString uri = resource.uri().toString();
        if ( !normalizedResources.contains( uri ) ) {
            QString name = resource.uri().fragment();
            if ( name.isEmpty() && !uri.contains( '#' ) ) {
                name = resource.uri().path().section( "/", -1 );
            }

            if ( !name.isEmpty() && !done.contains( name ) ) {
                normalizedResources.insert( uri, qMakePair( name, QString() ) );
                done += name;
            }
        }
    }

    // extract comments
    foreach( const Node &resource, allResources ) {
        StatementIterator it = model->listStatements( resource, Soprano::Vocabulary::RDFS::comment(), Node() );
        if ( it.next() ) {
            if ( normalizedResources.contains( resource.toString() ) ) {
                normalizedResources[resource.toString()].second = it.current().object().literal().toString();
            }
        }
    }

    if ( normalizedResources.isEmpty() ) {
        QTextStream s( stderr );
        s << "Nothing found to export." << endl;
        return 1;
    }

    // We simplify and take it as granted that all resources have the same NS
    QString ontoNamespace;
    QUrl namespaceUri( normalizedResources.constBegin().key() );
    if ( namespaceUri.hasFragment() ) {
        namespaceUri.setFragment( QString() );
        ontoNamespace = namespaceUri.toString() + '#';
    }
    else {
        ontoNamespace = namespaceUri.toString().section( "/", 0, -2 ) + '/';
    }
    qDebug() << "namespace: " << ontoNamespace;
    // ----------------------------------------------------


    // write the header
    // ----------------------------------------------------
    headerStream << LGPL_HEADER << endl;

    headerStream << "#ifndef _SOPRANO_" << className.toUpper() << "_H_" << endl
                 << "#define _SOPRANO_" << className.toUpper() << "_H_" << endl << endl;

    headerStream << "#include <QtCore/QUrl>" << endl;

    if ( visibilityExport )
        headerStream << QString( "#include \"%1_export.h\"").arg(exportModule.toLower()) << endl;
    headerStream << endl;

    int indent = 0;
    if ( !namespaceName.isEmpty() ) {
        QStringList tokens = namespaceName.split( "::" );
        for ( int i = 0; i < tokens.count(); ++i ) {
            headerStream << createIndent( indent++ ) << "namespace " << tokens[i] << " {" << endl;
        }
    }

    // the class name
    headerStream << createIndent( indent++ ) << "namespace " << className << " {" << endl;

    // the onto namespace
    headerStream << createIndent( indent ) << "/**" << endl
                 << createIndent( indent ) << " * " << ontoNamespace << endl
                 << createIndent( indent ) << " */" << endl;

    headerStream << createIndent( indent );
    if ( visibilityExport )
        headerStream << QString( "%1_EXPORT " ).arg(exportModule.toUpper());
    headerStream << "QUrl " << className.toLower() << "Namespace();" << endl << endl;

    for( QMap<QString, QPair<QString, QString> >::const_iterator it = normalizedResources.constBegin();
         it != normalizedResources.constEnd(); ++it ) {
        QString uri = it.key();
        QString name = normalizeName( it.value().first );
        QString comment = it.value().second;

        if ( comment.isEmpty() ) {
            headerStream << writeComment( uri, indent ) << endl;
        }
        else {
            headerStream << writeComment( uri + "\n\n" + comment, indent ) << endl;
        }
        headerStream << createIndent( indent );
        if ( visibilityExport )
            headerStream << QString( "%1_EXPORT " ).arg(exportModule.toUpper());
        headerStream << "QUrl " << name << "();" << endl;

        ++it;
        if ( it != normalizedResources.constEnd() ) {
            headerStream << endl;
        }
        --it;
    }

    // close the namespaces
    while ( indent > 0 ) {
        headerStream << createIndent( --indent ) << "}" << endl;
    }

    headerStream << endl << "#endif" << endl;
    // ----------------------------------------------------


    // write source
    // ----------------------------------------------------
    sourceStream << LGPL_HEADER << endl;
    sourceStream << "#include \"" << headerFile.fileName() << "\"" << endl << endl;

    QString privateClassName = className[0].toUpper() + className.mid( 1 ).toLower() + "Private";
    QString singletonName = "s_" + className.toLower();

    sourceStream << "class " << privateClassName << endl
                 << "{" << endl
                 << "public:" << endl
                 << createIndent( 1 ) << privateClassName << "()" << endl
                 << createIndent( 2 ) << ": ";

    sourceStream << className.toLower() << "_namespace( QUrl::fromEncoded( \"" << ontoNamespace << "\", QUrl::StrictMode ) )," << endl;

    for( QMap<QString, QPair<QString, QString> >::const_iterator it = normalizedResources.constBegin();
         it != normalizedResources.constEnd(); ++it ) {
        QString uri = it.key();
        QString name = normalizeName( it.value().first );

        sourceStream << createIndent( 2 ) << "  " << className.toLower() << "_" << name << "( QUrl::fromEncoded( \"" << uri << "\", QUrl::StrictMode ) )";

        ++it;
        if ( it != normalizedResources.constEnd() ) {
            sourceStream << "," << endl;
        }
        --it;
    }

    sourceStream << " {" << endl
                 << createIndent( 1 ) << "}" << endl << endl;

    sourceStream << createIndent( 1 ) << "QUrl " << className.toLower() << "_namespace;" << endl;

    for( QMap<QString, QPair<QString, QString> >::const_iterator it = normalizedResources.constBegin();
         it != normalizedResources.constEnd(); ++it ) {
        QString name = it.value().first;
        sourceStream << createIndent( 1 ) << "QUrl " << className.toLower() << "_" << name << ";" << endl;
    }
    sourceStream << "};" << endl << endl;

    sourceStream << "Q_GLOBAL_STATIC( " << privateClassName << ", " << singletonName << " )" << endl << endl;

    sourceStream << "QUrl ";
    if ( !namespaceName.isEmpty() ) {
        sourceStream << namespaceName << "::";
    }
    sourceStream << className << "::" << className.toLower() << "Namespace()" << endl
                 << "{" << endl
                 << createIndent( 1 ) << "return " << singletonName << "()->" << className.toLower() << "_namespace;" << endl
                 << "}" << endl << endl;

    for( QMap<QString, QPair<QString, QString> >::const_iterator it = normalizedResources.constBegin();
         it != normalizedResources.constEnd(); ++it ) {
        QString name = it.value().first;

        sourceStream << "QUrl ";

        if ( !namespaceName.isEmpty() ) {
            sourceStream << namespaceName << "::";
        }

        sourceStream << className << "::" << name << "()" << endl
                     << "{" << endl
                     << createIndent( 1 ) << "return " << singletonName << "()->" << className.toLower() << "_" << name << ";" << endl
                     << "}" << endl;

        ++it;
        if ( it != normalizedResources.constEnd() ) {
            sourceStream << endl;
        }
        --it;
    }

    // ----------------------------------------------------


    return 0;
}
