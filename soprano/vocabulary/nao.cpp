/*
 * This file has been generated by the onto2vocabularyclass tool
 * copyright (C) 2007-2011 Sebastian Trueg <trueg@kde.org>
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

#include "nao.h"

class NaoPrivate
{
public:
    NaoPrivate()
        : nao_namespace( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#", QUrl::StrictMode ) ),
          nao_FreeDesktopIcon( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#FreeDesktopIcon", QUrl::StrictMode ) ),
          nao_Party( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#Party", QUrl::StrictMode ) ),
          nao_Symbol( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#Symbol", QUrl::StrictMode ) ),
          nao_Tag( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#Tag", QUrl::StrictMode ) ),
          nao_altLabel( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#altLabel", QUrl::StrictMode ) ),
          nao_altSymbol( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#altSymbol", QUrl::StrictMode ) ),
          nao_annotation( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#annotation", QUrl::StrictMode ) ),
          nao_contributor( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#contributor", QUrl::StrictMode ) ),
          nao_created( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#created", QUrl::StrictMode ) ),
          nao_creator( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#creator", QUrl::StrictMode ) ),
          nao_deprecated( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#deprecated", QUrl::StrictMode ) ),
          nao_description( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#description", QUrl::StrictMode ) ),
          nao_engineeringTool( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#engineeringTool", QUrl::StrictMode ) ),
          nao_hasDefaultNamespace( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#hasDefaultNamespace", QUrl::StrictMode ) ),
          nao_hasDefaultNamespaceAbbreviation( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#hasDefaultNamespaceAbbreviation", QUrl::StrictMode ) ),
          nao_hasSubResource( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#hasSubResource", QUrl::StrictMode ) ),
          nao_hasSuperResource( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#hasSuperResource", QUrl::StrictMode ) ),
          nao_hasSymbol( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#hasSymbol", QUrl::StrictMode ) ),
          nao_hasTag( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#hasTag", QUrl::StrictMode ) ),
          nao_hasTopic( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#hasTopic", QUrl::StrictMode ) ),
          nao_iconName( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#iconName", QUrl::StrictMode ) ),
          nao_identifier( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#identifier", QUrl::StrictMode ) ),
          nao_isDataGraphFor( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#isDataGraphFor", QUrl::StrictMode ) ),
          nao_isRelated( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#isRelated", QUrl::StrictMode ) ),
          nao_isTagFor( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#isTagFor", QUrl::StrictMode ) ),
          nao_isTopicOf( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#isTopicOf", QUrl::StrictMode ) ),
          nao_lastModified( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#lastModified", QUrl::StrictMode ) ),
          nao_modified( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#modified", QUrl::StrictMode ) ),
          nao_numericRating( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#numericRating", QUrl::StrictMode ) ),
          nao_personalIdentifier( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#personalIdentifier", QUrl::StrictMode ) ),
          nao_pluralPrefLabel( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#pluralPrefLabel", QUrl::StrictMode ) ),
          nao_prefLabel( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#prefLabel", QUrl::StrictMode ) ),
          nao_prefSymbol( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#prefSymbol", QUrl::StrictMode ) ),
          nao_rating( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#rating", QUrl::StrictMode ) ),
          nao_score( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#score", QUrl::StrictMode ) ),
          nao_scoreParameter( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#scoreParameter", QUrl::StrictMode ) ),
          nao_serializationLanguage( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#serializationLanguage", QUrl::StrictMode ) ),
          nao_status( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#status", QUrl::StrictMode ) ),
          nao_userVisible( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#userVisible", QUrl::StrictMode ) ),
          nao_version( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#version", QUrl::StrictMode ) ),
          nao_Agent( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#Agent", QUrl::StrictMode ) ),
          nao_maintainedBy( QUrl::fromEncoded( "http://www.semanticdesktop.org/ontologies/2007/08/15/nao#maintainedBy", QUrl::StrictMode ) ) {
    }

    QUrl nao_namespace;
    QUrl nao_FreeDesktopIcon;
    QUrl nao_Party;
    QUrl nao_Symbol;
    QUrl nao_Tag;
    QUrl nao_altLabel;
    QUrl nao_altSymbol;
    QUrl nao_annotation;
    QUrl nao_contributor;
    QUrl nao_created;
    QUrl nao_creator;
    QUrl nao_deprecated;
    QUrl nao_description;
    QUrl nao_engineeringTool;
    QUrl nao_hasDefaultNamespace;
    QUrl nao_hasDefaultNamespaceAbbreviation;
    QUrl nao_hasSubResource;
    QUrl nao_hasSuperResource;
    QUrl nao_hasSymbol;
    QUrl nao_hasTag;
    QUrl nao_hasTopic;
    QUrl nao_iconName;
    QUrl nao_identifier;
    QUrl nao_isDataGraphFor;
    QUrl nao_isRelated;
    QUrl nao_isTagFor;
    QUrl nao_isTopicOf;
    QUrl nao_lastModified;
    QUrl nao_modified;
    QUrl nao_numericRating;
    QUrl nao_personalIdentifier;
    QUrl nao_pluralPrefLabel;
    QUrl nao_prefLabel;
    QUrl nao_prefSymbol;
    QUrl nao_rating;
    QUrl nao_score;
    QUrl nao_scoreParameter;
    QUrl nao_serializationLanguage;
    QUrl nao_status;
    QUrl nao_userVisible;
    QUrl nao_version;
    QUrl nao_Agent;
    QUrl nao_maintainedBy;
};

Q_GLOBAL_STATIC( NaoPrivate, s_nao )

QUrl Soprano::Vocabulary::NAO::naoNamespace()
{
    return s_nao()->nao_namespace;
}

QUrl Soprano::Vocabulary::NAO::FreeDesktopIcon()
{
    return s_nao()->nao_FreeDesktopIcon;
}

QUrl Soprano::Vocabulary::NAO::Party()
{
    return s_nao()->nao_Party;
}

QUrl Soprano::Vocabulary::NAO::Symbol()
{
    return s_nao()->nao_Symbol;
}

QUrl Soprano::Vocabulary::NAO::Tag()
{
    return s_nao()->nao_Tag;
}

QUrl Soprano::Vocabulary::NAO::altLabel()
{
    return s_nao()->nao_altLabel;
}

QUrl Soprano::Vocabulary::NAO::altSymbol()
{
    return s_nao()->nao_altSymbol;
}

QUrl Soprano::Vocabulary::NAO::annotation()
{
    return s_nao()->nao_annotation;
}

QUrl Soprano::Vocabulary::NAO::contributor()
{
    return s_nao()->nao_contributor;
}

QUrl Soprano::Vocabulary::NAO::created()
{
    return s_nao()->nao_created;
}

QUrl Soprano::Vocabulary::NAO::creator()
{
    return s_nao()->nao_creator;
}

QUrl Soprano::Vocabulary::NAO::deprecated()
{
    return s_nao()->nao_deprecated;
}

QUrl Soprano::Vocabulary::NAO::description()
{
    return s_nao()->nao_description;
}

QUrl Soprano::Vocabulary::NAO::engineeringTool()
{
    return s_nao()->nao_engineeringTool;
}

QUrl Soprano::Vocabulary::NAO::hasDefaultNamespace()
{
    return s_nao()->nao_hasDefaultNamespace;
}

QUrl Soprano::Vocabulary::NAO::hasDefaultNamespaceAbbreviation()
{
    return s_nao()->nao_hasDefaultNamespaceAbbreviation;
}

QUrl Soprano::Vocabulary::NAO::hasSubResource()
{
    return s_nao()->nao_hasSubResource;
}

QUrl Soprano::Vocabulary::NAO::hasSuperResource()
{
    return s_nao()->nao_hasSuperResource;
}

QUrl Soprano::Vocabulary::NAO::hasSymbol()
{
    return s_nao()->nao_hasSymbol;
}

QUrl Soprano::Vocabulary::NAO::hasTag()
{
    return s_nao()->nao_hasTag;
}

QUrl Soprano::Vocabulary::NAO::hasTopic()
{
    return s_nao()->nao_hasTopic;
}

QUrl Soprano::Vocabulary::NAO::iconName()
{
    return s_nao()->nao_iconName;
}

QUrl Soprano::Vocabulary::NAO::identifier()
{
    return s_nao()->nao_identifier;
}

QUrl Soprano::Vocabulary::NAO::isDataGraphFor()
{
    return s_nao()->nao_isDataGraphFor;
}

QUrl Soprano::Vocabulary::NAO::isRelated()
{
    return s_nao()->nao_isRelated;
}

QUrl Soprano::Vocabulary::NAO::isTagFor()
{
    return s_nao()->nao_isTagFor;
}

QUrl Soprano::Vocabulary::NAO::isTopicOf()
{
    return s_nao()->nao_isTopicOf;
}

QUrl Soprano::Vocabulary::NAO::lastModified()
{
    return s_nao()->nao_lastModified;
}

QUrl Soprano::Vocabulary::NAO::modified()
{
    return s_nao()->nao_modified;
}

QUrl Soprano::Vocabulary::NAO::numericRating()
{
    return s_nao()->nao_numericRating;
}

QUrl Soprano::Vocabulary::NAO::personalIdentifier()
{
    return s_nao()->nao_personalIdentifier;
}

QUrl Soprano::Vocabulary::NAO::pluralPrefLabel()
{
    return s_nao()->nao_pluralPrefLabel;
}

QUrl Soprano::Vocabulary::NAO::prefLabel()
{
    return s_nao()->nao_prefLabel;
}

QUrl Soprano::Vocabulary::NAO::prefSymbol()
{
    return s_nao()->nao_prefSymbol;
}

QUrl Soprano::Vocabulary::NAO::rating()
{
    return s_nao()->nao_rating;
}

QUrl Soprano::Vocabulary::NAO::score()
{
    return s_nao()->nao_score;
}

QUrl Soprano::Vocabulary::NAO::scoreParameter()
{
    return s_nao()->nao_scoreParameter;
}

QUrl Soprano::Vocabulary::NAO::serializationLanguage()
{
    return s_nao()->nao_serializationLanguage;
}

QUrl Soprano::Vocabulary::NAO::status()
{
    return s_nao()->nao_status;
}

QUrl Soprano::Vocabulary::NAO::userVisible()
{
    return s_nao()->nao_userVisible;
}

QUrl Soprano::Vocabulary::NAO::version()
{
    return s_nao()->nao_version;
}

QUrl Soprano::Vocabulary::NAO::Agent()
{
    return s_nao()->nao_Agent;
}

QUrl Soprano::Vocabulary::NAO::maintainedBy()
{
    return s_nao()->nao_maintainedBy;
}
