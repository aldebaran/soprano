/*
 * This file is part of Soprano Project.
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

#ifndef _SOPRANO_OWL_H_
#define _SOPRANO_OWL_H_

#include <QtCore/QUrl>
#include "soprano_export.h"

namespace Soprano {
    namespace Vocabulary {
        namespace OWL {
            /**
             * http://www.w3.org/2002/07/owl#
             */
            SOPRANO_EXPORT QUrl owlNamespace();

            /**
             * http://www.w3.org/2002/07/owl#AllDifferent 
             */
            SOPRANO_EXPORT QUrl AllDifferent();

            /**
             * http://www.w3.org/2002/07/owl#AnnotationProperty 
             */
            SOPRANO_EXPORT QUrl AnnotationProperty();

            /**
             * http://www.w3.org/2002/07/owl#Class 
             */
            SOPRANO_EXPORT QUrl Class();

            /**
             * http://www.w3.org/2002/07/owl#DataRange 
             */
            SOPRANO_EXPORT QUrl DataRange();

            /**
             * http://www.w3.org/2002/07/owl#DatatypeProperty 
             */
            SOPRANO_EXPORT QUrl DatatypeProperty();

            /**
             * http://www.w3.org/2002/07/owl#DeprecatedClass 
             */
            SOPRANO_EXPORT QUrl DeprecatedClass();

            /**
             * http://www.w3.org/2002/07/owl#DeprecatedProperty 
             */
            SOPRANO_EXPORT QUrl DeprecatedProperty();

            /**
             * http://www.w3.org/2002/07/owl#FunctionalProperty 
             */
            SOPRANO_EXPORT QUrl FunctionalProperty();

            /**
             * http://www.w3.org/2002/07/owl#InverseFunctionalProperty 
             */
            SOPRANO_EXPORT QUrl InverseFunctionalProperty();

            /**
             * http://www.w3.org/2002/07/owl#ObjectProperty 
             */
            SOPRANO_EXPORT QUrl ObjectProperty();

            /**
             * http://www.w3.org/2002/07/owl#Ontology 
             */
            SOPRANO_EXPORT QUrl Ontology();

            /**
             * http://www.w3.org/2002/07/owl#OntologyProperty 
             */
            SOPRANO_EXPORT QUrl OntologyProperty();

            /**
             * http://www.w3.org/2002/07/owl#Restriction 
             */
            SOPRANO_EXPORT QUrl Restriction();

            /**
             * http://www.w3.org/2002/07/owl#SymmetricProperty 
             */
            SOPRANO_EXPORT QUrl SymmetricProperty();

            /**
             * http://www.w3.org/2002/07/owl#TransitiveProperty 
             */
            SOPRANO_EXPORT QUrl TransitiveProperty();

            /**
             * http://www.w3.org/2002/07/owl#allValuesFrom 
             */
            SOPRANO_EXPORT QUrl allValuesFrom();

            /**
             * http://www.w3.org/2002/07/owl#backwardCompatibleWith 
             */
            SOPRANO_EXPORT QUrl backwardCompatibleWith();

            /**
             * http://www.w3.org/2002/07/owl#cardinality 
             */
            SOPRANO_EXPORT QUrl cardinality();

            /**
             * http://www.w3.org/2002/07/owl#complementOf 
             */
            SOPRANO_EXPORT QUrl complementOf();

            /**
             * http://www.w3.org/2002/07/owl#differentFrom 
             */
            SOPRANO_EXPORT QUrl differentFrom();

            /**
             * http://www.w3.org/2002/07/owl#disjointWith 
             */
            SOPRANO_EXPORT QUrl disjointWith();

            /**
             * http://www.w3.org/2002/07/owl#distinctMembers 
             */
            SOPRANO_EXPORT QUrl distinctMembers();

            /**
             * http://www.w3.org/2002/07/owl#equivalentClass 
             */
            SOPRANO_EXPORT QUrl equivalentClass();

            /**
             * http://www.w3.org/2002/07/owl#equivalentProperty 
             */
            SOPRANO_EXPORT QUrl equivalentProperty();

            /**
             * http://www.w3.org/2002/07/owl#hasValue 
             */
            SOPRANO_EXPORT QUrl hasValue();

            /**
             * http://www.w3.org/2002/07/owl#imports 
             */
            SOPRANO_EXPORT QUrl imports();

            /**
             * http://www.w3.org/2002/07/owl#incompatibleWith 
             */
            SOPRANO_EXPORT QUrl incompatibleWith();

            /**
             * http://www.w3.org/2002/07/owl#intersectionOf 
             */
            SOPRANO_EXPORT QUrl intersectionOf();

            /**
             * http://www.w3.org/2002/07/owl#inverseOf 
             */
            SOPRANO_EXPORT QUrl inverseOf();

            /**
             * http://www.w3.org/2002/07/owl#maxCardinality 
             */
            SOPRANO_EXPORT QUrl maxCardinality();

            /**
             * http://www.w3.org/2002/07/owl#minCardinality 
             */
            SOPRANO_EXPORT QUrl minCardinality();

            /**
             * http://www.w3.org/2002/07/owl#onProperty 
             */
            SOPRANO_EXPORT QUrl onProperty();

            /**
             * http://www.w3.org/2002/07/owl#oneOf 
             */
            SOPRANO_EXPORT QUrl oneOf();

            /**
             * http://www.w3.org/2002/07/owl#priorVersion 
             */
            SOPRANO_EXPORT QUrl priorVersion();

            /**
             * http://www.w3.org/2002/07/owl#sameAs 
             */
            SOPRANO_EXPORT QUrl sameAs();

            /**
             * http://www.w3.org/2002/07/owl#someValuesFrom 
             */
            SOPRANO_EXPORT QUrl someValuesFrom();

            /**
             * http://www.w3.org/2002/07/owl#unionOf 
             */
            SOPRANO_EXPORT QUrl unionOf();

            /**
             * http://www.w3.org/2002/07/owl#versionInfo 
             */
            SOPRANO_EXPORT QUrl versionInfo();
        }
    }
}

#endif
