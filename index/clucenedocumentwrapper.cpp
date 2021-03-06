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

#include "clucenedocumentwrapper.h"
#include "cluceneutils.h"
#include "tstring.h"

#include "clucene-config.h"

#include <CLucene/document/Document.h>
#include <CLucene/document/Field.h>

#include <QtCore/QDebug>


class Soprano::Index::CLuceneDocumentWrapper::Private
{
public:
    lucene::document::Document* document;
};


Soprano::Index::CLuceneDocumentWrapper::CLuceneDocumentWrapper( lucene::document::Document* doc )
    : d( new Private() )
{
    d->document = doc;
}


Soprano::Index::CLuceneDocumentWrapper::~CLuceneDocumentWrapper()
{
    delete d;
}


using lucene::document::Field;

void Soprano::Index::CLuceneDocumentWrapper::addProperty( const TString& field, const TString& text, bool isUri )
{
    // FIXME: I think we should only index (and never store) the following:
    //        1. The predicate/literal combination itself
    //        2. Everything in the "text" or "content" or some other special field

    // FIXME: Do we really need to store the values? after all we have them in the RDF store anyway!
    //        And if we have to store we could do it compressed using jstreams
    // store this predicate (YES, the CLucene API is that weird. We actually put in Fields allocated on the heap here!)
    d->document->add( *new Field( field.data(), text.data(),
#ifdef CL_VERSION_19_OR_GREATER
                                  isUri
                                  ? Field::STORE_YES|Field::INDEX_UNTOKENIZED|Field::TERMVECTOR_NO
                                  : Field::STORE_YES|Field::INDEX_TOKENIZED|Field::TERMVECTOR_NO
#else
                                  true /*store*/, true/*index*/, isUri /*tokenize*/
#endif
                          ) );

    // We don't have to recalculate the concatenated text: just add another
    // TEXT field and Lucene will take care of this. Additional advantage:
    // Lucene may be able to handle the invididual strings in a way that may
    // affect e.g. phrase and proximity searches (concatenation basically
    // means loss of information).
    //
    // (YES, the CLucene API is that weird. We actually put in Fields allocated on the heap here!)
    if( !isUri ) {
        d->document->add( *new Field( textFieldName().data(), text.data(),
#ifdef CL_VERSION_19_OR_GREATER
                                      Field::STORE_NO|Field::INDEX_TOKENIZED|Field::TERMVECTOR_NO
#else
                                      false, true, true
#endif
                              ) );
    }

}


void Soprano::Index::CLuceneDocumentWrapper::removeProperty( const TString& field, const TString& text, bool isUri )
{
    // clucene does not allow to remove a specific field/value combination. Thus,
    // we have to do a little hackling and re-add everything except our property (could we maybe just get these from the RDF model?)

    // step 1: remove the field itself
    TCHAR** values = d->document->getValues( field.data() );
    if ( values ) {
        d->document->removeFields( field.data() );

        // now copy the ones that we want to preserve back
        for ( int i = 0; values[i]; ++i ) {
            TString value( values[i], true );
            if ( value != text ) {
                // FIXME: using isUri here means that for one field isUri is always the same.
                // While this in theory is correct there might still be invalid data in Soprano
                addProperty( field, values[i], isUri );
            }
        }

        _CLDELETE_ARRAY( values );
    }

    // step 2: remove the field from the text index
    if( !isUri ) {
        d->document->removeFields( textFieldName().data() );

        lucene::document::DocumentFieldEnumeration* e = d->document->fields();
        while ( e->hasMoreElements() ) {
            lucene::document::Field* field = e->nextElement();
            if ( isPropertyField( TString( field->name(), true ) ) ) {
                d->document->add( *new Field( textFieldName().data(), field->stringValue(),
#ifdef CL_VERSION_19_OR_GREATER
                                              Field::STORE_NO|Field::INDEX_TOKENIZED|Field::TERMVECTOR_NO
#else
                                              false, true, true
#endif
                                      ) );
            }
        }
        _CLDELETE( e );
    }
}


bool Soprano::Index::CLuceneDocumentWrapper::hasProperty( const QString& field, const QString& text ) const
{
    TString wText( text );
    TCHAR** values = d->document->getValues( TString( field ).data() );
    while ( values ) {
        if ( TString( *values, true ) == wText ) {
            return true;
        }
        ++values;
    }

    return false;
}


int Soprano::Index::CLuceneDocumentWrapper::numberOfPropertyFields() const
{
    // ugly but fast hack, assumes that only the ID and the predicates are
    // stored.
    int size = 0;
    lucene::document::DocumentFieldEnumeration* fields = d->document->fields();
    while ( fields->hasMoreElements() ) {
        ++size;
        fields->nextElement();
    }
    _CLDELETE( fields );

    return qMax( 0, size - 1 );
}


void Soprano::Index::CLuceneDocumentWrapper::addID( const QString& id )
{
    // (YES, the CLucene API is that weird. We actually put in Fields allocated on the heap here!)
    d->document->add( *new lucene::document::Field( idFieldName().data(), TString( id ).data(),
#ifdef CL_VERSION_19_OR_GREATER
                                                    Field::STORE_YES|Field::INDEX_UNTOKENIZED|Field::TERMVECTOR_NO
#else
                                                    true, true, false
#endif
                          ) );
}


void Soprano::Index::CLuceneDocumentWrapper::save( lucene::index::IndexWriter* writer )
{
    writer->addDocument( d->document );
}
