/* This file is part of Soprano
 *
 * Copyright (C) 2006 Daniele Galdi <daniele.galdi@gmail.com>
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

#ifndef SOPRANO_REDLANDMODEL_FACTORY_H
#define SOPRANO_REDLANDMODEL_FACTORY_H

#include "ModelFactory.h"
#include "RedlandModel.h"

namespace Soprano
{

class RedlandModelFactory: public ModelFactory
{
public:
  RedlandModelFactory();
  ~RedlandModelFactory();

  RedlandModel *createMemoryModel( const QString &name ) const;

  RedlandModel *createPersistentModel( const QString &name, const QString &filePath ) const;
private:
  RedlandModelFactory( const RedlandModelFactory &other ) {};
};

}

#endif
