////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2018 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Geza Lore
//
// DESCRIPTION:
//
// Outputting facilities
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.core

import java.io.Writer

import com.argondesign.alogic.ast.Trees._

trait Output { this: CompilerContext =>

  private implicit val implicitThis: CompilerContext = this

  def getOutputWriter(entity: Decl, suffix: String): Writer = {
    settings.outputWriterFactory(entity, suffix)
  }

  def dump(decl: Decl, suffix: String): Unit = {
    val writer = getOutputWriter(decl, suffix + ".alogic")
    writer.write(decl.toSource)
    writer.write("\n")
    writer.close()
  }
}
