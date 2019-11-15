////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2019 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Geza Lore
//
// DESCRIPTION:
//
// Clone tree by replacing all symbols declared within this tree with fresh
// copies, so the new tree is independent of the old tree.
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.transform

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext

object Clone {

  def apply(decl: Decl)(implicit cc: CompilerContext): Decl = {
    // Create the symbol map by creating a new symbol for each symbol declared
    // in this tree
    val symbolMap = Map from {
      decl collectAll { case Decl(Sym(symbol, _), _) => symbol -> symbol.dup }
    }

    // Transform that replaces references to cloned symbols
    val transform = new TreeTransformer {
      override val typed: Boolean = false
      override val checkRefs: Boolean = false

      override def transform(tree: Tree): Tree = tree match {
        case node: Sym     => node.copy(symbol = symbolMap(node.symbol)) withLoc node.loc
        case node: ExprSym => node.copy(symbol = symbolMap(node.symbol)) withLoc node.loc
        case node          => node
      }
    }

    // Apply transform and we are done
    (decl rewrite transform).asInstanceOf[Decl]
  }

}
