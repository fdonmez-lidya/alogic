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
// Specialize parameters and process 'gen' constructs
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.specialize.Specialize
import com.argondesign.alogic.util.unreachable

object Elaborate extends Pass {
  val name = "elaborate"

  def apply(trees: List[Tree])(implicit cc: CompilerContext): List[Tree] = {

    val specialize = new Specialize

    val specialziedTopLevels = Set from {
      trees.iterator flatMap {
        case root: Root =>
          root.decls filter { _.symbol.attr.topLevel.isSet } map { decl: Decl =>
            specialize(decl, Map.empty, decl.ref.loc)
          }
        case _ => unreachable
      }
    }

    if (specialziedTopLevels exists { _.isEmpty }) {
      // There was an error during specialization, no need to proceed
      Nil
    } else {
      // Extract every single definition referenced transitively by the top
      // level entities.

      def dependencies(decl: Decl): Set[Decl] = {
        val definedSymbols = Set from {
          decl collect { case Sym(symbol, _) => symbol }
        }
        val requiredSymbols = List from {
          decl collect {
            case ExprSym(symbol) if !definedSymbols(symbol) && !symbol.isBuiltin => symbol
          }
        }
        val requiredDecls = requiredSymbols.iterator map { _.decl }
        val externalDecls = requiredSymbols.iterator flatMap { symbol =>
          dependencies(symbol.decl)
        }
        Set.from(Iterator.single(decl) ++ requiredDecls ++ externalDecls)
      }

      // Sort, so it's in a deterministic order
      (specialziedTopLevels.flatten flatMap dependencies).toList.sortBy(_.symbol.id)
    }
  }
}
