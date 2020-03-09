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
// Lower variables into flops and combinatorial nets. At this stage, anything
// that is of TypeInt is a flop, unless it is driven through a connect, or is
// one of the control signals of a memory, in which case it is a net.
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.analysis.WrittenSymbols
import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Symbols.Symbol
import com.argondesign.alogic.core.Types.TypeUInt
import com.argondesign.alogic.core.enums.EntityVariant
import com.argondesign.alogic.core.enums.ResetStyle
import com.argondesign.alogic.typer.TypeAssigner

import scala.collection.mutable.ListBuffer

final class LowerVariables(implicit cc: CompilerContext) extends TreeTransformer {

  // TODO: Generate clock enables

  override def skip(tree: Tree): Boolean = tree match {
    // We do not replace _q with _d in connects, connects always use the _q
    case _: EntConnect => true
    case _             => false
  }

  private val resetFlops = new ListBuffer[(Symbol, Symbol, Expr)]()
  private val nonResetFlops = new ListBuffer[(Symbol, Symbol)]()

  override def enter(tree: Tree): Option[Tree] = {
    tree match {

      case defn: DefnEntity =>
        // Drop the oreg prefix from the flops allocated for registered outputs,
        // These will now gain _d and _q, so the names will become unique.
        val prefix = s"`oreg${cc.sep}"
        val prefixLen = prefix.length
        for {
          Defn(symbol) <- defn.defns
          if symbol.name startsWith prefix
        } {
          symbol.name = symbol.name drop prefixLen
        }

        // Mark local symbols driven by Connect as combinational nets
        for {
          EntConnect(_, List(rhs)) <- defn.connects
          symbol <- WrittenSymbols(rhs)
          if symbol.kind.isInt
        } {
          symbol.attr.combSignal set true
        }

        defn.defns foreach {
          case defn @ DefnVar(symbol, initOpt) if !(symbol.attr.combSignal contains true) =>
            val loc = defn.loc
            val name = symbol.name
            // Append _q to the name of the symbol
            symbol.name = s"${name}_q"
            // Create the _d symbol
            val dSymbol = cc.newSymbol(s"${name}_d", loc) tap {
              _.kind = symbol.kind
            }
            // Move the clearOnStall attribute to the _d symbol
            symbol.attr.clearOnStall.get foreach { attr =>
              dSymbol.attr.clearOnStall set attr
              symbol.attr.clearOnStall.clear()
            }
            // If the symbol has a default attribute, move that to the _d,
            // otherwise use the _q as the default initializer
            val default = symbol.attr.default.getOrElse {
              ExprSym(symbol) regularize loc
            }
            dSymbol.attr.default set default
            symbol.attr.default.clear()
            // Set attributes
            symbol.attr.flop set dSymbol
            // Memorize
            if (cc.settings.resetAll || initOpt.isDefined) {
              val kind = symbol.kind
              val resetExpr = initOpt getOrElse ExprInt(kind.isSigned, kind.width.toInt, 0)
              resetFlops.append((symbol, dSymbol, resetExpr))
            } else {
              nonResetFlops.append((symbol, dSymbol))
            }

          case _ =>
        }

      case _ =>
    }
    None
  }

  override def transform(tree: Tree): Tree = tree match {

    //////////////////////////////////////////////////////////////////////////
    // Rewrite references
    //////////////////////////////////////////////////////////////////////////

    case ExprSym(qSymbol) =>
      // Rewrite references to flops as references to the _d,
      qSymbol.attr.flop.get map { dSymbol =>
        ExprSym(dSymbol) regularize tree.loc
      } getOrElse {
        tree
      }

    //////////////////////////////////////////////////////////////////////////
    // Add the clocked processes
    //////////////////////////////////////////////////////////////////////////

    case defn: DefnEntity =>
      lazy val goSymbolOpt = defn.defns collectFirst {
        case Defn(symbol) if symbol.attr.go.isSet => symbol
      }
      val resetProcess = Option.when(resetFlops.nonEmpty) {
        // TODO: Here we just make up an undeclared reset symbol (yuck) so we
        // can condition on it. It should be a proper signal...
        val rstSymbol = cc.newSymbol(cc.rst, tree.loc) tap { _.kind = TypeUInt(1) }
        val rstLow = cc.settings.resetStyle match {
          case ResetStyle.AsyncLow | ResetStyle.SyncLow => true
          case _                                        => false
        }
        val resetAssigns = List from {
          resetFlops.iterator map {
            case (qSymbol, _, resetVal) => StmtDelayed(ExprSym(qSymbol), resetVal)
          }
        }
        val dAssigns = {
          val assigns = List from {
            resetFlops.iterator map {
              case (qSymbol, dSymbol, _) => StmtDelayed(ExprSym(qSymbol), ExprSym(dSymbol))
            }
          }
          goSymbolOpt match {
            case None => assigns
            case Some(goSymbol) =>
              List(StmtIf(ExprSym(goSymbol), assigns, Nil))
          }
        }
        EntClockedProcess(
          reset = true,
          List(
            StmtComment("Reset flops"),
            StmtIf(
              if (rstLow) !ExprSym(rstSymbol) else ExprSym(rstSymbol),
              resetAssigns,
              dAssigns
            )
          )
        ) regularize tree.loc
      }
      val nonResetProcess = Option.when(nonResetFlops.nonEmpty) {
        val dAssigns = {
          val assigns = List from {
            nonResetFlops.iterator map {
              case (qSymbol, dSymbol) => StmtDelayed(ExprSym(qSymbol), ExprSym(dSymbol))
            }
          }
          goSymbolOpt match {
            case None => assigns
            case Some(goSymbol) =>
              List(StmtIf(ExprSym(goSymbol), assigns, Nil))
          }
        }
        EntClockedProcess(
          reset = false,
          StmtComment("Non-reset flops") :: dAssigns
        ) regularize tree.loc
      }
      if (resetProcess.isDefined || nonResetProcess.isDefined) {
        val newBody = defn.body ++ resetProcess.iterator ++ nonResetProcess.iterator
        TypeAssigner(defn.copy(body = newBody) withLoc tree.loc)
      } else {
        tree
      }

    //////////////////////////////////////////////////////////////////////////
    // Add declarations and definitions
    //////////////////////////////////////////////////////////////////////////

    case decl @ Decl(qSymbol) =>
      qSymbol.attr.flop.get map { dSymbol =>
        Thicket(List(decl, dSymbol.mkDecl)) regularize tree.loc
      } getOrElse tree

    case defn @ Defn(qSymbol) =>
      qSymbol.attr.flop.get map { dSymbol =>
        Thicket(List(defn, dSymbol.mkDefn)) regularize tree.loc
      } getOrElse tree

    //////////////////////////////////////////////////////////////////////////
    // Note: Initial _d = _q fence statements will be added in
    // DefaultAssignments as required
    //////////////////////////////////////////////////////////////////////////

    case _ => tree
  }

}

object LowerVariables extends EntityTransformerPass(declFirst = false) {
  val name = "lower-variables"

  override def skip(decl: Decl, defn: Defn)(implicit cc: CompilerContext): Boolean =
    super.skip(decl, defn) || {
      defn match {
        case DefnEntity(_, EntityVariant.Net, _) => true
        case _                                   => false
      }
    }

  def create(symbol: Symbol)(implicit cc: CompilerContext) = new LowerVariables
}
