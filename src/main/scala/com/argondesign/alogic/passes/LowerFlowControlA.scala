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
// Do:
// - Convert port flow control to stall statements
// - Split ports with flow control into constituent signals
// - Lower output storage slices into output slice instances
//
// Do not:
// - Update Connects yet
// - Replace naked port references yet
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.FlowControlTypes._
import com.argondesign.alogic.core.StorageTypes._
import com.argondesign.alogic.core.Symbols._
import com.argondesign.alogic.core.SyncRegFactory
import com.argondesign.alogic.core.SyncSliceFactory
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.util.unreachable

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

final class LowerFlowControlA(implicit cc: CompilerContext) extends TreeTransformer {

  private val sep = cc.sep

  // Map from output port symbol to output storage entity, instance symbol,
  // and a boolean that is true if the storage is multiple output slices
  private val oStorage = mutable.Map[Symbol, (Decl, Symbol, Boolean)]()

  // Stack of extra statements to emit when finished with a statement
  private[this] val extraStmts = mutable.Stack[mutable.ListBuffer[Stmt]]()

  private[this] val fctn = FlowControlTypeNone
  private[this] val stw = StorageTypeWire

  // Some statements can be completely removed, this flag marks them
  private[this] var removeStmt = false

  // New entities created in this pass
  private[this] val extraEntities = new ListBuffer[Decl]

  override def enter(tree: Tree): Unit = tree match {

    case Decl(Sym(symbol, _), _: DescEntity) =>
      symbol.attr.highLevelKind set symbol.kind.asType.kind.asEntity

    case Decl(Sym(symbol, _), _) =>
      symbol.kind match {
        ////////////////////////////////////////////////////////////////////////////
        // FlowControlTypeNone
        ////////////////////////////////////////////////////////////////////////////

        case TypeIn(_, FlowControlTypeNone) =>
          symbol.attr.fcn set true

        case TypeOut(_, FlowControlTypeNone, _) =>
          symbol.attr.fcn set true

        ////////////////////////////////////////////////////////////////////////////
        // FlowControlTypeValid
        ////////////////////////////////////////////////////////////////////////////

        case TypeIn(kind, FlowControlTypeValid) =>
          // Allocate payload and valid signals
          val loc = tree.loc
          val pName = symbol.name
          val vName = pName + sep + "valid"
          lazy val pSymbol = cc.newSymbol(pName, loc) tap { _.kind = TypeIn(kind, fctn) }
          val vSymbol = cc.newSymbol(vName, loc) tap { _.kind = TypeIn(TypeUInt(1), fctn) }
          val newSymbols = if (kind != TypeVoid) (Some(pSymbol), vSymbol) else (None, vSymbol)
          // Set attributes
          symbol.attr.fcv set newSymbols
          symbol.attr.expandedPort set true

        case TypeOut(kind, FlowControlTypeValid, st) =>
          // Allocate payload and valid signals
          val loc = tree.loc
          val pName = symbol.name
          val vName = pName + sep + "valid"
          lazy val pSymbol = cc.newSymbol(pName, loc) tap { _.kind = TypeOut(kind, fctn, stw) }
          val vSymbol = cc.newSymbol(vName, loc) tap { _.kind = TypeOut(TypeUInt(1), fctn, stw) }
          val newSymbols = if (kind != TypeVoid) (Some(pSymbol), vSymbol) else (None, vSymbol)
          // Set attributes
          symbol.attr.fcv set newSymbols
          symbol.attr.expandedPort set true
          if (st == StorageTypeWire) {
            vSymbol.attr.default set (ExprInt(false, 1, 0) withLoc loc)
            vSymbol.attr.clearOnStall set true
          } else {
            // If a synchronous output register is required, construct it
            // TODO: mark inline
            val eName = entitySymbol.name + sep + "or" + sep + pName
            val sregEntity = SyncRegFactory(eName, loc, kind)
            extraEntities append sregEntity
            val iSymbol = {
              val iName = "or" + sep + pName
              cc.newSymbol(iName, loc) tap { _.kind = sregEntity.symbol.kind.asType.kind }
            }
            // Set attributes
            oStorage(symbol) = (sregEntity, iSymbol, false)
            entitySymbol.attr.interconnectClearOnStall.append((iSymbol, s"ip${sep}valid"))
          }

        ////////////////////////////////////////////////////////////////////////////
        // FlowControlTypeReady
        ////////////////////////////////////////////////////////////////////////////

        case TypeIn(kind, FlowControlTypeReady) =>
          // Allocate payload, valid and ready signals
          val loc = tree.loc
          val pName = symbol.name
          val vName = pName + sep + "valid"
          val rName = pName + sep + "ready"
          lazy val pSymbol = cc.newSymbol(pName, loc) tap { _.kind = TypeIn(kind, fctn) }
          val vSymbol = cc.newSymbol(vName, loc) tap { _.kind = TypeIn(TypeUInt(1), fctn) }
          val rSymbol = cc.newSymbol(rName, loc) tap { _.kind = TypeOut(TypeUInt(1), fctn, stw) }
          val newSymbols = if (kind != TypeVoid) {
            (Some(pSymbol), vSymbol, rSymbol)
          } else {
            (None, vSymbol, rSymbol)
          }
          // Set attributes
          symbol.attr.fcr set newSymbols
          symbol.attr.expandedPort set true
          rSymbol.attr.default set (ExprInt(false, 1, 0) withLoc loc)
          rSymbol.attr.clearOnStall set true
          rSymbol.attr.dontCareUnless set vSymbol
          vSymbol.attr.dontCareUnless set rSymbol

        case TypeOut(kind, FlowControlTypeReady, st) =>
          // Allocate payload, valid and ready signals
          val loc = tree.loc
          val pName = symbol.name
          val vName = pName + sep + "valid"
          val rName = pName + sep + "ready"
          lazy val pSymbol = cc.newSymbol(pName, loc) tap { _.kind = TypeOut(kind, fctn, stw) }
          val vSymbol = cc.newSymbol(vName, loc) tap { _.kind = TypeOut(TypeUInt(1), fctn, stw) }
          val rSymbol = cc.newSymbol(rName, loc) tap { _.kind = TypeIn(TypeUInt(1), fctn) }
          val newSymbols = if (kind != TypeVoid) {
            (Some(pSymbol), vSymbol, rSymbol)
          } else {
            (None, vSymbol, rSymbol)
          }
          // Set attributes
          symbol.attr.fcr set newSymbols
          symbol.attr.expandedPort set true
          rSymbol.attr.dontCareUnless set vSymbol
          vSymbol.attr.dontCareUnless set rSymbol
          // If output slices are required, construct them
          st match {
            case StorageTypeWire           =>
            case StorageTypeSlices(slices) =>
              // TODO: mark inline
              val ePrefix = entitySymbol.name + sep + pName
              val sliceEntities = SyncSliceFactory(slices, ePrefix, loc, kind)
              extraEntities appendAll sliceEntities
              val iSymbol = {
                val iName = "os" + sep + pName
                cc.newSymbol(iName, loc) tap { _.kind = sliceEntities.head.symbol.kind.asType.kind }
              }
              // Set attributes
              oStorage(symbol) = (sliceEntities.head, iSymbol, sliceEntities.tail.nonEmpty)
              entitySymbol.attr.interconnectClearOnStall.append((iSymbol, s"ip${sep}valid"))
            case _ => unreachable
          }

        ////////////////////////////////////////////////////////////////////////////
        // FlowControlTypeAccept
        ////////////////////////////////////////////////////////////////////////////

        case TypeIn(kind, FlowControlTypeAccept) =>
          // Allocate payload, valid and accept signals
          val loc = tree.loc
          val pName = symbol.name
          val vName = pName + sep + "valid"
          val aName = pName + sep + "accept"
          lazy val pSymbol = cc.newSymbol(pName, loc) tap { _.kind = TypeIn(kind, fctn) }
          val vSymbol = cc.newSymbol(vName, loc) tap { _.kind = TypeIn(TypeUInt(1), fctn) }
          val aSymbol = cc.newSymbol(aName, loc) tap { _.kind = TypeOut(TypeUInt(1), fctn, stw) }
          val newSymbols = if (kind != TypeVoid) {
            (Some(pSymbol), vSymbol, aSymbol)
          } else {
            (None, vSymbol, aSymbol)
          }
          // Set attributes
          symbol.attr.fca set newSymbols
          symbol.attr.expandedPort set true
          aSymbol.attr.default set (ExprInt(false, 1, 0) withLoc loc)

        case TypeOut(kind, FlowControlTypeAccept, _) =>
          // Allocate payload, valid and ready signals
          val loc = tree.loc
          val pName = symbol.name
          val vName = pName + sep + "valid"
          val aName = pName + sep + "accept"
          lazy val pSymbol = cc.newSymbol(pName, loc) tap { _.kind = TypeOut(kind, fctn, stw) }
          val vSymbol = cc.newSymbol(vName, loc) tap { _.kind = TypeOut(TypeUInt(1), fctn, stw) }
          val aSymbol = cc.newSymbol(aName, loc) tap { _.kind = TypeIn(TypeUInt(1), fctn) }
          val newSymbols = if (kind != TypeVoid) {
            (Some(pSymbol), vSymbol, aSymbol)
          } else {
            (None, vSymbol, aSymbol)
          }
          // Set attributes
          symbol.attr.fca set newSymbols
          symbol.attr.expandedPort set true
          vSymbol.attr.default set (ExprInt(false, 1, 0) withLoc loc)
          vSymbol.attr.clearOnStall set true
          vSymbol.attr.dontCareUnless set aSymbol

        ////////////////////////////////////////////////////////////////////////////
        // Other decls
        ////////////////////////////////////////////////////////////////////////////

        case _ =>
      }

    ////////////////////////////////////////////////////////////////////////////
    // Statements
    ////////////////////////////////////////////////////////////////////////////

    case StmtExpr(expr @ ExprCall(ExprSelect(ExprSym(symbol), "read", _), _))
        if !expr.tpe.isVoid => {

      extraStmts.push(ListBuffer())

      val attr = symbol.attr

      // We can remove 'port.read();' statements altogether
      removeStmt = attr.fcn.isSet || attr.fcv.isSet || attr.fcr.isSet || attr.fca.isSet
    }

    case _: Stmt => {
      // Whenever we enter a new statement, add a new buffer to
      // store potential extra statements
      extraStmts.push(ListBuffer())
    }

    case _ =>
  }

  private[this] def assignTrue(expr: Expr) = StmtAssign(expr, ExprInt(false, 1, 1))

  override def transform(tree: Tree): Tree = {
    val result: Tree = tree match {

      //////////////////////////////////////////////////////////////////////////
      // Rewrite statements
      //////////////////////////////////////////////////////////////////////////

      // TODO: Factor out with non-void read
      case StmtExpr(expr @ ExprCall(ExprSelect(ref @ ExprSym(symbol), "read", _), Nil))
          if expr.tpe.isVoid => {
        symbol.attr.fcn.get.map { _ =>
          ref
        } orElse symbol.attr.fcv.get.map {
          case (None, vSymbol) =>
            StmtStall(ExprSym(vSymbol))
          case _ => unreachable
        } orElse symbol.attr.fcr.get.map {
          case (None, vSymbol, rSymbol) =>
            StmtBlock(
              List(
                assignTrue(ExprSym(rSymbol)),
                StmtStall(ExprSym(vSymbol))
              ))
          case _ => unreachable
        } orElse symbol.attr.fca.get.map {
          case (None, vSymbol, aSymbol) =>
            StmtBlock(
              List(
                assignTrue(ExprSym(aSymbol)),
                StmtStall(ExprSym(vSymbol))
              ))
          case _ => unreachable
        } getOrElse {
          tree
        }
      }

      case _: Stmt if removeStmt => {
        StmtBlock(Nil)
      } tap { _ =>
        removeStmt = false
      }

      case StmtExpr(ExprCall(ExprSelect(ref @ ExprSym(symbol), "write", _), args)) => {
        lazy val arg = args.head.asInstanceOf[ArgP].expr
        symbol.attr.fcn.get.map { _ =>
          StmtAssign(ref, arg)
        } orElse oStorage.get(symbol).map {
          case (_, iSymbol, _) =>
            lazy val iRef = ExprSym(iSymbol)
            lazy val pAssign = StmtAssign(iRef select "ip", arg)
            lazy val vAssign = assignTrue(iRef select s"ip${sep}valid")
            lazy val rStall = StmtStall(iRef select s"ip${sep}ready")
            symbol.attr.fcv.get.map {
              case (None, _) => vAssign
              case _         => StmtBlock(List(pAssign, vAssign))
            } orElse symbol.attr.fcr.get.map {
              case (None, _, _) => StmtBlock(List(vAssign, rStall))
              case _            => StmtBlock(List(pAssign, vAssign, rStall))
            } getOrElse {
              unreachable
            }
        } orElse symbol.attr.fcv.get.map {
          case (pSymbolOpt, vSymbol) =>
            val vAssign = assignTrue(ExprSym(vSymbol))
            pSymbolOpt match {
              case Some(pSymbol) =>
                val pAssign = StmtAssign(ExprSym(pSymbol), arg)
                StmtBlock(List(pAssign, vAssign))
              case None => vAssign
            }
        } orElse symbol.attr.fca.get.map {
          case (pSymbolOpt, vSymbol, aSymbol) =>
            val vAssign = assignTrue(ExprSym(vSymbol))
            val aStall = StmtStall(ExprSym(aSymbol))
            pSymbolOpt match {
              case Some(pSymbol) =>
                val pAssign = StmtAssign(ExprSym(pSymbol), arg)
                StmtBlock(List(pAssign, vAssign, aStall))
              case None => StmtBlock(List(vAssign, aStall))
            }
        } getOrElse {
          tree
        }
      }

      case StmtExpr(ExprCall(ExprSelect(ref @ ExprSym(symbol), "wait", _), args)) => {
        symbol.attr.fcr.get.map {
          case (_, vSymbol, _) => StmtStall(ExprSym(vSymbol))
        } getOrElse {
          tree
        }
      }

      case StmtExpr(ExprCall(ExprSelect(ref @ ExprSym(symbol), "flush", _), args)) => {
        oStorage.get(symbol).map {
          case (_, iSymbol, false) => StmtStall(ExprSym(iSymbol) select "space")
          case (_, iSymbol, true)  => StmtStall(ExprSym(iSymbol) select "space" unary "&")
        } getOrElse {
          tree
        }
      }

      //////////////////////////////////////////////////////////////////////////
      // Rewrite expressions
      //////////////////////////////////////////////////////////////////////////

      // TODO: Factor out with void read
      case ExprCall(ExprSelect(ref @ ExprSym(symbol), "read", _), Nil) if !tree.tpe.isVoid => {
        symbol.attr.fcn.get.map { _ =>
          ref
        } orElse symbol.attr.fcv.get.map {
          case (Some(pSymbol), vSymbol) =>
            extraStmts.top append StmtStall(ExprSym(vSymbol))
            ExprSym(pSymbol)
          case _ => unreachable
        } orElse symbol.attr.fcr.get.map {
          case (Some(pSymbol), vSymbol, rSymbol) =>
            extraStmts.top append assignTrue(ExprSym(rSymbol))
            extraStmts.top append StmtStall(ExprSym(vSymbol))
            ExprSym(pSymbol)
          case _ => unreachable
        } orElse symbol.attr.fca.get.map {
          case (Some(pSymbol), vSymbol, aSymbol) =>
            extraStmts.top append assignTrue(ExprSym(aSymbol))
            extraStmts.top append StmtStall(ExprSym(vSymbol))
            ExprSym(pSymbol)
          case _ => unreachable
        } getOrElse {
          tree
        }
      }

      case ExprSelect(ExprSym(symbol), "valid", _) => {
        symbol.attr.fcv.get.map {
          case (_, vSymbol) => ExprSym(vSymbol)
        } orElse symbol.attr.fcr.get.map {
          case (_, vSymbol, _) => ExprSym(vSymbol)
        } getOrElse {
          tree
        }
      }

      case ExprSelect(ExprSym(symbol), "space", _) => {
        oStorage.get(symbol) map {
          case (_, iSymbol, _) => ExprSym(iSymbol) select "space"
        } getOrElse {
          tree
        }
      }

      case ExprSelect(ExprSym(symbol), "empty", _) => {
        oStorage.get(symbol) map {
          case (_, iSymbol, false) => ExprSym(iSymbol) select "space"
          case (_, iSymbol, true)  => ExprSym(iSymbol) select "space" unary "&"
        } getOrElse {
          tree
        }
      }

      case ExprSelect(ExprSym(symbol), "full", _) => {
        oStorage.get(symbol) map {
          case (_, iSymbol, false) => ~(ExprSym(iSymbol) select "space")
          case (_, iSymbol, true)  => ~(ExprSym(iSymbol) select "space" unary "|")
        } getOrElse {
          tree
        }
      }

      //////////////////////////////////////////////////////////////////////////
      // Add declarations of the expanded symbols
      //////////////////////////////////////////////////////////////////////////

      case decl @ EntDecl(Decl(Sym(symbol, _), _)) => {
        // Note: We also leave the declaration of the original symbol, as
        // Connect instances have not been rewritten yet. These will be fixed
        // up in a later pass as they required all entities to have been
        // converted before we can type port references
        symbol.attr.fcv.get.map {
          case (pSymbolOpt, vSymbol) =>
            val vDecl = EntDecl(vSymbol.decl)
            val newDecls = pSymbolOpt match {
              case None          => List(vDecl)
              case Some(pSymbol) => List(EntDecl(pSymbol.decl), vDecl)
            }
            Thicket(decl :: newDecls)
        } orElse symbol.attr.fcr.get.map {
          case (pSymbolOpt, vSymbol, rSymbol) =>
            val vDecl = EntDecl(vSymbol.decl)
            val rDecl = EntDecl(rSymbol.decl)
            val newDecls = pSymbolOpt match {
              case None          => List(vDecl, rDecl)
              case Some(pSymbol) => List(EntDecl(pSymbol.decl), vDecl, rDecl)
            }
            Thicket(decl :: newDecls)
        } orElse symbol.attr.fca.get.map {
          case (pSymbolOpt, vSymbol, aSymbol) =>
            val vDecl = EntDecl(vSymbol.decl)
            val aDecl = EntDecl(aSymbol.decl)
            val newDecls = pSymbolOpt match {
              case None          => List(vDecl, aDecl)
              case Some(pSymbol) => List(EntDecl(pSymbol.decl), vDecl, aDecl)
            }
            Thicket(decl :: newDecls)
        } getOrElse {
          tree
        }
      }

      //////////////////////////////////////////////////////////////////////////
      // Add storage slice entities
      //////////////////////////////////////////////////////////////////////////

      case decl @ Decl(_, desc: DescEntity) => {
        val ospSymbols = desc.decls collect {
          case Decl(Sym(symbol, _), _) if oStorage contains symbol => symbol
        }

        val instances = ospSymbols map { symbol =>
          EntDecl(oStorage(symbol)._2.decl)
        }

        val connects = ospSymbols flatMap { symbol =>
          val iSymbol = oStorage(symbol)._2
          val iRef = ExprSym(iSymbol)

          val (pSymbolOpt, vSymbol, rSymbolOpt) = symbol.attr.fcv.get.map {
            case (pSymbolOpt, vSymbol) => (pSymbolOpt, vSymbol, None)
          } orElse symbol.attr.fcr.get.map {
            case (pSymbolOpt, vSymbol, rSymbol) => (pSymbolOpt, vSymbol, Some(rSymbol))
          } getOrElse {
            unreachable
          }

          val pConnOpt = pSymbolOpt map { pSymbol =>
            EntConnect(iRef select "op", List(ExprSym(pSymbol)))
          }
          val vConn = EntConnect(iRef select s"op${sep}valid", List(ExprSym(vSymbol)))
          val rConnOpt = rSymbolOpt map { rSymbol =>
            EntConnect(ExprSym(rSymbol), List(iRef select s"op${sep}ready"))
          }

          pConnOpt.toList ::: vConn :: rConnOpt.toList
        }

        // Remove fcn attributes, they are no longer needed
        desc.decls foreach {
          case Decl(Sym(symbol, Nil), _) => symbol.attr.fcn.clear()
          case _                         => unreachable
        }

        // Note: Output port defaults, including for flow control signals will
        // be set in the DefaultAssignments pass

        val newDesc = desc.copy(body = desc.body ::: instances ::: connects)
        val thisEntity = decl.copy(desc = newDesc)
        Thicket(thisEntity :: extraEntities.toList)
      }

      case _ => tree
    }

    assert(tree.isInstanceOf[Stmt] == result.isInstanceOf[Stmt])

    // Emit any extra statement with this statement
    val result2 = result match {
      case StmtBlock(Nil) =>
        val extra = extraStmts.pop()
        if (extra.isEmpty) Thicket(Nil) else StmtBlock(extra.toList)
      case stmt: Stmt =>
        val extra = extraStmts.pop()
        if (extra.isEmpty) stmt else StmtBlock((extra append stmt).toList)
      case _ => result
    }

    // If we did modify the node, regularize it
    if (result2 ne tree) {
      result2 regularize tree.loc
    }

    // Done
    result2
  }

  override def finalCheck(tree: Tree): Unit = {
    assert(extraStmts.isEmpty)

    tree visit {
      case node @ ExprCall(ExprSelect(ref, sel, _), _) if ref.tpe.isOut =>
        cc.ice(node, s"Output port .${sel}() remains")
      case node @ ExprCall(ExprSelect(ref, sel, _), _) if ref.tpe.isIn =>
        cc.ice(node, s"Input port .${sel}() remains")
    }
  }

}

object LowerFlowControlA extends TreeTransformerPass {
  val name = "lower-flow-control-a"

  def create(implicit cc: CompilerContext) = new LowerFlowControlA
}
