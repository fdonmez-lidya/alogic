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
// - Lower sram variables into sram instances
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Loc
import com.argondesign.alogic.core.SramFactory
import com.argondesign.alogic.core.StorageTypes.StorageTypeReg
import com.argondesign.alogic.core.StorageTypes.StorageTypeWire
import com.argondesign.alogic.core.Symbols._
import com.argondesign.alogic.core.SyncRegFactory
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.core.enums.EntityVariant
import com.argondesign.alogic.util.unreachable

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

final class SramBuilder {
  // Re-use SRAM entities of identical sizes
  val store = mutable.Map[(Int, Int), Decl]()

  def apply(width: Int, depth: Int)(implicit cc: CompilerContext): Decl = synchronized {
    lazy val sram = SramFactory(s"sram_${depth}x$width", Loc.synthetic, width, depth)
    store.getOrElseUpdate((width, depth), sram)
  }
}

final class LowerSrams(
    sramBuilder: SramBuilder
)(implicit cc: CompilerContext)
    extends TreeTransformer {

  private val sep = cc.sep

  // Collection of various bits required to implement SRAMs
  // These are all the possible components required
  //  sEntity: Decl,    // The SRAM entity
  //  sSymbol: Symbol,  // The instance of the SRAM entity above
  //  rSymbol: Symbol,  // If the SRAM is of struct type, this is the local rdata signal
  //  oEntity: Decl,    // If the output is registered, this is the SyncReg entity
  //  oSymbol: Symbol   // If the output is registered, the instance of the SyncReg entity above
  private sealed trait SramParts

  // TODO: sEntity is not unused in these

  // SRAM with wire driver and int/uint element type
  private case class SramWireInt(
      sEntity: Decl,
      sSymbol: Symbol
  ) extends SramParts
  // SRAM with wire driver and struct element type
  private case class SramWireStruct(
      sEntity: Decl,
      sSymbol: Symbol,
      rSymbol: Symbol
  ) extends SramParts
  // SRAM with reg driver and int/uint element type
  private case class SramRegInt(
      sEntity: Decl,
      sSymbol: Symbol,
      oEntity: Decl,
      oSymbol: Symbol
  ) extends SramParts
  // SRAM with reg driver and struct element type
  private case class SramRegStruct(
      sEntity: Decl,
      sSymbol: Symbol,
      rSymbol: Symbol,
      oEntity: Decl,
      oSymbol: Symbol
  ) extends SramParts

  // Extractors for transposed views of the above
  object SramWire {
    def unapply(parts: SramParts): Option[(Decl, Symbol)] = parts match {
      case SramWireInt(sEntity, sSymbol)       => Some((sEntity, sSymbol))
      case SramWireStruct(sEntity, sSymbol, _) => Some((sEntity, sSymbol))
      case _                                   => None
    }
  }

  object SramReg {
    def unapply(parts: SramParts): Option[(Decl, Symbol, Decl, Symbol)] =
      parts match {
        case SramRegInt(sEntity, sSymbol, oEntity, oSymbol) =>
          Some((sEntity, sSymbol, oEntity, oSymbol))
        case SramRegStruct(sEntity, sSymbol, _, oEntity, oSymbol) =>
          Some((sEntity, sSymbol, oEntity, oSymbol))
        case _ => None
      }
  }

  object SramInt {
    def unapply(parts: SramParts): Option[(Decl, Symbol)] = parts match {
      case SramWireInt(sEntity, sSymbol)      => Some((sEntity, sSymbol))
      case SramRegInt(sEntity, sSymbol, _, _) => Some((sEntity, sSymbol))
      case _                                  => None
    }
  }

  object SramStruct {
    def unapply(parts: SramParts): Option[(Decl, Symbol, Symbol)] = parts match {
      case SramWireStruct(sEntity, sSymbol, rSymbol)      => Some((sEntity, sSymbol, rSymbol))
      case SramRegStruct(sEntity, sSymbol, rSymbol, _, _) => Some((sEntity, sSymbol, rSymbol))
      case _                                              => None
    }
  }

  // Map from original sram variable symbol to the corresponding SramKit,
  private[this] val sramMap = mutable.LinkedHashMap[Symbol, SramParts]()

  // Stack of extra statements to emit when finished with a statement
  private[this] val extraStmts = mutable.Stack[mutable.ListBuffer[Stmt]]()

  override def skip(tree: Tree): Boolean = tree match {
    case Decl(_, DescEntity(EntityVariant.Net, _)) => true
    case _                                         => false
  }

  override def enter(tree: Tree): Unit = tree match {

    case Decl(Sym(symbol, _), _: DescSram) =>
      symbol.kind match {
        case TypeSram(kind, depth, st) =>
          val loc = tree.loc
          val name = symbol.name

          // Build the sram entity             // TODO: signed/unsigned
          val sEntity = sramBuilder(kind.width.toInt, depth.toInt)

          // Create the instance
          val sSymbol = cc.newSymbol("sram" + sep + name, loc) tap {
            _.kind = sEntity.symbol.kind.asType.kind
          }

          // If this is an SRAM with an underlying struct type, we need a new
          // signal to unpack the read data into, allocate this here
          lazy val rSymbol = cc.newSymbol(name + sep + "rdata", loc) tap { _.kind = kind }

          // If the sram is driven through registers, we need a SyncReg to drive it
          lazy val (oEntity, oSymbol) = {
            assert(st == StorageTypeReg)

            // Build the SyncReg entity
            val oEntity = {
              val oName = entitySymbol.name + sep + "or" + sep + name
              val weKind = sSymbol.kind.asEntity("we").get.kind.underlying
              val addrKind = sSymbol.kind.asEntity("addr").get.kind.underlying
              val weSymbol = cc.newSymbol("we", tree.loc) tap { _.kind = weKind }
              val addrSymbol = cc.newSymbol("addr", tree.loc) tap { _.kind = addrKind }
              val wdataSymbol = cc.newSymbol("wdata", tree.loc) tap { _.kind = kind }
              val oSymbol = cc.newSymbol(oName, tree.loc)
              val oKind = TypeType(TypeRecord(oSymbol, List(weSymbol, addrSymbol, wdataSymbol)))
              oSymbol.kind = oKind
              SyncRegFactory(oName, loc, oKind.kind)
            }

            // Create the instance
            val oSymbol = cc.newSymbol("or" + sep + name, loc) tap {
              _.kind = oEntity.symbol.kind.asType.kind
            }

            entitySymbol.attr.interconnectClearOnStall.append((oSymbol, s"ip${sep}valid"))

            (oEntity, oSymbol)
          }

          if (st == StorageTypeWire) {
            // Clear ce when the entity stalls
            entitySymbol.attr.interconnectClearOnStall.append((sSymbol, "ce"))
          }

          // We now have everything we possibly need, collect the relevant parts
          val sramParts = (kind, st) match {
            case (_: TypeInt, StorageTypeWire) =>
              SramWireInt(sEntity, sSymbol)
            case (_: TypeRecord | _: TypeVector, StorageTypeWire) =>
              SramWireStruct(sEntity, sSymbol, rSymbol)
            case (_: TypeInt, StorageTypeReg) =>
              SramRegInt(sEntity, sSymbol, oEntity, oSymbol)
            case (_: TypeRecord | _: TypeVector, StorageTypeReg) =>
              SramRegStruct(sEntity, sSymbol, rSymbol, oEntity, oSymbol)
            case _ =>
              cc.ice(tree, "Don't know how to build SRAM of type", kind.toSource)
          }

          sramMap(symbol) = sramParts
        case _ => unreachable
      }

    ////////////////////////////////////////////////////////////////////////////
    // FlowControlTypeReady
    ////////////////////////////////////////////////////////////////////////////

    case _: Stmt =>
      // Whenever we enter a new statement, add a new buffer to
      // store potential extra statements
      extraStmts.push(ListBuffer())

    case _ =>
  }

  private[this] def assignTrue(expr: Expr) = StmtAssign(expr, ExprInt(false, 1, 1))
  private[this] def assignFalse(expr: Expr) = StmtAssign(expr, ExprInt(false, 1, 0))

  override def transform(tree: Tree): Tree = {
    val result: Tree = tree match {

      //////////////////////////////////////////////////////////////////////////
      // Rewrite statements
      //////////////////////////////////////////////////////////////////////////

      case StmtExpr(ExprCall(ExprSelect(ExprSym(symbol), "read", _), List(ArgP(addr)))) =>
        sramMap.get(symbol) map {
          case SramWire(_, iSymbol) =>
            val iRef = ExprSym(iSymbol)
            StmtBlock(
              List(
                assignTrue(iRef select "ce"),
                assignFalse(iRef select "we"),
                StmtAssign(iRef select "addr", addr)
              ))
          case SramReg(_, _, _, oSymbol) =>
            symbol.kind match {
              case TypeSram(kind, _, _) =>
                val oRef = ExprSym(oSymbol)
                val data = ExprInt(false, kind.width.toInt, 0) // Don't care
                StmtBlock(
                  List(
                    assignTrue(oRef select s"ip${sep}valid"),
                    StmtAssign(oRef select "ip", ExprCat(List(ExprInt(false, 1, 0), addr, data)))
                  ))
              case _ => unreachable
            }
        } getOrElse {
          tree
        }

      case StmtExpr(
          ExprCall(ExprSelect(ExprSym(symbol), "write", _), List(ArgP(addr), ArgP(data)))) =>
        sramMap.get(symbol) map {
          case SramWire(_, iSymbol) =>
            val iRef = ExprSym(iSymbol)
            StmtBlock(
              List(
                assignTrue(iRef select "ce"),
                assignTrue(iRef select "we"),
                StmtAssign(iRef select "addr", addr),
                StmtAssign(iRef select "wdata", data)
              ))
          case SramReg(_, _, _, oSymbol) =>
            val oRef = ExprSym(oSymbol)
            StmtBlock(
              List(
                assignTrue(oRef select s"ip${sep}valid"),
                StmtAssign(oRef select "ip", ExprCat(List(ExprInt(false, 1, 1), addr, data)))
              ))
        } getOrElse {
          tree
        }

      //////////////////////////////////////////////////////////////////////////
      // Rewrite expressions
      //////////////////////////////////////////////////////////////////////////

      case ExprSelect(ExprSym(symbol), "rdata", _) =>
        sramMap.get(symbol) map {
          case SramInt(_, iSymbol)       => ExprSym(iSymbol) select "rdata"
          case SramStruct(_, _, rSymbol) => ExprSym(rSymbol)
        } getOrElse {
          tree
        }

      //////////////////////////////////////////////////////////////////////////
      // Add sram entities
      //////////////////////////////////////////////////////////////////////////

      case decl @ Decl(_, desc: DescEntity) if sramMap.nonEmpty =>
        val newBody = List from {
          {
            // Add rdata unpacking declarations
            sramMap.valuesIterator collect {
              case SramStruct(_, _, rSymbol) => rSymbol.decl
            } map EntDecl
          } concat {
            // Add instances
            sramMap.valuesIterator flatMap {
              case SramWire(_, sSymbol)            => Iterator.single(sSymbol.decl)
              case SramReg(_, sSymbol, _, oSymbol) => Iterator(sSymbol.decl, oSymbol.decl)
            } map EntDecl
          } concat {
            // Add connects for read data unpacking
            sramMap.valuesIterator collect {
              case SramStruct(_, sS, rS) =>
                EntConnect(ExprSym(sS) select "rdata", List(ExprSym(rS)))
            }
          } concat {
            // Add connects for reg driver
            {
              sramMap.valuesIterator collect {
                case SramReg(_, sS, _, oS) =>
                  Iterator(
                    EntConnect(ExprSym(oS) select s"op${sep}valid", List(ExprSym(sS) select "ce")),
                    EntConnect(ExprSym(oS) select s"op", List(ExprCat {
                      List(ExprSym(sS) select "we",
                           ExprSym(sS) select "addr",
                           ExprSym(sS) select "wdata")
                    }))
                  )
              }
            }.flatten
          } concat {
            // Drop sram, declarations
            desc.body.iterator filter {
              case EntDecl(Decl(_, _: DescSram)) => false
              case _                             => true
            }
          }
        }

        val newDecl = decl.copy(desc = desc.copy(body = newBody))

        // Note that we only collect register slices here,
        // SRAMs are added in the Pass dispatcher below
        val extraEntities = sramMap.valuesIterator collect {
          case SramReg(_, _, oEntity, _) => oEntity
        }

        Thicket(newDecl :: extraEntities.toList)

      case _ => tree
    }

    // Emit any extra statement with this statement
    val result2 = result match {
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
      case node @ ExprSelect(ref, sel, _) if ref.tpe.isSram => cc.ice(node, s"SRAM .$sel remains")
    }
  }

}

object LowerSrams {
  class LowerSramsPass extends TreeTransformerPass {
    val name = "lower-srams"

    val sramBuilder = new SramBuilder

    def create(implicit cc: CompilerContext) = new LowerSrams(sramBuilder)

    override def apply(trees: List[Tree])(implicit cc: CompilerContext): List[Tree] = {
      // Transform all trees
      val results = super.apply(trees)
      // Add all SRAMs as well
      sramBuilder.store.values.toList ::: results
    }
  }

  def apply(): Pass = new LowerSramsPass
}
