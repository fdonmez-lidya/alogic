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
// Lift srams to outer entities and wire them through ports.
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees.Expr.InstancePortRef
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.FlowControlTypes.FlowControlTypeNone
import com.argondesign.alogic.core.StorageTypes.StorageTypeWire
import com.argondesign.alogic.core.Symbols.Symbol
import com.argondesign.alogic.core.Types.TypeIn
import com.argondesign.alogic.core.Types.TypeOut
import com.argondesign.alogic.typer.TypeAssigner
import com.argondesign.alogic.util.unreachable

import scala.annotation.tailrec
import scala.collection.mutable

final class LiftSramsFrom(
    liftFromMap: Map[Symbol, List[Symbol]]
)(implicit cc: CompilerContext)
    extends TreeTransformer {

  private val fcn = FlowControlTypeNone
  private val stw = StorageTypeWire

  // Map from 'instance.port' -> 'lifted port'
  private val portMap = mutable.LinkedHashMap[(Symbol, Symbol), Symbol]()

  override def skip(tree: Tree): Boolean = tree match {
    case decl: Decl => !(liftFromMap contains decl.symbol)
    case _          => false
  }

  override protected def enter(tree: Tree): Unit = tree match {
    case Decl(Sym(symbol, _), desc: DescEntity) =>
      val ourList = liftFromMap(entitySymbol)

      // For each port of the instances being lifted,
      // create a new port on the current entity
      for {
        Decl(Sym(iSymbol, _), _) <- desc.instances
        if ourList contains iSymbol
        pSymbol <- iSymbol.kind.asEntity.publicSymbols
      } yield {
        val name = iSymbol.name + cc.sep + pSymbol.name
        val loc = iSymbol.loc
        val nSymbol = pSymbol.kind match {
          case TypeIn(kind, `fcn`) =>
            cc.newSymbol(name, loc) tap { _.kind = TypeOut(kind, fcn, stw) }
          case TypeOut(kind, `fcn`, `stw`) =>
            cc.newSymbol(name, loc) tap { _.kind = TypeIn(kind, fcn) }
          case _ => unreachable
        }
        // Propagate interconnectClearOnStall to lifted node
        for {
          icos <- symbol.attr.interconnectClearOnStall.get
          if icos contains ((iSymbol, pSymbol.name))
        } {
          nSymbol.attr.clearOnStall set true
        }
        portMap((iSymbol, pSymbol)) = nSymbol
      }

    case _ => ()
  }

  override protected def transform(tree: Tree): Tree = tree match {

    ////////////////////////////////////////////////////////////////////////////
    // Rewrite references to instance.port as references to the new port
    ////////////////////////////////////////////////////////////////////////////

    case InstancePortRef(iSymbol, pSymbol) =>
      portMap.get((iSymbol, pSymbol)) map { nSymbol =>
        ExprSym(nSymbol) regularize tree.loc
      } getOrElse {
        tree
      }

    ////////////////////////////////////////////////////////////////////////////
    // Replace instances, add the new ports
    ////////////////////////////////////////////////////////////////////////////

    case decl @ Decl(Sym(symbol, _), desc: DescEntity) =>
      val ourList = liftFromMap(symbol)

      val newBody = List from {
        {
          // Add new declarations
          portMap.valuesIterator map { symbol =>
            EntDecl(symbol.decl) regularize symbol.loc
          }
        } concat {
          // Loose lifted instances
          desc.body.iterator filterNot {
            case EntDecl(d) => ourList contains d.symbol
            case _          => false
          }
        }
      }

      val newDesc = TypeAssigner(desc.copy(body = newBody) withLoc desc.loc)
      TypeAssigner(decl.copy(desc = newDesc) withLoc desc.loc)

    case _ => tree
  }

}

final class LiftSramsTo(
    liftFromMap: Map[Symbol, List[Symbol]]
)(implicit cc: CompilerContext)
    extends TreeTransformer {

  private def portRef(iSymbol: Symbol, sel: String) = ExprSelect(ExprSym(iSymbol), sel, Nil)

  override protected def transform(tree: Tree): Tree = tree match {
    case desc: DescEntity =>
      // For each instance that we lifted something out from,
      // create the lifted instances and connect them up
      val (newInstances, newConnects) = {
        val items = for {
          Decl(Sym(iSymbol, _), _) <- desc.instances
          eSymbol = iSymbol.kind.asEntity.symbol
          lSymbol <- liftFromMap.getOrElse(eSymbol, Nil)
        } yield {
          val prefix = "sram" + cc.sep
          assert(lSymbol.name startsWith prefix)
          val name = prefix + iSymbol.name + cc.sep + lSymbol.name.drop(prefix.length)
          val lKind = lSymbol.kind.asEntity
          // Create the local instance
          val nSymbol = cc.newSymbol(name, iSymbol.loc) tap { _.kind = lKind }
          val instance = EntDecl(nSymbol.decl) regularize lSymbol.loc
          // Create the connections
          val connects = for (pSymbol <- lKind.publicSymbols.iterator) yield {
            val iPortName = lSymbol.name + cc.sep + pSymbol.name
            val connect = pSymbol.kind match {
              case _: TypeIn =>
                EntConnect(portRef(iSymbol, iPortName), List(portRef(nSymbol, pSymbol.name)))
              case _: TypeOut =>
                EntConnect(portRef(nSymbol, pSymbol.name), List(portRef(iSymbol, iPortName)))
              case _ => unreachable
            }
            connect regularize lSymbol.loc
          }
          (instance, connects)
        }
        items.unzip
      }

      if (newInstances.isEmpty) {
        tree
      } else {
        TypeAssigner {
          desc.copy(body = desc.body ::: newInstances ::: newConnects.flatten) withLoc tree.loc
        }
      }

    // Types for entities changed by LiftSramsFrom. Re-type references
    case expr @ ExprSym(symbol) if symbol.kind.isType =>
      TypeAssigner(expr.copy() withLoc expr.loc)

    case _ => tree
  }
}

object LiftSrams extends Pass {
  val name = "lift-srams"

  def apply(trees: List[Tree])(implicit cc: CompilerContext): List[Tree] = {

    // TODO: We just accidentally lost all non-entitities here
    val entities = trees collect {
      case decl @ Decl(_, _: DescEntity) => decl
    }

    // Build an eSymbol -> entity map
    val eMap = Map from {
      entities map { entity =>
        entity.symbol -> entity
      }
    }

    // Gather entities with the liftSrams attribute,
    // and all other entities instantiated by them
    val liftFromSet = {
      val seed = Set from {
        entities filter { entity =>
          entity.symbol.attr.liftSrams contains true
        }
      }

      // Expand entity set by adding all instantiated entities
      @tailrec
      def expand(curr: Set[Decl], prev: Set[Decl]): Set[Decl] = {
        if (curr == prev) {
          curr
        } else {
          val extra = curr flatMap {
            case Decl(_, desc: DescEntity) =>
              desc.instances map { inst =>
                eMap(inst.symbol.kind.asEntity.symbol)
              }
            case _ => unreachable
          }
          expand(curr union extra, curr)
        }
      }

      expand(seed, Set()) map { _.symbol }
    }

    // Lift entities by 1 level in each iteration
    @tailrec
    def loop(entities: List[Decl]): List[Decl] = {
      // Gather the 'parent entity' -> 'List(lifted instance)' map
      val liftFromMap = {
        val pairs = for {
          entity <- entities.iterator
          if liftFromSet contains entity.symbol
        } yield {
          val desc = entity.desc.asInstanceOf[DescEntity]
          val iSymbols = for {
            instance <- desc.instances
            if instance.symbol.kind.asEntity.symbol.attr.sram contains true
          } yield {
            instance.symbol
          }
          entity.symbol -> iSymbols
        }
        Map from { pairs filter { _._2.nonEmpty } }
      }

      if (liftFromMap.isEmpty) {
        entities
      } else {
        // Apply the liftFrom transform
        val liftedFrom = entities map { entity =>
          (entity rewrite new Retype rewrite new LiftSramsFrom(liftFromMap) rewrite new Retype)
            .asInstanceOf[Decl]
        }

        // Apply the liftTo transform
        val liftedTo = liftedFrom map { entity =>
          (entity rewrite new Retype rewrite new LiftSramsTo(liftFromMap) rewrite new Retype)
            .asInstanceOf[Decl]
        }

        // Repeat until settles
        loop(liftedTo)
      }
    }

    loop(entities)
  }
}
