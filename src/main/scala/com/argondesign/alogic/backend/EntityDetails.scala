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
// Unpicked entity details used in the backed
////////////////////////////////////////////////////////////////////////////////
package com.argondesign.alogic.backend

import com.argondesign.alogic.ast.Trees.Expr.InstancePortRef
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Symbols._
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.core.enums.EntityVariant

final class EntityDetails(val entity: Decl, details: => Map[Symbol, EntityDetails])(
    implicit cc: CompilerContext) {

  val desc = entity.desc.asInstanceOf[DescEntity]

  assert {
    desc.decls forall {
      _.symbol.kind match {
        case _: TypeInt    => true
        case _: TypeEntity => true
        case _: TypeIn     => true
        case _: TypeOut    => true
        case _: TypeConst  => true
        case _: TypeArray  => true
        case _             => false
      }
    }
  }

  val resetFlops: List[Decl] = desc.decls filter {
    case Decl(Sym(symbol, _), DescVar(_, Some(_))) => symbol.attr.flop.isSet
    case Decl(Sym(symbol, _), DescVar(_, None))    => symbol.attr.flop.isSet && cc.settings.resetAll
    case _                                         => false
  }

  val unresetFlops: List[Decl] = desc.decls filter {
    case Decl(Sym(symbol, _), DescVar(_, None)) => symbol.attr.flop.isSet && !cc.settings.resetAll
    case _                                      => false
  }

  lazy val isVerbatim: Boolean = desc.variant == EntityVariant.Ver

  lazy val hasConsts: Boolean = desc.decls exists { _.symbol.kind.isConst }

  lazy val hasFlops: Boolean = resetFlops.nonEmpty || unresetFlops.nonEmpty

  lazy val hasCombSignals: Boolean = desc.decls exists { _.symbol.attr.combSignal.isSet }

  lazy val hasArrays: Boolean = desc.decls exists { _.symbol.attr.memory.isSet }

  lazy val hasInterconnect: Boolean = desc.decls exists { _.symbol.attr.interconnect.isSet }

  lazy val hasInstances: Boolean = desc.instances.nonEmpty

  lazy val canStall: Boolean = desc.preOrderIterator exists {
    case _: StmtStall => true
    case _            => false
  }

  lazy val needsClock: Boolean = isVerbatim || hasFlops || hasArrays || {
    desc.instances exists { decl =>
      details(decl.symbol.kind.asEntity.symbol).needsClock
    }
  }

  lazy val needsReset: Boolean = isVerbatim || resetFlops.nonEmpty || {
    desc.instances exists { decl =>
      details(decl.symbol.kind.asEntity.symbol).needsReset
    }
  }

  // Any symbol that is driven by a connect must be a net
  lazy val netSymbols: List[Symbol] = desc.connects flatMap {
    case EntConnect(_, rhs :: Nil) => rhs collect { case ExprSym(symbol) => symbol }
    case _                         => Nil
  }

  // Group and sort interconnect symbols by instance, then by port declaration order
  lazy val groupedInterconnectSymbols: List[(Symbol, List[Symbol])] = {
    // Calculate (instance symbol, port name, interconnect symbol) triplets
    val trip = for {
      Decl(Sym(nSymbol, _), _) <- desc.decls
      (iSymbol, sel) <- nSymbol.attr.interconnect.get
    } yield {
      (iSymbol, sel, nSymbol)
    }

    // Group by instance, loose instance symbol from values
    val groups = trip.groupMap { _._1 } { case (_, s, n) => (s, n) }

    // Sort by groups by instance order
    val sortedInstances = {
      // Sorting map for instance symbols
      val ordering = Map from {
        for {
          (decl, i) <- desc.instances.iterator.zipWithIndex
        } yield {
          decl.symbol -> i
        }
      }
      // Sort by instance
      groups.toList sortBy { case (i, _) => ordering(i) }
    }

    // Sort within group by port definition order
    sortedInstances map {
      case (iSymbol, list) =>
        // Sorting map for port selectors
        val ordering = Map from {
          for {
            (symbol, i) <- iSymbol.kind.asEntity.publicSymbols.iterator.zipWithIndex
          } yield {
            symbol.name -> i
          }
        }
        // Sort by port selector, then loose them, note that some interconnect
        // symbols can remain as placeholders in concatenations while their
        // corresponding ports have ben removed. We put these at the end sorted
        // lexically.
        val sortedSymbols = list sortWith {
          case ((a, _), (b, _)) =>
            (ordering.get(a), ordering.get(b)) match {
              case (Some(oa), Some(ob)) => oa < ob
              case (Some(_), None)      => true
              case (None, Some(_))      => false
              case (None, None)         => a < b
            }
        } map { _._2 }
        (iSymbol, sortedSymbols)
    }
  }

  // Function from 'instance symbol => port selector => connected expression'
  lazy val instancePortExpr: Map[Symbol, Map[String, Expr]] = {
    val trip = desc.connects collect {
      case EntConnect(InstancePortRef(iSymbol, pSymbol), rhs :: Nil) =>
        (iSymbol, pSymbol.name, rhs)
      case EntConnect(lhs, List(InstancePortRef(iSymbol, pSymbol))) =>
        (iSymbol, pSymbol.name, lhs)
    }

    val grouped = trip.groupMap({ _._1 })({ case (_, s, e) => (s, e) })

    Map from {
      grouped.view mapValues { pairs =>
        pairs.toMap ensuring { _.size == pairs.length }
      }
    }
  }

  // Connects that are not of the form 'a.b -> SOMETHING' or 'SOMETHING -> a.b'
  // where a is an instance
  lazy val nonPortConnects: List[EntConnect] = desc.connects filter {
    case EntConnect(InstancePortRef(_, _), _)       => false
    case EntConnect(_, List(InstancePortRef(_, _))) => false
    case _                                          => true
  }

}
