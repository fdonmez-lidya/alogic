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
// Collection of all symbol attributes
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.core

import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.Symbols._
import com.argondesign.alogic.core.Types.TypeEntity

class SymbolAttributes {
  // Symbol is meant to be unused, do not warn
  val unused = new Attribute[Boolean]()

  // The variant flavour of this entity (e.g: fsm/network/verbatim)
  val variant = new Attribute[String]()
  // Is this a toplevel entity
  val topLevel = new Attribute[Boolean]()
  // Is this an entry point function
  val entry = new Attribute[Boolean]()

  // Entity call stack limit
  val stackLimit = new Attribute[Expr]()
  // Function recursion limit
  val recLimit = new Attribute[Expr]()
  // The return stack symbol, if this is an entity
  val returnStack = new Attribute[Symbol]()
  // The state variable symbol, if this is an entity
  val stateVar = new Attribute[Symbol]()

  // Is this a FlowControlTypeNone port?
  val fcn = new Attribute[Boolean]()
  // If this is a FlowControlTypeValid port,
  // the corresponding payload and valid symbols
  val fcv = new Attribute[(Option[Symbol], Symbol)]()
  // If this is a FlowControlTypeReady port,
  // the corresponding payload, valid and ready symbols
  val fcr = new Attribute[(Option[Symbol], Symbol, Symbol)]()
  // If this is a FlowControlTypeAccept port,
  // the corresponding payload, valid and accept symbols
  val fca = new Attribute[(Option[Symbol], Symbol, Symbol)]()
  // Is this a port that has been expanded to multiple signals?
  val expandedPort = new Attribute[Boolean]()

  // If this is an entity symbol, then the type it was before
  // flow control lowering and structure splitting (i.e.: with the high
  // level interface), without the TypeType wrapper
  val highLevelKind = new Attribute[TypeEntity]()

  // If the state system stalls, set this signal to all zeros
  val clearOnStall = new Attribute[Boolean]()
  // If this is an entity symbol, then these are further (instance, portname)
  // pairs (driven from the state system) that need to be cleared on a stall
  val interconnectClearOnStall = new Attribute[List[(Symbol, String)]]()

  // If the value of ExprSym(symbol) in this attribute is 0,
  // then the value of this signal is known to be don't care
  val dontCareUnless = new Attribute[Symbol]()

  // Describes implication relationship between this symbol and the denoted
  // symbols. Both this symbol and the implied symbols must be 1 bit. There
  // are 2 further booleans attached. The first boolean denotes the state
  // of this, and the second boolean denotes the states of the attached symbol.
  // For example, an attribute (true, true, foo) means "this |-> foo",
  // (false, true, foo) means "~this |-> foo", and (true, false, foo) means
  // "this |-> ~foo"
  val implications = new Attribute[List[(Boolean, Boolean, Symbol)]]()

  // The output register symbol if this is a registered output port
  val oReg = new Attribute[Symbol]()

  // If this is flop _q symbol, the corresponding _d symbol
  val flop = new Attribute[Symbol]()

  // If this is a memory _q symbol, the corresponding we, waddr and wdata symbols
  val memory = new Attribute[(Symbol, Symbol, Symbol)]()

  // If this is an interconnect signal, the corresponding instance symbol and port name
  val interconnect = new Attribute[(Symbol, String)]()

  // If this signal is a combinatorically driven local signal
  val combSignal = new Attribute[Boolean]()

  // The expanded field symbols of a struct symbol
  val fieldSymbols = new Attribute[List[Symbol]]()
  // The struct symbol if this symbol was split from a struct
  val structSymbol = new Attribute[Symbol]()
  // The field offset if this symbol was split from a struct
  val fieldOffset = new Attribute[Int]()

  // The default value of this symbol, if required
  val default = new Attribute[Expr]()

  // Is this an SRAM entity?
  val sram = new Attribute[Boolean]()

  // Denotes that SRAM instances should be lifted from the hierarchy below this entity
  val liftSrams = new Attribute[Boolean]()

  // Name of this symbol as declared in source, with dictionary index values
  val sourceName = new Attribute[(String, List[BigInt])]

  // Whether this choice has been generated
  val wasParam = new Attribute[Boolean]()

  // Iterator that enumerates all fields above
  private def attrIterator = Iterator(
    unused,
    variant,
    topLevel,
    entry,
    stackLimit,
    recLimit,
    returnStack,
    stateVar,
    fcn,
    fcv,
    fcr,
    fca,
    expandedPort,
    highLevelKind,
    clearOnStall,
    interconnectClearOnStall,
    dontCareUnless,
    implications,
    oReg,
    flop,
    memory,
    interconnect,
    combSignal,
    fieldSymbols,
    structSymbol,
    fieldOffset,
    default,
    sram,
    liftSrams,
    sourceName,
    wasParam
  )

  // Iterator that enumerates names of fields above
  private def nameIterator = Iterator(
    "unused",
    "variant",
    "topLevel",
    "entry",
    "stackLimit",
    "recLimit",
    "returnStack",
    "stateVar",
    "fcn",
    "fcv",
    "fcr",
    "fca",
    "expandedPort",
    "highLevelKind",
    "clearOnStall",
    "interconnectClearOnStall",
    "dontCareUnless",
    "implications",
    "oReg",
    "flop",
    "memory",
    "interconnect",
    "combSignal",
    "fieldSymbols",
    "structSymbol",
    "fieldOffset",
    "default",
    "sram",
    "liftSrams",
    "sourceName",
    "wasParam"
  )

  // Copy values of attributes from another instance
  def update(that: SymbolAttributes): Unit = {
    for ((a, b) <- attrIterator zip that.attrIterator) {
      a.asInstanceOf[Attribute[Any]] update b.asInstanceOf[Attribute[Any]]
    }
  }

  // Copy values from source attributes
  def update(attr: scala.collection.Map[String, Expr])(implicit cc: CompilerContext): Unit =
    for ((name, expr) <- attr) {
      name match {
        case "unused"     => unused set true
        case "stacklimit" => stackLimit set expr
        case "reclimit"   => recLimit set expr
        case "toplevel"   => topLevel set true
        case "liftsrams"  => liftSrams set true
        case _            => cc.error(expr, s"Unknown attribute '$name'")
      }
    }

  // Render in some human readable form
  def toSource(implicit cc: CompilerContext): String = {
    val parts = for ((name, attr) <- nameIterator zip attrIterator if attr.isSet) yield {
      attr.value match {
        case true       => s"${name}"
        case false      => s"!${name}"
        case expr: Expr => s"${name} = ${expr.toSource}"
        case other      => s"${name} = ${other.toString}"
      }
    }
    if (parts.nonEmpty) parts.mkString("(* ", ", ", " *)") else ""
  }
}
