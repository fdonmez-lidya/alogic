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
// The Namer:
// - Constructs types and symbols for definitions
// - Resolves identifiers to symbols
// - Converts EntityIdent to EntityNamed
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Loc
import com.argondesign.alogic.core.Symbols.Symbol
import com.argondesign.alogic.core.Types.TypeChoice
import com.argondesign.alogic.core.enums.EntityVariant
import com.argondesign.alogic.lib.TreeLike
import com.argondesign.alogic.util.unreachable

import scala.annotation.tailrec
import scala.collection.mutable

final class Namer(implicit cc: CompilerContext) extends TreeTransformer { namer =>

  override val typed: Boolean = false
  override val checkDefs: Boolean = false

  private[this] var stmtLevel = 0
  private[this] val stmtSymbols = mutable.Set[Symbol]()

  final private[this] object Scopes {

    private val choiceSymbols = mutable.Set[Symbol]()

    private class SymTab(val genIf: Boolean, val genLoop: Boolean) {
      val tab: mutable.LinkedHashMap[String, Symbol] = mutable.LinkedHashMap()
      val extraSymbols: mutable.ListBuffer[Symbol] = mutable.ListBuffer()
    }

    private val scopes = mutable.Stack[SymTab]()

    private def current: SymTab = scopes.head

    def push(genIf: Boolean = false, genLoop: Boolean = false): Unit =
      scopes.push(new SymTab(genIf, genLoop))

    // Pop the current lexical scope. Return the list of extra symbols whose
    // definition needs to be inserted into the scope being popped
    def pop(): List[Symbol] =
      scopes.headOption map { finished =>
        scopes.pop()

        if (finished.genIf || finished.genLoop) {
          // Add symbols to the outer choice symbol. This will only exists if the
          // name needs to escape the scope.
          for {
            (name, symbol) <- finished.tab
            // If we finished a gen loop, step past the header scope
            outerScope <- (if (finished.genLoop) scopes drop 1 else scopes).headOption
            // Get the choice symbol
            choiceSymbol <- outerScope.tab.get(name)
          } {
            assert(choiceSymbols contains choiceSymbol)
            choiceSymbol.kind = TypeChoice(symbol :: choiceSymbol.kind.asChoice.symbols)
          }
        }

        finished.extraSymbols.toList
      } getOrElse Nil

    // Lookup name in symbol table
    def lookup(name: String): Option[Symbol] = {
      @tailrec
      def loop(name: String, scopes: mutable.Stack[SymTab]): Option[Symbol] = scopes match {
        case s +: ss =>
          s.tab.get(name) match {
            case opt @ Some(_) => opt
            case None          => loop(name, ss)
          }
        case _ => cc.globalScope.get(name)
      }
      loop(name, scopes)
    }

    // Insert Symbol into current scope as appropriate
    def insert[T <: Symbol](ident: Ident, asChoice: Boolean): Unit = {
      val name = ident.name

      current.tab.get(name) pipe {
        case Some(oldSymbol) =>
          // Inserting duplicate name - only error if not duplicate choice symbol
          if (!(asChoice && (choiceSymbols contains oldSymbol))) {
            cc.error(
              ident,
              s"Redefinition of '$name' with previous definition at",
              oldSymbol.loc.prefix
            )
          }
          // Don't replace the existing symbol
          None
        case None =>
          // Create the new symbol
          Some(cc.newSymbol(ident))
      } foreach { newSymbol =>
        // Bookkeeping for various situations
        if (asChoice) {
          choiceSymbols add newSymbol
          newSymbol.kind = TypeChoice(Nil)
          current.extraSymbols append newSymbol
        }
        if (stmtLevel > 0) {
          stmtSymbols add newSymbol
        }

        // Warn about name hiding - TODO: This needs to be more selective
        if (stmtLevel > 0) {
          lookup(name) filterNot choiceSymbols filter {
            _.loc.start < newSymbol.loc.start
          } foreach { oldSymbol =>
            cc.warning(
              newSymbol.loc,
              s"Definition of '$name' hides previous definition at",
              oldSymbol.loc.prefix
            )
          }
        }

        // Insert into the actual symbol table
        current.tab(name) = newSymbol
      }
    }

    def dictCreateAllowed: Boolean = scopes.head.genLoop

    def finalCheck(): Unit = {
      assert(scopes.isEmpty)
    }
  }

  private[this] def lookup(loc: Loc, name: String): Option[Symbol] = {
    Scopes.lookup(name) tap {
      case None    => cc.error(loc, s"'$name' is not defined")
      case Some(_) =>
    }
  }

  private[this] def lookup(ident: Ident): Option[Symbol] = lookup(ident.loc, ident.name)

  private[this] val swapScope = mutable.Stack[(List[Tree], Boolean)]()
  private[this] val extraThenSymbolsStack = mutable.Stack[List[Symbol]]()

  private[this] var pushScope: Option[(List[Tree], Boolean)] = None

  // Insert names early so they can be referred to before the definition site in source
  private[this] def insertDecls(trees: List[Tree]): Unit = {
    def insertDecl(decl: Decl, asChoice: Boolean, dictOnly: Boolean): Unit = {
      val ident = decl.ref.asInstanceOf[Ident]
      if (!dictOnly || ident.idxs.nonEmpty) {
        Scopes.insert(ident, asChoice)
      }
    }

    def insertGen(gen: Gen, dictOnly: Boolean): Unit = gen match {
      case GenIf(_, thenItems, elseItems) =>
        insertTrees(thenItems, asChoice = true, dictOnly = dictOnly)
        insertTrees(elseItems, asChoice = true, dictOnly = dictOnly)
      case GenFor(_, _, _, body)   => insertTrees(body, asChoice = true, dictOnly = true)
      case GenRange(_, _, _, body) => insertTrees(body, asChoice = true, dictOnly = true)
    }

    def insertTrees(trees: List[Tree], asChoice: Boolean, dictOnly: Boolean): Unit = {
      trees foreach {
        case decl: Decl     => insertDecl(decl, asChoice, dictOnly)
        case EntDecl(decl)  => insertDecl(decl, asChoice, dictOnly)
        case RecDecl(decl)  => insertDecl(decl, asChoice, dictOnly)
        case StmtDecl(decl) => insertDecl(decl, asChoice, dictOnly)
        case RizDecl(decl) if !(cc.globalScope contains decl.name) =>
          assert(!asChoice)
          assert(!dictOnly)
          insertDecl(decl, false, false)
        case gen: Gen     => insertGen(gen, dictOnly)
        case EntGen(gen)  => insertGen(gen, dictOnly)
        case RecGen(gen)  => insertGen(gen, dictOnly)
        case StmtGen(gen) => insertGen(gen, dictOnly)
        case _            => Nil
      }
    }

    insertTrees(trees, asChoice = false, dictOnly = false)
  }

  override def enter(tree: Tree): Unit = {
    // Push extra scope where required
    if (pushScope map { _._1.head.id } contains tree.id) {
      val (body, inGen) = pushScope.get
      pushScope = None
      Scopes.push(genLoop = inGen)
      insertDecls(body)
    }

    // Replace current scope where required
    if (swapScope.headOption map { _._1.head.id } contains tree.id) {
      extraThenSymbolsStack push Scopes.pop()
      val (body, inGen) = swapScope.pop()
      Scopes.push(genIf = inGen)
      insertDecls(body)
    }

    if (tree.isInstanceOf[Stmt]) {
      stmtLevel += 1
    }

    tree match {
      case Root(body) =>
        // Push root scope
        Scopes.push()
        // Insert local declarations
        insertDecls(body)

      case Decl(ident: Ident, _) =>
        // Check dict ident creation is allowed
        if (ident.idxs.nonEmpty && !Scopes.dictCreateAllowed) {
          cc.error(
            tree,
            s"Definition with dictionary identifier must appear directly in 'gen' loop scope."
          )
        }
        // Name the source attributes
        ident.attr mapValuesInPlace { case (_, v) => walk(v).asInstanceOf[Expr] }

      case desc: Desc =>
        // Push the new scope
        Scopes.push()
        // Insert decls
        desc match {
          case DescEntity(_, body)        => insertDecls(body)
          case DescSingleton(_, body)     => insertDecls(body)
          case DescRecord(body)           => insertDecls(body)
          case DescFunc(_, _, args, body) => insertDecls(args); insertDecls(body)
          case _                          =>
        }

      case GenFor(inits, _, _, body) =>
        Scopes.push()
        insertDecls(inits)
        if (body.nonEmpty) {
          pushScope = Some((body, true))
        }

      case GenRange(decl, _, _, body) =>
        Scopes.push()
        insertDecls(List(decl))
        if (body.nonEmpty) {
          pushScope = Some((body, true))
        }

      case GenIf(_, thenItems, elseItems) =>
        Scopes.push(genIf = true)
        insertDecls(thenItems)
        if (elseItems.nonEmpty) {
          swapScope.push((elseItems, true))
        }

      case EntCombProcess(body) =>
        Scopes.push()
        insertDecls(body)

      case StmtBlock(body) =>
        Scopes.push()
        insertDecls(body)

      case StmtLet(inits, body) =>
        Scopes.push()
        insertDecls(inits)
        if (body.nonEmpty) {
          pushScope = Some((body, false))
        }

      case StmtLoop(body) =>
        Scopes.push()
        insertDecls(body)

      case StmtDo(_, body) =>
        Scopes.push()
        insertDecls(body)

      case StmtWhile(_, body) =>
        Scopes.push()
        insertDecls(body)

      case StmtFor(inits, _, _, body) =>
        Scopes.push()
        insertDecls(inits)
        if (body.nonEmpty) {
          pushScope = Some((body, false))
        }

      case StmtIf(_, thenStmts, elseStmts) =>
        Scopes.push()
        insertDecls(thenStmts)
        if (elseStmts.nonEmpty) {
          swapScope.push((elseStmts, false))
        }

      case CaseRegular(_, body) =>
        Scopes.push()
        insertDecls(body)

      case CaseDefault(body) =>
        Scopes.push()
        insertDecls(body)

      case _: CaseGen =>
        Scopes.push()

      case _ => ()
    }
  }

  def mkDecls[T <: Tree](symbols: List[Symbol], wrap: Decl => T): List[T] = symbols map { symbol =>
    wrap(symbol.decl) tap {
      _.preOrderIterator foreach {
        case t: Tree => t withLoc symbol.loc
        case _       =>
      }
    }
  }

  override def transform(tree: Tree): Tree = {
    val result = tree match {
      case _: Root =>
        Scopes.pop() ensuring { _.isEmpty }
        tree

      case decl @ Decl(ident: Ident, desc) =>
        // Lookup symbol (inserted in enter)
        val symbol = lookup(ident).get

        // Update symbol attributes with named ident attributes
        symbol.attr update ident.attr

        // Behaviour specific to particular definitions - TODO: shouldn't really be in the Namer
        desc match {
          // Always lift SRAMs in verbatim entities
          case DescEntity(EntityVariant.Ver, _)    => symbol.attr.liftSrams set true
          case DescSingleton(EntityVariant.Ver, _) => symbol.attr.liftSrams set true
          // Mark main function as an entry point
          case _: DescFunc if ident.name == "main" => symbol.attr.entry set true
          //
          case _ =>
        }

        // Rewrite node with Sym as ref
        decl.copy(ref = Sym(symbol, ident.idxs) withLoc ident.loc) withLoc tree.loc

      case desc: Desc =>
        // Pop the desc scope
        val extraSymbols = Scopes.pop()

        if (extraSymbols.isEmpty) {
          tree
        } else {
          desc match {
            case d: DescEntity =>
              d.copy(body = d.body ::: mkDecls(extraSymbols, EntDecl)) withLoc d.loc
            case d: DescRecord =>
              d.copy(body = d.body ::: mkDecls(extraSymbols, RecDecl)) withLoc d.loc
            case d: DescSingleton =>
              d.copy(body = d.body ::: mkDecls(extraSymbols, EntDecl)) withLoc d.loc
            case d: DescFunc =>
              d.copy(body = d.body ::: mkDecls(extraSymbols, StmtDecl)) withLoc d.loc
            case _ => unreachable
          }
        }

      case gen @ GenFor(_, _, _, body) =>
        val extraSymbols = if (body.nonEmpty) Scopes.pop() else Nil
        val extraItems = mkDecls(extraSymbols, identity)
        // Pop the header scope
        Scopes.pop() ensuring { _.isEmpty }
        if (extraItems.isEmpty) {
          tree
        } else {
          gen.copy(body = body ::: extraItems) withLoc gen.loc
        }

      case gen @ GenRange(_, _, _, body) =>
        val extraSymbols = if (body.nonEmpty) Scopes.pop() else Nil
        val extraItems = mkDecls(extraSymbols, identity)
        // Pop the header scope
        Scopes.pop() ensuring { _.isEmpty }
        if (extraItems.isEmpty) {
          tree
        } else {
          gen.copy(body = body ::: extraItems) withLoc gen.loc
        }

      case gen @ GenIf(_, thenItems, elseItems) =>
        val extraThenSymbols = if (elseItems.isEmpty) Scopes.pop() else extraThenSymbolsStack.pop()
        val extraElseSymbols = if (elseItems.isEmpty) Nil else Scopes.pop()
        val extraThenItems = mkDecls(extraThenSymbols, identity)
        val extraElseItems = mkDecls(extraElseSymbols, identity)
        if (extraThenItems.isEmpty && extraElseItems.isEmpty) {
          tree
        } else {
          gen.copy(
            thenItems = thenItems ::: extraThenItems,
            elseItems = elseItems ::: extraElseItems
          ) withLoc gen.loc
        }

      case ent @ EntCombProcess(stmts) =>
        val extraSymbols = Scopes.pop()
        val extraStmts = mkDecls(extraSymbols, StmtDecl)
        if (extraStmts.isEmpty) {
          tree
        } else {
          ent.copy(stmts = stmts ::: extraStmts) withLoc ent.loc
        }

      case stmt @ StmtBlock(body) =>
        val extraSymbols = Scopes.pop()
        val extraStmts = mkDecls(extraSymbols, StmtDecl)
        if (extraStmts.isEmpty) {
          tree
        } else {
          stmt.copy(body = body ::: extraStmts) withLoc stmt.loc
        }

      case stmt @ StmtLet(_, body) =>
        val extraSymbols = if (body.nonEmpty) Scopes.pop() else Nil
        val extraStmts = mkDecls(extraSymbols, StmtDecl)
        // Pop the header scope
        Scopes.pop() ensuring { _.isEmpty }
        if (extraStmts.isEmpty) {
          tree
        } else {
          stmt.copy(body = body ::: extraStmts) withLoc stmt.loc
        }

      case stmt @ StmtLoop(body) =>
        val extraSymbols = Scopes.pop()
        val extraStmts = mkDecls(extraSymbols, StmtDecl)
        if (extraStmts.isEmpty) {
          tree
        } else {
          stmt.copy(body = body ::: extraStmts) withLoc stmt.loc
        }

      case stmt @ StmtDo(_, body) =>
        val extraSymbols = Scopes.pop()
        val extraStmts = mkDecls(extraSymbols, StmtDecl)
        if (extraStmts.isEmpty) {
          tree
        } else {
          stmt.copy(body = body ::: extraStmts) withLoc stmt.loc
        }

      case stmt @ StmtWhile(_, body) =>
        val extraSymbols = Scopes.pop()
        val extraStmts = mkDecls(extraSymbols, StmtDecl)
        if (extraStmts.isEmpty) {
          tree
        } else {
          stmt.copy(body = body ::: extraStmts) withLoc stmt.loc
        }

      case stmt @ StmtFor(_, _, _, body) =>
        val extraSymbols = if (body.nonEmpty) Scopes.pop() else Nil
        val extraStmts = mkDecls(extraSymbols, StmtDecl)
        // Pop the header scope
        Scopes.pop() ensuring { _.isEmpty }
        if (extraStmts.isEmpty) {
          tree
        } else {
          stmt.copy(body = body ::: extraStmts) withLoc stmt.loc
        }

      case stmt @ StmtIf(_, thenStmts, elseStmts) =>
        val extraThenSymbols = if (elseStmts.isEmpty) Scopes.pop() else extraThenSymbolsStack.pop()
        val extraElseSymbols = if (elseStmts.isEmpty) Nil else Scopes.pop()
        val extraThenStmts = mkDecls(extraThenSymbols, StmtDecl)
        val extraElseStmts = mkDecls(extraElseSymbols, StmtDecl)
        if (extraThenStmts.isEmpty && extraElseStmts.isEmpty) {
          tree
        } else {
          stmt.copy(
            thenStmts = thenStmts ::: extraThenStmts,
            elseStmts = elseStmts ::: extraElseStmts
          ) withLoc stmt.loc
        }

      case kase @ CaseRegular(_, stmts) =>
        val extraSymbols = Scopes.pop()
        val extraStmts = mkDecls(extraSymbols, StmtDecl)
        if (extraStmts.isEmpty) {
          tree
        } else {
          kase.copy(stmts = stmts ::: extraStmts) withLoc kase.loc
        }

      case kase @ CaseDefault(stmts) =>
        val extraSymbols = Scopes.pop()
        val extraStmts = mkDecls(extraSymbols, StmtDecl)
        if (extraStmts.isEmpty) {
          tree
        } else {
          kase.copy(stmts = stmts ::: extraStmts) withLoc kase.loc
        }

      case _: CaseGen =>
        Scopes.pop() ensuring { _.isEmpty }
        tree

      ////////////////////////////////////////////////////////////////////////////
      // Resolve references
      ////////////////////////////////////////////////////////////////////////////

      case ExprRef(ident @ Ident(name, idxs)) =>
        // Lookup symbol
        lookup(tree.loc, name) match {
          case Some(symbol) =>
            // Check use before definition in statements
            if (stmtLevel > 0 && (stmtSymbols contains symbol) && symbol.loc.start > tree.loc.start) {
              cc.error(tree, s"'$name' used before it is defined")
            }
            // Rewrite node
            if (idxs.isEmpty) {
              ExprSym(symbol) withLoc tree.loc
            } else {
              ExprRef(Sym(symbol, idxs) withLoc ident.loc) withLoc tree.loc
            }
          case None => ExprError() withLoc tree.loc
        }

      ////////////////////////////////////////////////////////////////////////////
      // Done
      ////////////////////////////////////////////////////////////////////////////

      case _ => tree
    }

    if (tree.isInstanceOf[Stmt]) {
      stmtLevel -= 1
    }

    result
  }

  override def finalCheck(tree: Tree): Unit = {
    Scopes.finalCheck()

    assert(stmtLevel == 0)
    assert(swapScope.isEmpty)
    assert(pushScope.isEmpty)
    assert(extraThenSymbolsStack.isEmpty)

    // Check tree does not contain any Ident related nodes anymore
    def check(tree: TreeLike): Unit = {
      tree visitAll {
        case node: Ident                 => cc.ice(node, "Ident remains")
        case node @ ExprRef(Sym(_, Nil)) => cc.ice(node, "ExprRef(Sym(_, Nil))")
      }
    }

    check(tree)
  }

}

object Namer extends TreeTransformerPass {
  val name = "namer"
  def create(implicit cc: CompilerContext) = new Namer
}
