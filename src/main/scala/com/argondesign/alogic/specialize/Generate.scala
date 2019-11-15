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
// Process 'gen' constructs in all unparametrized decls
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.specialize

import com.argondesign.alogic.analysis.StaticEvaluation
import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.Bindings
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.FuncVariant
import com.argondesign.alogic.core.Loc
import com.argondesign.alogic.core.Symbols._
import com.argondesign.alogic.typer.TypeAssigner
import com.argondesign.alogic.util.BigIntOps._
import com.argondesign.alogic.util.unreachable

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

private[specialize] object Generate {

  // Type class used for handling context specific processing of generate
  private trait Generatable[T <: Tree] {
    // String describing what kind of content a generate needs to yield
    val description: String
    // Predicate indicating whether this tree is valid generate content in this context
    def isValid(tree: Tree): Boolean
    // Transform generate content to expected content
    def splice(tree: Tree): T
  }

  // Type class instance for Ent
  private implicit object generatableEnt extends Generatable[Ent] {
    val description = "entity content"
    def isValid(tree: Tree): Boolean = tree match {
      case _: Gen  => true
      case _: Ent  => true
      case _: Decl => true
      case _       => false
    }
    def splice(tree: Tree): Ent = tree match {
      case gen: Gen => EntGen(gen) withLoc gen.loc
      case ent: Ent => ent
      case decl @ Decl(_, desc: DescFunc) =>
        assert(desc.variant == FuncVariant.None)
        val newDesc = desc.copy(variant = FuncVariant.Comb) withLoc desc.loc
        val newDecl = decl.copy(desc = newDesc) withLoc decl.loc
        EntDecl(newDecl) withLoc decl.loc
      case decl: Decl => EntDecl(decl) withLoc decl.loc
      case _          => unreachable
    }
  }

  // Type class instance for Stmt
  private implicit object generatableStmt extends Generatable[Stmt] {
    val description = "statement"
    def isValid(tree: Tree): Boolean = tree match {
      case _: Gen  => true
      case _: Stmt => true
      case _: Decl => true
      case _       => false
    }
    def splice(tree: Tree): Stmt = tree match {
      case gen: Gen   => StmtGen(gen) withLoc gen.loc
      case stmt: Stmt => stmt
      case decl: Decl => StmtDecl(decl) withLoc decl.loc
      case _          => unreachable
    }
  }

  // Type class instance for Case
  private implicit object generatableCase extends Generatable[Case] {
    val description = "case clause"
    def isValid(tree: Tree): Boolean = tree match {
      case _: Gen  => true
      case _: Case => true
      case _       => false
    }
    def splice(tree: Tree): Case = tree match {
      case gen: Gen   => CaseGen(gen) withLoc gen.loc
      case kase: Case => kase
      case _          => unreachable
    }
  }

  def values(idxs: List[Expr])(implicit cc: CompilerContext): Option[List[BigInt]] = idxs match {
    case Nil => Some(Nil)
    case head :: tail =>
      val resOpt = values(tail) // Compute eagerly to emit all errors
      head.value match {
        case Some(value) => resOpt map { value :: _ }
        case None        => cc.error(head, "Identifier index must be a compile time constant"); None
      }
  }

  def apply(decl: Decl)(implicit cc: CompilerContext): Option[Decl] = {
    assert(!decl.desc.isParametrized)
    assert(decl.ref.asInstanceOf[Sym].idxs.isEmpty)

    // Whether this choice has been generated
    val validChoices = mutable.Set[Symbol]()

    // Resolution of dictionary symbols: 'dict symbol' -> 'indices' -> 'result'
    val dictResolutions = mutable.Map[Symbol, mutable.Map[List[BigInt], Symbol]]()

    final class Process[T <: Tree](
        // Bindings for symbols with known values (gen variables)
        bindings: Bindings,
        // The symbols already cloned externally (generated symbols that are used outside)
        newSymbols: Map[Symbol, Symbol],
        // ????
        initialEntityLevel: Int
    )(
        implicit cc: CompilerContext
    ) extends TreeTransformer {
      assert(initialEntityLevel == 0) // >????

      override val typed: Boolean = false
      override val checkRefs: Boolean = false

      // The cloned symbol map
      private val symbolMap = mutable.Map from newSymbols

      // Latch errors
      var hadError = false

      private[this] def error(loc: Loc, msg: String*): Unit = {
        cc.error(loc, msg: _*)
        hadError = true
      }

      private[this] def error(tree: Tree, msg: String*): Unit = error(tree.loc, msg: _*)

      // Clone the symbols defined in the scope of this tree
      private def cloneSymbols(tree: Tree): List[(Symbol, Symbol)] = {
        def stmtDecls(stmts: List[Stmt]): List[Decl] = stmts collect {
          case StmtDecl(decl) => decl
        }

        val decls = tree match {
          case desc: DescEntity                => desc.decls
          case desc: DescRecord                => desc.decls
          case desc: DescSingleton             => desc.decls
          case desc: DescFunc                  => desc.decls
          case EntCombProcess(stmts)           => stmtDecls(stmts)
          case StmtBlock(body)                 => stmtDecls(body)
          case StmtIf(_, thenStmts, elseStmts) => stmtDecls(thenStmts) ::: stmtDecls(elseStmts)
          case StmtLoop(body)                  => stmtDecls(body)
          case StmtWhile(_, body)              => stmtDecls(body)
          case StmtFor(inits, _, _, body)      => stmtDecls(inits) ::: stmtDecls(body)
          case StmtDo(_, body)                 => stmtDecls(body)
          case StmtLet(inits, body)            => stmtDecls(inits) ::: stmtDecls(body)
          case CaseRegular(_, stmts)           => stmtDecls(stmts)
          case CaseDefault(stmts)              => stmtDecls(stmts)
          case _                               => Nil
        }

        cloneSymbolsInDecls(decls, bindings, "")
      }

      private def cloneSymbolsInDecls(
          decls: List[Decl],
          bindings: Bindings,
          suffix: String
      ): List[(Symbol, Symbol)] = decls flatMap {
        // Scalar symbols
        case Decl(Sym(symbol, Nil), desc) =>
          symbolMap.get(symbol) match {
            // A scalar symbol may already be cloned if referenced by an outer
            // DescChoice. We just need to mark it valid at this point.
            case Some(cloneSymbol) =>
              // This choice will now be active, so mark as such
              validChoices add cloneSymbol
              // Rename the clone by appending the suffix
              cloneSymbol.name = cloneSymbol.name + suffix
              // Already in the symbol map, no need to add it
              Nil

            // If a scalar symbol was not already cloned, we must clone it
            case None =>
              // Clone the symbol
              val newSymbol = symbol.dup
              // Rename the clone by appending the suffix
              newSymbol.name = newSymbol.name + suffix
              // If this is a choice symbol, recursively clone all referenced
              // choices as well. We clone recursively to ensure only one
              // clone exists, even if a referenced choice is inside a loop.
              def choiceClones(desc: Desc): List[(Symbol, Symbol)] = desc match {
                case DescChoice(choices) =>
                  choices flatMap {
                    case ExprSym(choice) =>
                      // These could not have been seen before,
                      assert(!(symbolMap contains choice))
                      (choice -> choice.dup) :: choiceClones(choice.decl.desc)
                  }
                case _ => Nil
              }
              // Add this clone and the choice clones (if any)
              (symbol -> newSymbol) :: choiceClones(desc)
          }

        // Dict symbols
        case Decl(sym @ Sym(symbol, idxs), desc) =>
          // Choice symbols are never dict
          assert(!desc.isInstanceOf[DescChoice])
          // At this point the indices must be known, or it's an error
          values(idxs map { _ given bindings }) match {
            case None =>
              hadError = true
              Nil
            case Some(idxValues) =>
              // Dict symbols will have always have been cloned as they can only
              // be defined in a 'gen' loop, and they are always injected into the
              // enclosing scope via a choice symbol, so just get the clone.
              val dictSymbol = symbolMap(symbol)

              // We will now have at least one instance of the dict decl,
              // so mark the dictSymbol as a valid choice
              validChoices add dictSymbol

              // Clone the symbol, this is the specific instance
              val newSymbol = symbol.dup

              // Rename based on value of indices
              newSymbol.name = idxValues.mkString(symbol.name + cc.sep, "_", "")

              // Set the attribute used ot resolve external dict references
              newSymbol.attr.sourceName.set((symbol.name, idxValues))

              // Add to dictResolutions, error if already exists
              dictResolutions
                .getOrElseUpdate(dictSymbol, mutable.Map())
                .put(idxValues, newSymbol) match {
                case Some(_) =>
                  val srcName = idxValues.mkString(symbol.name + "#[", ", ", "]")
                  error(sym, s"'$srcName' defined multiple times after processing 'gen' constructs")
                case None => // OK, first definition with these indices
              }

              // The dict clone is already in the symbolMap, no need to add it
              Nil
          }

        // None of these exist at this point
        case Decl(_: Ident, _) => unreachable
      }

      // Compute the generated tree from generate
      private def generate[U <: Tree: Generatable](gen: Gen): Option[List[Tree]] = {
        val dispatcher: Generatable[U] = implicitly[Generatable[U]]

        def process(bindings: Bindings, trees: List[Tree]): List[Tree] = {
          // Check for 'gen' content invalid in this context
          val (valid, invalid) = trees partition dispatcher.isValid

          // Issue error for any invalid contents
          invalid foreach { t =>
            error(
              t,
              s"'gen' construct yields invalid syntax, ${dispatcher.description} is expected (${t.toString})")
          }

          // Gather definitions in the 'gen' scope
          val decls = valid collect { case decl: Decl => decl }

          // Clone symbols introduced in the scope of this Gen, and build the new
          // starting symbol map. Rename cloned scalar symbols based on bindins.
          val sm = {
            val suffix = if (bindings.isEmpty) {
              ""
            } else {
              bindings.toList sortBy {
                _._1.loc.start
              } map {
                case (symbol, expr) => s"${symbol.name}_${expr.value.get}"
              } mkString (cc.sep, cc.sep, "")
            }

            Map from {
              symbolMap.iterator concat cloneSymbolsInDecls(decls, bindings, suffix)
            }
          }

          // Create the recursive Generate transform
          val transform = new Process(bindings, sm, parametrizedLevel)

          // Recursively process valid trees, then splice them
          val results = valid map dispatcher.splice map transform

          // Propagate errors
          hadError |= transform.hadError

          // Flatten thickets
          results flatMap {
            case Thicket(ts) => ts
            case tree        => List(tree)
          }
        }

        def generateFor(bindings: Bindings,
                        terminate: Bindings => Option[Boolean],
                        loc: Loc,
                        body: List[Tree],
                        step: Stmt): List[Tree] = {
          val buf = new ListBuffer[Tree]

          @tailrec
          def loop(bindings: Bindings): Unit = terminate(bindings) match {
            case None => error(loc, "Condition of 'gen for' is not a compile time constant")
            case Some(false) =>
              buf appendAll process(bindings, body)
              loop(StaticEvaluation(step, bindings)._2)
            case _ => ()
          }

          loop(bindings)

          buf.toList
        }

        // Type check trees, yield Some(Nil) if type error, None if cannot be
        // typed and Some(result) otherwise
        def typeCheck(trees: Tree*)(result: => List[Tree]): Option[List[Tree]] = {

          val extra = trees flatMap { _ collect { case ExprSym(symbol) => symbol.decl } }

          val all = trees ++ extra

          val checks = all flatMap cc.typeCheck

          if (checks exists { !_ }) {
            hadError = true
            Some(Nil)
          } else if (checks.length != all.length) {
            None
          } else {
            Some(result)
          }
        }

        val result = gen match {
          case GenIf(cond, thenItems, elseItems) =>
            typeCheck(cond) {
              (cond given bindings).value match {
                case None =>
                  error(cond, "Condition of 'gen if' is not a compile time constant")
                  Nil
                case Some(v) if v != 0 => process(bindings, thenItems)
                case _                 => process(bindings, elseItems)
              }
            }

          case tree @ GenFor(gInits, cond, gSteps, body) =>
            typeCheck(gInits ::: cond :: gSteps: _*) {
              // normalize inits and steps so ticks and unsized constants are sized
              val inits = gInits map { _.normalize }
              val steps = gSteps map { _.normalize }
              if (cond.value.isDefined) {
                error(cond, "'gen for' condition does not depend on loop variable")
                Nil
              } else {
                val initBindings = bindings ++ {
                  inits collect {
                    case Decl(Sym(symbol, _), DescGen(_, init)) => symbol -> init.simplify
                  }
                }
                val stepStmt = TypeAssigner(StmtBlock(steps) withLoc tree.loc)
                val iteration = (LazyList from 0).iterator
                val limit = cc.settings.genLoopLimit
                val terminate = { bindings: Bindings =>
                  (cond given bindings).value map { value =>
                    if (value == 0) {
                      true
                    } else if (iteration.next() >= limit) {
                      error(
                        cond,
                        s"'gen for' exceeds $limit iterations. Possibly an infinite loop,",
                        s"otherwise set --gen-loop-limit to more than $limit"
                      )
                      true
                    } else {
                      false
                    }
                  }
                }
                generateFor(initBindings, terminate, cond.loc, body, stepStmt)
              }
            }

          case GenRange(decl @ Decl(Sym(symbol, _), _: DescGen), op, end, body) =>
            // Build a spoof condition node for type checking only
            val cond = {
              val expr = (ExprSym(symbol) withLoc symbol.loc) < end
              expr.copy() withLoc decl.loc.copy(start = symbol.loc.start)
            }
            typeCheck(decl, end, cond) {
              // Some(Maximum inclusive value representable by symbol.kind) or None if infinite
              val maxValueOpt = if (symbol.kind.underlying.isNum) {
                None
              } else if (symbol.kind.isSigned) {
                Some(BigInt.mask(symbol.kind.width - 1))
              } else {
                Some(BigInt.mask(symbol.kind.width))
              }

              (end given bindings).value map { value =>
                if (op == "<") value - 1 else value // Inclusive end value
              } match {
                case None =>
                  error(end, "End value of range 'gen for' is not a compile time constant")
                  Nil
                case Some(endValue) =>
                  val lastValue = maxValueOpt map { _ min endValue } getOrElse endValue
                  if (endValue > lastValue) {
                    val v = (end given bindings).value.get
                    val t = symbol.kind.underlying.toSource
                    cc.warning(
                      decl,
                      s"End value $v is out of range for variable ${symbol.name} with type '$t',",
                      s"will iterate only up to ${symbol.name} == ${maxValueOpt.get}"
                    )
                  }
                  val init = if (symbol.kind.underlying.isNum) {
                    ExprNum(symbol.kind.isSigned, 0) regularize symbol.loc
                  } else {
                    ExprInt(symbol.kind.isSigned, symbol.kind.width.toInt, 0) regularize symbol.loc
                  }
                  val initBindings = bindings + (symbol -> init)
                  val iter = (BigInt(0) to lastValue).iterator
                  val terminate = { _: Bindings =>
                    Some(if (iter.hasNext) { iter.next(); false } else true)
                  }
                  val stepStmt = StmtPost(ExprSym(symbol), "++") regularize decl.loc
                  generateFor(initBindings, terminate, Loc.synthetic, body, stepStmt)
              }
            }

          case _: GenRange => unreachable
        }

        if (hadError) Some(Nil) else result
      }

      // Result of the outermost encountered Gen construct
      private var generated: Option[List[Tree]] = None

      // Indicates whether we are in a parametrized Decl (> 0) or not ( == 0)
      private var parametrizedLevel = initialEntityLevel

      // Don't descend into expanded Gen
      override def skip(tree: Tree): Boolean = generated.nonEmpty

      override def enter(tree: Tree): Unit = {
        assert(generated.isEmpty, "should have stopped descent")

        // Clone symbols declared in the scope of this tree
        symbolMap ++= cloneSymbols(tree)

        tree match {
          case decl: Decl if decl.desc.isParametrized => parametrizedLevel += 1
          case _                                      =>
        }

        // Only process Gen in non-parametrized context
        if (parametrizedLevel == 0) {
          tree match {
            // Gen that must produce statement
            case StmtGen(gen) => generated = generate[Stmt](gen)

            // Gen that must produce case clauses
            case CaseGen(gen) => generated = generate[Case](gen)

            // Gen that must produce entity contents
            case EntGen(gen) => generated = generate[Ent](gen)

            // Keep going
            case _ =>
          }
        }
      }

      override def transform(tree: Tree): Tree = tree match {
        //////////////////////////////////////////////////////////////////////////
        // Replace processed *Gen nodes with the result
        //////////////////////////////////////////////////////////////////////////

        case _: EntGen if generated.isDefined =>
          val result = generated.get
          generated = None
          Thicket(result) withLoc tree.loc

        case _: StmtGen if generated.isDefined =>
          val result = generated.get
          generated = None
          Thicket(result) withLoc tree.loc

        case _: CaseGen if generated.isDefined =>
          val result = generated.get
          generated = None
          // Check we produced at most one default case
          val defaultCases = result collect { case c: CaseDefault => c }
          if (defaultCases.lengthIs > 1) {
            for (loc <- (defaultCases map { _.loc }).distinct) {
              error(loc, "'gen' yields multiple default cases")
            }
          }
          Thicket(result) withLoc tree.loc

        //////////////////////////////////////////////////////////////////////////
        // Replace refs to bound symbols with the value, and to cloned symbols
        // with a ref to the new symbol. Dict indices are handled by Resolve.
        //////////////////////////////////////////////////////////////////////////

        case ExprSym(symbol) =>
          bindings.get(symbol) orElse {
            symbolMap.get(symbol) map { ExprSym(_) withLoc tree.loc }
          } getOrElse tree

        case Sym(symbol, idxs) =>
          symbolMap.get(symbol) map { newSymbol =>
            Sym(newSymbol, idxs) withLoc tree.loc
          } getOrElse tree

        //////////////////////////////////////////////////////////////////////////
        // Update parametrizedLevel
        //////////////////////////////////////////////////////////////////////////

        case decl: Decl if decl.desc.isParametrized =>
          parametrizedLevel -= 1
          tree

        ////////////////////////////////////////////////////////////////////////
        // Done
        ////////////////////////////////////////////////////////////////////////

        case _ => tree
      }

      override def finalCheck(tree: Tree): Unit = {
        if (!hadError) {
          assert(generated.isEmpty)
          assert(parametrizedLevel == initialEntityLevel)
        }
      }
    }

    final class Resolve(implicit cc: CompilerContext) extends TreeTransformer {

      override val typed: Boolean = false
      override val checkRefs: Boolean = false

      // Latch errors
      var hadError = false

//    private[this] val refCounts = mutable.Map[Symbol, Int]()

      private[this] def error(loc: Loc, msg: String*): Unit = {
        cc.error(loc, msg: _*)
        hadError = true
      }

      // Indicates whether we are in a parametrized Decl (> 0) or not ( == 0)
      private var parametrizedLevel = 0

      // Skip choice symbol declarations that will be resolved. These will be
      // completely removed, but they also refer to invalid choices, which we
      // do not want to issue an error for as these references are being removed.
      override def skip(tree: Tree): Boolean = tree match {
        case Decl(_, _: DescChoice) => parametrizedLevel == 0
        case _                      => false
      }

      override def enter(tree: Tree): Unit = tree match {
        case decl: Decl if decl.desc.isParametrized => parametrizedLevel += 1
        case _                                      =>
      }

      private def extractValidChoices(symbol: Symbol): List[Symbol] =
        symbol.kind.asChoice.symbols flatMap { choice =>
          if (!(validChoices contains choice)) {
            Nil
          } else if (choice.isChoice) {
            extractValidChoices(choice)
          } else {
            List(choice)
          }
        }

      private def resolveChoiceSymbol(symbol: Symbol, loc: Loc): Option[Symbol] = {
        if (!symbol.isChoice) {
          Some(symbol)
        } else {
          extractValidChoices(symbol) match {
            case Nil =>
              if (parametrizedLevel == 0) {
                // Only error when appears in the non-parametrized context. The
                // choice symbol might be introduced in a nested parametrized
                // definition, and if so will be resolved when that definition is
                // specialized.
                error(loc, s"'${symbol.name}' is not defined after processing 'gen' constructs")
              }
              None
            case resolution :: Nil => Some(resolution)
            case resolutions =>
              val msg = s"'${symbol.name}' is ambiguous after processing 'gen' constructs. Active definitions at:" ::
                (resolutions.reverse map { _.loc.prefix })
              error(loc, msg: _*)
              None
          }
        }
      }

      private def resolveDict(symbol: Symbol, idxs: List[Expr], loc: Loc): Option[Symbol] =
        idxs match {
          case Nil => Some(symbol)
          case _ =>
            dictResolutions.get(symbol) match {
              case None => None // Gen not yet expanded (nested entity)
              case Some(dMap) =>
                values(idxs) orElse {
                  hadError = true
                  None
                } flatMap { idxValues =>
                  dMap.get(idxValues) orElse {
                    val expected = dMap.head._1.length
                    val provided = idxValues.length
                    if (expected != provided) {
                      error(
                        loc,
                        s"Wrong number of indices for name '${symbol.name}' (expected $expected, provided $provided)")
                    } else {
                      val srcName = idxValues.mkString(symbol.name + "#[", ", ", "]")
                      error(loc, s"'$srcName' is not defined after processing 'gen' constructs")
                    }
                    None
                  }
                }
            }
        }

      override def transform(tree: Tree): Tree = {
        val result = tree match {
          //////////////////////////////////////////////////////////////////////////
          // Resolve references to choice symbols
          //////////////////////////////////////////////////////////////////////////

          case ExprSym(symbol) =>
            resolveChoiceSymbol(symbol, tree.loc) map { symbol =>
              assert(!(dictResolutions contains symbol))
              ExprSym(symbol) withLoc tree.loc
            } getOrElse tree

          //////////////////////////////////////////////////////////////////////////
          // Resolve dict references
          //////////////////////////////////////////////////////////////////////////

          case Sym(symbol, idxs) =>
            resolveChoiceSymbol(symbol, tree.loc) flatMap {
              resolveDict(_, idxs, tree.loc)
            } map {
              Sym(_, Nil) withLoc tree.loc
            } getOrElse tree

          //////////////////////////////////////////////////////////////////////////
          // simplify now resolved ExprRefs
          //////////////////////////////////////////////////////////////////////////

          case ExprRef(Sym(symbol, Nil)) => ExprSym(symbol) withLoc tree.loc

          //////////////////////////////////////////////////////////////////////////
          // Drop choice  definitions
          //////////////////////////////////////////////////////////////////////////

          case EntDecl(Decl(_, _: DescChoice)) if parametrizedLevel == 0 =>
            Thicket(Nil) withLoc tree.loc
          case RecDecl(Decl(_, _: DescChoice)) if parametrizedLevel == 0 =>
            Thicket(Nil) withLoc tree.loc
          case StmtDecl(Decl(_, _: DescChoice)) if parametrizedLevel == 0 =>
            Thicket(Nil) withLoc tree.loc

          //////////////////////////////////////////////////////////////////////////
          // DescEntity
          //////////////////////////////////////////////////////////////////////////

//        case desc: DescEntity => {
//          if (parametrizedLevel == 0 || desc.variant == EntityVariant.Ver) {
//            desc
//          } else {
////            // Remove const declarations with no more references
////            @tailrec
////            def loop(body: List[Ent]): List[Ent] = {
////              if (refCounts.valuesIterator contains 0) {
////                loop {
////                  body filter {
////                    case EntDecl(Decl(Sym(symbol, _), desc)) if refCounts get symbol contains 0 =>
////                      refCounts remove symbol
////                      desc visit { case ExprSym(s) => refCounts(s) -= 1 }
////                      false
////                    case _ => true
////                  }
////                }
////              } else {
////                body
////              }
////            }
////
////            desc.copy(body = loop(desc.body)) withLoc desc.loc
//            desc
//          }
//        } tap { _ =>
//          entityLevel -= 1
//        }

          //////////////////////////////////////////////////////////////////////////
          // Update parametrizedLevel
          //////////////////////////////////////////////////////////////////////////

          case decl: Decl if decl.desc.isParametrized =>
            parametrizedLevel -= 1
            tree

          ////////////////////////////////////////////////////////////////////////
          // Done
          ////////////////////////////////////////////////////////////////////////

          case _ => tree

        }

        // TODO: make it work out of order and with param assings...
//      result match {
//        case ExprSym(symbol) =>
//          refCounts.updateWith(symbol) { _ map { _ + 1 } }
//        case Decl(Sym(symbol, _), _: DescConst) if entityLevel == 1 =>
//          refCounts(symbol) = 0
////      case EntInstance(_, _, _, paramExprs) =>
////        // Ignore references in parameter assignments. These will be stripped
////        // by the end of Specialize.
////        paramExprs foreach {
////          _ visit {
////            case ExprSym(symbol) => refCounts.updateWith(symbol) { _ map { _ - 1 } }
////          }
////        }
//        case _ =>
//      }

        result
      }

      override def finalCheck(tree: Tree): Unit = {
        if (!hadError) {
          assert(parametrizedLevel == 0)
          tree visit {
            case EntDecl(Decl(_, _: DescEntity))      => // Stop descent
            case node @ Sym(_, idxs) if idxs.nonEmpty => cc.error(node, "Sym with indices remains")
            case node: DescChoice                     => cc.ice(node, "DescChoice remains")
          }
        }
      }
    }

    val hasGen = decl exists {
      case desc: Desc if desc.isParametrized => false // Stop descent
      case _: Gen                            => true
    }

    if (!hasGen) {
      Some(decl)
    } else {
      // Expand Gen nodes
      val processed = {
        val process = new Process(Bindings.empty, Map.empty, 0)
        val res = (decl rewrite process).asInstanceOf[Decl] ensuring { _.symbol eq decl.symbol }
        if (process.hadError) None else Some(res)
      }

      // Resolve choice and dict symbols
      val resolved = processed flatMap { decl: Decl =>
        val resolve = new Resolve
        val res = (decl rewrite resolve).asInstanceOf[Decl] ensuring { _.symbol eq decl.symbol }
        if (resolve.hadError) None else Some(res)
      }

      // Finally, clone the declared symbol
      resolved map { decl: Decl =>
        decl.copy(
          ref = Sym(decl.symbol.dup, Nil) withLoc decl.ref.loc
        ) withLoc decl.loc
      }
    }
  }
}
