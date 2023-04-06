package commutativity

import viper.silver.ast.{And, AnySetCardinality, AnySetContains, AnySetIntersection, AnySetUnion, Assert, Bool, CondExp, Domain, DomainAxiom, DomainFunc, DomainFuncApp, EmptyMultiset, EmptySeq, EmptySet, EqCmp, ErrTrafo, Exhale, Exp, ExplicitMultiset, ExplicitSeq, ExplicitSet, ExtensionMember, FieldAccessPredicate, Forall, FullPerm, FuncApp, Function, GeCmp, GtCmp, Implies, Inhale, IntLit, Label, Let, LocalVar, LocalVarAssign, LocalVarDecl, LtCmp, Method, MethodCall, MultisetType, NoInfo, NoTrafos, Node, NodeTrafo, Position, Predicate, PredicateAccess, PredicateAccessPredicate, Program, Ref, Result, SeqAppend, SeqIndex, SeqLength, SeqType, Seqn, SetType, Stmt, Sub, Trafos, Trigger, TrueLit, Type, TypeVar}
import viper.silver.ast.utility.{Expressions, QuantifiedPermissions}
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.sif.SIFExtendedTransformer.{MethodControlFlowVars, TranslationContext}
import viper.silver.sif.{SIFExtendedTransformer, SIFLowEventExp, SIFLowExp}
import viper.silver.verifier.{AbstractError, TypecheckerError}
import viper.silver.verifier.errors.{AssertFailed, ExhaleFailed, PostconditionViolated}

import scala.collection.mutable
import scala.collection.mutable.ListBuffer


object Extensions {
  implicit class ExpWithStuff[T <: Node](val e: T) extends AnyVal {
    def replaceT(toReplace: Exp, lv: LocalVar) : T = {
      e.transform({
        case exp: Exp if exp == toReplace => {
          LocalVar(lv.name, lv.typ)(exp.pos, errT=NodeTrafo(exp))
        }
      }, Traverse.BottomUp)
    }
  }
}

/*
 * Implements the encoding of lock specifications, thread fork and join, lock operations, ghost operations,
 * as well as information flow and action (guard) assertions.
 */
trait CommutativityTransformer {

  import Extensions._

  var nameCtr = 0

  /*
   * Returns a fresh integer (used to generate fresh names).
   */
  def getFreshInt(): Int = {
    nameCtr += 1
    nameCtr - 1
  }

  /*
   * Declares a function "intervalSet(from, until)" representing the set of all integers between from and until.
   */
  def getIntervalSetFunction() = {
    val frm = LocalVarDecl("$frm", viper.silver.ast.Int)()
    val ntl = LocalVarDecl("$ntl", viper.silver.ast.Int)()
    val params = Seq(frm, ntl)
    val pres = Seq(GeCmp(ntl.localVar, frm.localVar)())
    val i = LocalVarDecl("$i", viper.silver.ast.Int)()
    val iInResult = AnySetContains(i.localVar, Result(SetType(viper.silver.ast.Int))())()
    val triggers = Seq(Trigger(Seq(iInResult))())
    val iInBounds = And(GeCmp(i.localVar, frm.localVar)(), LtCmp(i.localVar, ntl.localVar)())()
    val bod = EqCmp(iInResult, iInBounds)()
    val lenPost = EqCmp(AnySetCardinality(Result(SetType(viper.silver.ast.Int))())(), Sub(ntl.localVar, frm.localVar)())()
    val posts = Seq(Forall(Seq(i), triggers, bod)(), lenPost)
    val intervalSetFunc = Function("intervalSet", params, SetType(viper.silver.ast.Int), pres, posts, None)()
    intervalSetFunc
  }

  def setBetween(from: Exp, until: Exp, pos: Position, errtrans: ErrTrafo): Exp = {
    FuncApp("intervalSet", Seq(from, until))(pos, NoInfo, SetType(viper.silver.ast.Int), errtrans)
  }

  def reportError(error: AbstractError): Unit

  /*
   * Checks well-definedness criteria for the lock specification em and extracts some information from it into the
   * supplied maps.
   */
  def checkDeclarationConsistency(em: ExtensionMember, lockSpecs: mutable.HashMap[String, LockSpec],
                                  actionGuardNames: mutable.HashMap[String, mutable.HashMap[String, (String, Type, Boolean)]]
                                 ) = em match {
    case l@LockSpec(name, t, inv, alpha, hist, actions, proofs, nlabels) => {
      if (!Expressions.isPure(alpha.exp)) {
        reportError(TypecheckerError("Abstraction function must be pure", alpha.exp.pos))
      }
      if (hist.isDefined && !Expressions.isPure(hist.get.inv)) {
        reportError(TypecheckerError("History invariant must be pure", hist.get.inv.pos))
      }
      inv.inv.visit {
        case _: Lock => reportError(TypecheckerError("Invariants must not contain lock() assertions.", inv.inv.pos))
        case _: Locked => reportError(TypecheckerError("Invariants must not contain locked() assertions.", inv.inv.pos))
        case _: Barrier => reportError(TypecheckerError("Invariants must not contain barrier() assertions.", inv.inv.pos))
      }

      lockSpecs.update(name, l)
      val guardNames = mutable.HashMap[String, (String, Type, Boolean)]()
      actionGuardNames.update(name, guardNames)


      for (a <- actions) {
        guardNames.update(a.name, ("$guard$" + name + "$" + a.name, a.argType, a.duplicable))
        if (!Expressions.isPure(a.pre)) {
          reportError(TypecheckerError("Precondition must be pure", a.pre.pos))
        }
        if (a.pre.existsDefined {
          case LocalVar(name, _) if name == a.params(0).name => true
        }) {
          reportError(TypecheckerError("Precondition must not constrain lock state", a.pre.pos))
        }
        if (!Expressions.isPure(a.newVal)) {
          reportError(TypecheckerError("Action definition must be pure", a.newVal.pos))
        }
      }
    }
  }

  /*
   * For the given method m, generates a predicate representing the right to join a thread running said method,
   * as well as one function each for each parameter of the method, which represent the argument with which a given
   * thread is running said method (and stores them in the given maps).
   */
  def generateJoinable(m: Method, joinableNames: mutable.HashMap[String, String],
                       joinablePreds: mutable.HashMap[String, Predicate],
                       joinableFunctions: mutable.HashMap[String, ListBuffer[Function]]) = {
    val joinableName = "$joinable$" + m.name
    joinableNames.update(m.name, joinableName)
    val receiver = LocalVarDecl("$rec", Ref)()
    val joinablePred = Predicate(joinableName, Seq(receiver), None)()
    joinablePreds.update(m.name, joinablePred)
    val funcs = ListBuffer[Function]()
    joinableFunctions.update(m.name, funcs)
    val predAcc = PredicateAccess(Seq(receiver.localVar), joinableName)()
    val pred = PredicateAccessPredicate(predAcc, FullPerm()())()
    for (arg <- m.formalArgs) {
      val funcName = "$joinable$" + m.name + "$" + arg.name
      val joinableFunc = Function(funcName, Seq(receiver), arg.typ, Seq(pred), Seq(), None)()
      funcs.append(joinableFunc)
    }
  }

  /*
   * Generates havoc-methods (that return arbitrary values and can thus be used to havoc local variables),
   * one for each output parameter of the given method m (with its respective type) and stores them
   * into newMethods.
   */
  def generateHavocMethods(m: Method, havocNames: mutable.HashMap[Type, String],
                           newMethods: ListBuffer[Method]) = {
    val name = "$$havoc$" + getFreshInt()
    havocNames.update(Ref, name)
    val resVar = LocalVarDecl(name + "$res", Ref)()
    val newMethod = Method(name, Seq(), Seq(resVar), Seq(), Seq(), None)()
    newMethods.append(newMethod)
    for (arg <- m.formalReturns) {
      if (!havocNames.contains(arg.typ)) {
        val name = "$$havoc$" + getFreshInt()
        havocNames.update(arg.typ, name)
        val resVar = LocalVarDecl(name + "$res", arg.typ)()
        val newMethod = Method(name, Seq(), Seq(resVar), Seq(), Seq(), None)()
        newMethods.append(newMethod)
      }
    }
  }

  /*
   * Generates methods for checking various properties of the given lock specification em, and stores them in
   * newMethods.
   * Properties checked are:
   * - the lock invariant uniquely defines the value of the lock.
   * - the abstraction function alpha is well-defined
   * - noLabels is non-negative
   * - the lock specification is valid:
   *   - each action preserves the low-ness of the abstraction of the lock value
   *   - every relevant pair of actions commutes (i.e., all actions with all actions except unique actions with themselves)
   */
  def encodeExtension(em: ExtensionMember, newMethods: ListBuffer[Method]) = em match {
    case l@LockSpec(name, t, inv, alpha, _, actions, proofs, nlabels) => {

      ////// nlabels positive
      val labelsPos = GtCmp(nlabels, IntLit(0)())()
      newMethods.append(Method("$nlabelsPos$" + name + getFreshInt(), Seq(), Seq(), Seq(), Seq(labelsPos), Some(Seqn(Seq(), Seq())()))())

      ////// invariant uniquely defines value (ud)
      // declare 1 lock, 2 value vars
      val udLockVar = LocalVarDecl("$udVar$" + getFreshInt(), Ref)()
      val udVal1 = LocalVarDecl("$udVar1$" + getFreshInt(), t)()
      val udVal2 = LocalVarDecl("$udVar2$" + getFreshInt(), t)()

      // inhale perms
      val perms = inv.permissionsWithArgs(Seq(udLockVar.localVar, udVal1.localVar))

      // inhale val def on first and second var
      val valDef1 = inv.pureWithArgs(Seq(udLockVar.localVar, udVal1.localVar))
      val valDef2 = inv.pureWithArgs(Seq(udLockVar.localVar, udVal2.localVar))

      // assert same var
      val uniquenessTrafo = ErrTrafo({
        case PostconditionViolated(node, _, reason, _) => UniquenessCheckFailed(name, node, reason)
      })
      val sameVal = EqCmp(udVal1.localVar, udVal2.localVar)(l.pos, errT = uniquenessTrafo)

      val udMethod = Method("$udCheck$" + name + "$" + getFreshInt(), Seq(udLockVar, udVal1, udVal2), Seq(), Seq(perms, valDef1, valDef2), Seq(sameVal), Some(Seqn(Seq(), Seq())()))(l.pos, errT = uniquenessTrafo)
      newMethods.append(udMethod)

      /////// alpha is well-defined
      val alphaWDV = LocalVarDecl("$alphaWDVar$" + getFreshInt(), t)()
      val alphaWDInv = alpha.lowWithArg(alphaWDV.localVar, alpha.exp.pos)
      val alphaWDMethod = Method("$secWD$" + name + "$" + getFreshInt(), Seq(alphaWDV), Seq(), Seq(alphaWDInv), Seq(), None)(l.pos)
      newMethods.append(alphaWDMethod)

      for (a <- actions) {

        ////// actionX2 preserves lowness of abstraction
        // declare original, final val, ret val variables
        val presOrigVar = LocalVarDecl("$presOrig$" + getFreshInt(), t)()
        val presArgVar = LocalVarDecl("$presArg$" + getFreshInt(), a.argType)()
        val presFinalVar = LocalVarDecl("$presFinal$" + getFreshInt(), t)()

        // assume secInv and precond
        val presSecInv = alpha.lowWithArg(presOrigVar.localVar)
        val presPrecond = a.pre.replaceT(a.params(0).localVar, presOrigVar.localVar).replaceT(a.params(1).localVar, presArgVar.localVar)

        // define results
        val presFinalVal = a.newVal.replaceT(a.params(0).localVar, presOrigVar.localVar).replaceT(a.params(1).localVar, presArgVar.localVar)
        val presFinalValEq = EqCmp(presFinalVar.localVar, presFinalVal)(presFinalVal.pos, errT = NodeTrafo(presFinalVal))

        // assert alpha is low
        val preservationTrafo = ErrTrafo({
          case PostconditionViolated(node, _, reason, _) => PreservationCheckFailed(a.name, node, reason)
        })
        //val presPostcond = a.post.replaceT(a.params(0).localVar, presOrigVar.localVar).replaceT(a.params(1).localVar, presArgVar.localVar).replaceT(Result(a.retType)(), presRetVar.localVar)
        val presSecInvFinal = alpha.lowWithArg(presFinalVar.localVar, alpha.exp.pos)
        val presProof = proofs.find(p => p.proofType == "preservation" && p.actions.length == 1 && p.actions(0) == a.name)
        val presBody = presProof match {
          case None => Some(Seqn(Seq(), Seq())())
          case Some(p) => Some(p.body.replaceT(p.params(0).localVar, presOrigVar.localVar).replaceT(p.params(1).localVar, presArgVar.localVar))
        }
        val presPosts = Seq((presSecInvFinal, SIFLowExp(alpha.exp)(alpha.exp.pos))).map { case (p: Exp, po: Exp) => EqCmp(TrueLit()(), p)(a.pos, errT = Trafos(List({
          case PostconditionViolated(node, _, reason, _) => PreservationCheckFailed(a.name, node, reason)
        }), List(), Some(po)))
        }
        val presMethod = Method("$presCheck$" + getFreshInt(), Seq(presOrigVar, presArgVar, presFinalVar), Seq(), Seq(SIFLowEventExp()(), presSecInv, presPrecond, presFinalValEq), presPosts, presBody)(a.pos, errT = preservationTrafo)
        newMethods.append(presMethod)

        val a1 = a
        for (a2 <- actions) {
          if (actions.indexOf(a1) < actions.indexOf(a2) || (a1 == a2 && a1.duplicable)) {
            // for every action with every other action including itself

            ////// actions commute
            // all vars
            val commOrigDecl = LocalVarDecl("$commOrig$" + getFreshInt(), t)()
            val commFinalDecl = LocalVarDecl("$commFinal$" + getFreshInt(), t)()
            val commChoiceDecl = LocalVarDecl("$commChoice$" + getFreshInt(), Bool)()
            val commOrig1Decl = LocalVarDecl("$commOrig1$" + getFreshInt(), t)()
            val commOrig2Decl = LocalVarDecl("$commOrig2$" + getFreshInt(), t)()
            val commArg1Decl = LocalVarDecl("$commArg1$" + getFreshInt(), a1.argType)()
            val commArg2Decl = LocalVarDecl("$commArg2$" + getFreshInt(), a2.argType)()
            val commRes1Decl = LocalVarDecl("$commRes1$" + getFreshInt(), t)()
            val commRes2Decl = LocalVarDecl("$commRes2$" + getFreshInt(), t)()

            // pres hold
            val commPreA1 = a1.pre.replaceT(a1.params(0).localVar, commOrig1Decl.localVar).replaceT(a1.params(1).localVar, commArg1Decl.localVar)
            val commPreA2 = a2.pre.replaceT(a2.params(0).localVar, commOrig2Decl.localVar).replaceT(a2.params(1).localVar, commArg2Decl.localVar)
            val commOrigSecInv = alpha.lowWithArg(commOrigDecl.localVar)

            // define results
            val commResA1 = EqCmp(commRes1Decl.localVar, a1.newVal.replaceT(a1.params(0).localVar, commOrig1Decl.localVar).replaceT(a1.params(1).localVar, commArg1Decl.localVar))(a1.newVal.pos, errT = NodeTrafo(a1.newVal))
            val commResA2 = EqCmp(commRes2Decl.localVar, a2.newVal.replaceT(a2.params(0).localVar, commOrig2Decl.localVar).replaceT(a2.params(1).localVar, commArg2Decl.localVar))(a2.newVal.pos, errT = NodeTrafo(a2.newVal))

            // define both execution orders
            val commOpt1Orig = EqCmp(commOrigDecl.localVar, commOrig1Decl.localVar)()
            val commOpt1ResOrig = EqCmp(commOrig2Decl.localVar, commRes1Decl.localVar)()
            val commOpt1Final = EqCmp(commFinalDecl.localVar, commRes2Decl.localVar)()
            val commOpt2Orig = EqCmp(commOrigDecl.localVar, commOrig2Decl.localVar)()
            val commOpt2ResOrig = EqCmp(commOrig1Decl.localVar, commRes2Decl.localVar)()
            val commOpt2Final = EqCmp(commFinalDecl.localVar, commRes1Decl.localVar)()
            val commOpt1 = And(And(commOpt1Orig, commOpt1ResOrig)(), commOpt1Final)()
            val commOpt2 = And(And(commOpt2Orig, commOpt2ResOrig)(), commOpt2Final)()
            val commOptions = CondExp(commChoiceDecl.localVar, commOpt1, commOpt2)()

            // checks
            val commutativityTrafo = ErrTrafo({
              case PostconditionViolated(node, _, reason, _) => CommutativityCheckFailed(a1.name, a2.name, node, reason)
            })
            val commCheckSecInv = alpha.lowWithArg(commFinalDecl.localVar)


            val commName = "$commCheck$" + a1.name + "$" + a2.name + "$" + getFreshInt()
            val commParams = Seq(commOrigDecl, commFinalDecl, commChoiceDecl, commOrig1Decl, commOrig2Decl, commArg1Decl, commArg2Decl, commRes1Decl, commRes2Decl)
            val commPres = Seq(SIFLowEventExp()(), commPreA1, commPreA2, commOrigSecInv, commResA1, commResA2, commOptions)
            val commPosts = Seq((commCheckSecInv, SIFLowExp(alpha.exp)(alpha.exp.pos))).map { case (p, po) => EqCmp(TrueLit()(), p)(a1.pos, errT = Trafos(List({
              case PostconditionViolated(node, _, reason, _) => CommutativityCheckFailed(a1.name, a2.name, node, reason)
            }), List(), Some(po)))
            }

            val commProof = proofs.find(p => p.proofType == "commutativity" && p.actions(0) == a1.name && p.actions(1) == a2.name)
            val commBody = if (commProof.isDefined) {
              commProof.get.body.replaceT(commProof.get.params(0).localVar, commOrigDecl.localVar).replaceT(commProof.get.params(1).localVar, commArg1Decl.localVar).replaceT(commProof.get.params(2).localVar, commArg2Decl.localVar)
            } else {
              Seqn(Seq(), Seq())()
            }
            val commMethod = Method(commName, commParams, Seq(), commPres, commPosts, Some(commBody))(a1.pos, errT = commutativityTrafo)
            newMethods.append(commMethod)
          }
        }
      }
    }
  }

  /*
   * Encodes a program containing lock specs and other parts of the extended language into a standard Viper program
   * that can be verified by Viper.
   * More concretely,
   * - checks consistency criteria for lock specs
   * - generates various helper functions, predicates, and methods
   * - encodes well-definedness and validity checks for lock specs
   * - transforms all statements, expressions and assertions related to commutativity reasoning
   * - creates a product program of the resulting program, which also transforms low(e) and lowEvent assertions
   *   into standard Viper assertions
   */
  def encodeProgram(input: Program): Program = {
    val lockSpecs = mutable.HashMap[String, LockSpec]()
    val actionGuardNames = mutable.HashMap[String, mutable.HashMap[String, (String, Type, Boolean)]]()

    input.extensions.foreach(em => checkDeclarationConsistency(em, lockSpecs, actionGuardNames))

    val newMethods = ListBuffer[Method]()
    val havocNames = mutable.HashMap[Type, String]()

    // For every method m with n input parameters, we create n functions joinable_m_i and a predicate joinable_m,
    // s.t. having the predicate represents the right to join a thread executing the method and inhale the method
    // postcondition, and joinable_m_i returns the ith argument it was started with.
    val joinableNames = mutable.HashMap[String, String]()
    val joinablePreds = mutable.HashMap[String, Predicate]()
    val joinableFunctions = mutable.HashMap[String, ListBuffer[Function]]()

    for (m <- input.methods) {
      generateJoinable(m, joinableNames, joinablePreds, joinableFunctions)
      generateHavocMethods(m, havocNames, newMethods)
    }

    // For every action a, we create a predicate guard_a representing the guard
    val guardPreds = actionGuardNames.map(ls => ls._2.map(a => Predicate(a._2._1, Seq(LocalVarDecl("$rec", Ref)()) ++ (if (a._2._3) Seq(LocalVarDecl("$lbls", SetType(viper.silver.ast.Int))()) else Seq()), None)())).flatten
    // and a function guardArgs_a depending on the predicate that returns the guard's argument multiset or sequence
    // (depending on whether the action is shared or not).
    val guardArgFuncs: Seq[Function] = actionGuardNames.flatMap(ls => ls._2.map(a => {
      val fname = a._2._1 + "$args"
      val params = Seq(LocalVarDecl("$rec", Ref)()) ++ (if (a._2._3) Seq(LocalVarDecl("$lbls", SetType(viper.silver.ast.Int))()) else Seq())
      val rtype = if (a._2._3) MultisetType(a._2._2) else SeqType(a._2._2)
      val pres = Seq(PredicateAccessPredicate(PredicateAccess(params.map(_.localVar), a._2._1)(), FullPerm()())())
      val posts = if (a._2._3) Seq(Implies(EqCmp(AnySetCardinality(LocalVar("$lbls", SetType(viper.silver.ast.Int))())(), IntLit(0)())(),
        EqCmp(AnySetCardinality(Result(rtype)())(), IntLit(0)())())()) else Seq()
      Function(fname, params, rtype, pres, posts, None)()
    })).toSeq

    val newPredicates: Seq[Predicate] = input.predicates ++ joinablePreds.values ++ guardPreds
    val newFunctions: Seq[Function] = input.functions ++ guardArgFuncs ++ joinableFunctions.values.flatten

    input.methods.foreach(newMethods.append(_))

    input.extensions.foreach(em => encodeExtension(em, newMethods))

    val withAdded = input.copy(extensions = Seq(), predicates = newPredicates, functions = newFunctions, methods = newMethods)(input.pos, input.info, input.errT)

    // Function to encode custom expressions and assertions to standard Viper assertions.
    val transformExp: PartialFunction[Node, Exp] = {
      case pt@PointsToPredicate(fa, p, None) =>
        // [x.f --[p]-> _] is encoded to acc(x.f, p)
        FieldAccessPredicate(fa, p)(pt.pos, errT = NodeTrafo(pt))
      case pt@PointsToPredicate(fa, p, Some(e)) =>
        // [x.f --[p]-> e] is encoded to acc(x.f, p) && x.f == e
        And(FieldAccessPredicate(fa, p)(), EqCmp(fa, e)(pt.pos, errT = NodeTrafo(pt)))(pt.pos, errT = NodeTrafo(pt))
      case pt@VarDefiningPointsToPredicate(fa, p, v, Some(b)) =>
        // [x.f --[p]-> ?v * b] is encoded to acc(x.f, p) && let v = e in b
        And(FieldAccessPredicate(fa, p)(pt.pos, errT = NodeTrafo(pt)), Let(v, fa, b)(pt.pos, errT = NodeTrafo(pt)))(pt.pos, errT = NodeTrafo(pt))
      case pt@VarDefiningPointsToPredicate(fa, p, v, None) =>
        // [x.f --[p]-> ?v] is encoded to acc(x.f, p)
        FieldAccessPredicate(fa, p)(pt.pos, errT = NodeTrafo(pt))
      case pt@Joinable(m, e, args) => {
        // joinable[m](e, args) is encoded as
        // acc(joinable_m(e)) && joinable_m_0(e) == args(0) && ... && joinable_m_n(e) == args(n)
        val pa = PredicateAccess(Seq(e), joinableNames.get(m).get)()
        val pap = PredicateAccessPredicate(pa, FullPerm()())(pt.pos, errT = NodeTrafo(pt))
        var res: Exp = pap
        for (i <- 0 until args.length) {
          val funcApp = EqCmp(FuncApp(joinableFunctions.get(m).get(i), Seq(e))(pt.pos, errT = NodeTrafo(pt)), args(i))(pt.pos, errT = NodeTrafo(pt))
          res = And(res, funcApp)(pt.pos, errT = NodeTrafo(pt))
        }
        res
      }
      case pt@SGuard(lt, g, lock, lbls) => {
        // sguard[lt, a](lock, lbls) is encoded as
        // guard_a(lock, lbls)
        val pa = PredicateAccess(Seq(lock, lbls), actionGuardNames.get(lt).get.get(g).get._1)()
        PredicateAccessPredicate(pa, FullPerm()())(pt.pos, errT = NodeTrafo(pt))
      }
      case pt@UGuard(lt, g, lock) => {
        // uguard[lt, a](lock) is encoded as
        // guard_a(lock)
        val pa = PredicateAccess(Seq(lock), actionGuardNames.get(lt).get.get(g).get._1)()
        PredicateAccessPredicate(pa, FullPerm()())(pt.pos, errT = NodeTrafo(pt))
      }
      case pt@SGuardArgs(lt, g, lock, lbls, typ) => {
        // sguardArgs[lt, a](lock, lbls) is encoded as
        // guardArgs_a(lock, lbls)
        FuncApp(actionGuardNames.get(lt).get.get(g).get._1 + "$args", Seq(lock, lbls))(pt.pos, pt.info, typ, errT = NodeTrafo(pt))
      }
      case pt@UGuardArgs(lt, g, lock, typ) => {
        // uguardArgs[lt, a](lock) is encoded as
        // guardArgs_a(lock)
        FuncApp(actionGuardNames.get(lt).get.get(g).get._1 + "$args", Seq(lock))(pt.pos, pt.info, typ, errT = NodeTrafo(pt))
      }
      case as@AllPre(lt, actionName, args) => {
        // allPre[lt, a](args) is encoded as
        // allPre_a(args)
        val lockSpec = lockSpecs.get(lt).get
        SIFLowExp(args, Some("allpre$" + lockSpec.name + "$" + actionName))(as.pos)
      }
    }

    // Function to transform custom statements to standard Viper code.
    val transformStmt: PartialFunction[Node, Stmt] = {
      case s@Share(lt, lockExp, lockVal) => {
        // share[lt](lockExp, lockVal) is encoded to
        // assert Inv(lockExp, lockVal)
        // assert lowEvent
        // assert low(alpha(lockVal))
        // exhale Inv(lockExp, lockVal)
        // <for action a in lt>
        //   <if a is unique>
        //     inhale guard_a(lockExp)
        //     inhale guardArgs_a(lockExp) == Sequence()
        //   <else>
        //     inhale guard_a(lockExp, Set(0 .. noLabels))
        //     inhale guardArgs_a(lockExp, Set(0 .. noLabels)) == Multiset()

        val lockSpec = lockSpecs.get(lt).get
        val invPerms = lockSpec.invariant.withArgs(Seq(lockExp, lockVal))
        val errTrafo = ErrTrafo({
          case AssertFailed(_, reason, _) => ShareFailed(s, reason)
        })
        val assertInv = Assert(invPerms)(s.pos, errT = errTrafo)
        val exhaleInv = Exhale(invPerms)(s.pos)

        val assertSecInv = Assert(lockSpec.alpha.lowWithArg(lockVal))(s.pos, errT = errTrafo)
        val assertLowEvent = Assert(SIFLowEventExp()(s.pos))(s.pos, errT = errTrafo)

        val guardInhales = ListBuffer[Inhale]()
        val guardNames = actionGuardNames.get(lt).get
        val fp = FullPerm()()
        for (a <- lockSpec.actions) {
          val args = if (a.duplicable) {
            Seq(lockExp, setBetween(IntLit(0)(), lockSpec.nlabels, s.pos, errTrafo))
          } else {
            Seq(lockExp)
          }
          val (argsType, argsVal) = if (a.duplicable) {
            (MultisetType(a.argType), EmptyMultiset(a.argType)())
          } else {
            (SeqType(a.argType), EmptySeq(a.argType)())
          }
          val pa = PredicateAccess(args, guardNames.get(a.name).get._1)()
          val fa = FuncApp(guardNames.get(a.name).get._1 + "$args", args)(s.pos, NoInfo, argsType, errT = NodeTrafo(s))
          guardInhales.append(Inhale(PredicateAccessPredicate(pa, fp)(s.pos, errT = NodeTrafo(s)))(s.pos, errT = NodeTrafo(s)))
          guardInhales.append(Inhale(EqCmp(fa, argsVal)())())
        }
        Seqn(Seq(assertInv, assertLowEvent, assertSecInv, exhaleInv) ++ guardInhales, Seq())(s.pos)
      }
      case u@Unshare(lt, lockExp) => {
        // unshare[lt](lockExp) is encoded as
        // <for action a in lt>
        //   <if a is unique>
        //     assert guard_a(lockExp>)
        //   <else>
        //     assert guard_a(lockExp, Set(0 .. noLabels)
        // assert lowEvent
        // var invVal
        // inhale Inv(lockExp, invVal)
        // <for action a in lt>
        //   <if a is unique>
        //     assert allPre_a(guardArgs_a(lockExp>))
        //   <else>
        //     assert allPre_a(guardArgs_a(lockExp, Set(0 .. noLabels))
        // <for action a in lt>
        //   <if a is unique>
        //     exhale guard_a(lockExp>)
        //   <else>
        //     exhale guard_a(lockExp, Set(0 .. noLabels)
        // inhale low(alpha(invVal))

        val lockSpec = lockSpecs.get(lt).get
        // assert all guards and allpre, exhale all guards
        val guardAsserts = ListBuffer[Assert]()
        val guardAllPreAsserts = ListBuffer[Assert]()
        val guardExhales = ListBuffer[Exhale]()
        val guardNames = actionGuardNames.get(lt).get
        val fp = FullPerm()()
        val errTrafo = ErrTrafo({
          case AssertFailed(_, reason, _) => UnshareFailed(u, reason)
        })
        for (a <- lockSpec.actions) {
          val args = if (a.duplicable) {
            Seq(lockExp, setBetween(IntLit(0)(), lockSpec.nlabels, u.pos, errTrafo))
          } else {
            Seq(lockExp)
          }
          val (argsType, _) = if (a.duplicable) {
            (MultisetType(a.argType), EmptyMultiset(a.argType)())
          } else {
            (SeqType(a.argType), EmptySeq(a.argType)())
          }
          val pa = PredicateAccess(args, guardNames.get(a.name).get._1)()
          val fa = FuncApp(guardNames.get(a.name).get._1 + "$args", args)(u.pos, NoInfo, argsType, errT = NodeTrafo(u))
          guardAsserts.append(Assert(PredicateAccessPredicate(pa, fp)(u.pos, errT = NodeTrafo(u)))(u.pos, errT = NodeTrafo(u)))
          guardExhales.append(Exhale(PredicateAccessPredicate(pa, fp)(u.pos, errT = NodeTrafo(u)))(u.pos, errT = NodeTrafo(u)))
          guardAllPreAsserts.append(Assert(SIFLowExp(fa, Some("allpre$" + lockSpec.name + "$" + a.name))())())
        }

        // assert lowEvent
        val assertLowEvent = Assert(SIFLowEventExp()(u.pos))(u.pos, errT = errTrafo)
        // inhale Inv(lockExp, invVal)
        val invValDummyName = "$invVal$" + getFreshInt()
        val invValDummyDecl = LocalVarDecl(invValDummyName, lockSpec.t)()
        val invPerms = lockSpec.invariant.withArgs(Seq(lockExp, invValDummyDecl.localVar))

        val inhaleInv = Inhale(invPerms)(u.pos)

        // assume low(alpha(v))
        val assumeSecInv = Inhale(lockSpec.alpha.lowWithArg(invValDummyDecl.localVar))(u.pos, errT = errTrafo)
        Seqn(guardAsserts ++ Seq(assertLowEvent, inhaleInv) ++ guardAllPreAsserts ++ guardExhales ++ Seq(assumeSecInv), Seq(invValDummyDecl))()
      }
      case w@With(lt, lockExp, whenExp, actionName, arg, lbl, bod) => {
        // with[lt] lt when whenExp performing actionName(arg) at lbl { bod }
        // is encoded as
        // assert guard_a(lockExp)
        // var tmp := guardArgs_a(lockExp)
        // exhale guard_a(lockExp)
        // var invVal
        // inhale Inv(lockExp, invVal)
        // <if whenExp is defined>
        //   assume whenExp
        // [[bod]]
        // var newInvVal := action(invVal, arg)
        // exhale Inv(lockExp, newInvVal)
        // inhale guard_a(lockExp)
        // assume guardArgs_a(lockExp) == tmp ++ [arg]
        // assert allPre(tmp) && a.pre(arg) ==> allPre(tmp ++ [arg])

        val lockSpec = lockSpecs.get(lt).get
        val a = lockSpec.actions.find(la => la.name == actionName).get
        // assert guard
        val guardArgs = Seq(lockExp) ++ (if (lbl.isDefined) Seq(ExplicitSet(Seq(lbl.get))()) else Seq())
        val guardPred = PredicateAccess(guardArgs, actionGuardNames.get(lt).get.get(actionName).get._1)(w.pos)
        val fp = FullPerm()()
        val guardPredAcc = PredicateAccessPredicate(guardPred, fp)(w.pos)
        val assertGuard = Assert(guardPredAcc)(w.pos)
        val exhaleGuard = Exhale(guardPredAcc)(w.pos)
        // remember guardargs
        val guardArgsType = if (a.duplicable) MultisetType(a.argType) else SeqType(a.argType)
        val guardArgsFa = FuncApp(actionGuardNames.get(lt).get.get(actionName).get._1 + "$args", guardArgs)(w.pos, w.info, guardArgsType, errT = NoTrafos)
        val oldGuardArgsName = "$oldGuardArgs$" + getFreshInt()
        val oldGuardArgsDecl = LocalVarDecl(oldGuardArgsName, guardArgsType)()
        val oldGuardArgsAssign = LocalVarAssign(oldGuardArgsDecl.localVar, guardArgsFa)()
        // exhale guard
        // inhale lockinv(v)
        val invValDummyName = "$invVal$" + getFreshInt()
        val invValDummyDecl = LocalVarDecl(invValDummyName, lockSpec.t)()
        val invPerms = lockSpec.invariant.withArgs(Seq(lockExp, invValDummyDecl.localVar))

        val inhaleInv = Inhale(invPerms)(w.pos)
        val (whenExpAssume, whenExpVar) = if (whenExp.isDefined) {
          val whenExpTmpName = "$whenExpTmp$" + getFreshInt()
          val whenExpTmpDecl = LocalVarDecl(whenExpTmpName, viper.silver.ast.Bool)()
          val whenExpAssign = LocalVarAssign(whenExpTmpDecl.localVar, whenExp.get)()
          val whenExpAssume = Inhale(whenExpTmpDecl.localVar)()
          (Seq(whenExpAssign, whenExpAssume), Some(whenExpTmpDecl))
        } else {
          (Seq(), None)
        }
        val actionNewVal = a.newVal.replaceT(a.params(0).localVar, invValDummyDecl.localVar).replace(a.params(1).localVar, arg)
        val invAfterAction = lockSpec.invariant.withArgs(Seq(lockExp, actionNewVal))
        val exhaleInvAfterAction = Exhale(invAfterAction)(w.pos)
        // exhale inv(action(v, arg))

        // inhale guard(guardargs ++ arg, lbls)
        val inhaleGuardAfter = Inhale(guardPredAcc)()
        val newGuardArgsExp = if (a.duplicable) {
          AnySetUnion(oldGuardArgsDecl.localVar, ExplicitMultiset(Seq(arg))())()
        } else {
          SeqAppend(oldGuardArgsDecl.localVar, ExplicitSeq(Seq(arg))())()
        }
        val assumeNewGuardArgs = Inhale(EqCmp(guardArgsFa, newGuardArgsExp)())()
        // assert pre(arg) && allpre(oldguardargs) ==> allpre(newguardargs)
        val actionPre = a.pre.replaceT(a.params(0).localVar, invValDummyDecl.localVar).replace(a.params(1).localVar, arg)
        val oldAllPre = SIFLowExp(oldGuardArgsDecl.localVar, Some("allpre$" + lockSpec.name + "$" + a.name))()
        val newAllPre = SIFLowExp(guardArgsFa, Some("allpre$" + lockSpec.name + "$" + a.name))()
        val assertAllPreUpdate = Assert(Implies(And(actionPre, oldAllPre)(), newAllPre)(w.pos))(w.pos)
        Seqn(Seq(assertGuard, oldGuardArgsAssign, exhaleGuard, inhaleInv) ++ whenExpAssume ++ Seq(bod, exhaleInvAfterAction, inhaleGuardAfter, assumeNewGuardArgs, assertAllPreUpdate),
          Seq(oldGuardArgsDecl, invValDummyDecl) ++ whenExpVar.toIterator)(w.pos)
      }
      case m@Merge(lt, actionName, lockExp, lbls1, lbls2) => {
        // merge[lt, actionName](lockExp, lbls1, lbls2) is encoded to
        // assert lbls1 intersect lbls2 == Set()
        // assert acc(guard_a(lockExp, lbls1))
        // assert acc(guard_a(lockExp, lbls2))
        // var tmp1 := guardArgs_a(lockExp, lbls1)
        // var tmp2 := guardArgs_a(lockExp, lbls2)
        // exhale acc(guard_a(lockExp, lbls1)) && acc(guard_a(lockExp, lbls2))
        // inhale guard_a(lockExp, lbls1 union lbls2)
        // assume guardArgs_a(lockExp, lbls1 union lbls2) == tmp1 union tmp2

        val lockSpec = lockSpecs.get(lt).get
        val a = lockSpec.actions.find(la => la.name == actionName).get
        // assert intersect lbls1, lbls2 == empty
        val assertEmptyIntersect = Assert(EqCmp(AnySetIntersection(lbls1, lbls2)(), EmptySet(viper.silver.ast.Int)())())(m.pos)
        // assert guard(lbls1), guard(lbls2)
        val fp = FullPerm()()
        val guardPredLbls1 = PredicateAccess(Seq(lockExp, lbls1), actionGuardNames.get(lt).get.get(actionName).get._1)(m.pos)
        val guardPredAccLbls1 = PredicateAccessPredicate(guardPredLbls1, fp)(m.pos)
        val guardPredLbls2 = PredicateAccess(Seq(lockExp, lbls2), actionGuardNames.get(lt).get.get(actionName).get._1)(m.pos)
        val guardPredAccLbls2 = PredicateAccessPredicate(guardPredLbls2, fp)(m.pos)
        val assertGuards = Assert(And(guardPredAccLbls1, guardPredAccLbls2)(m.pos))(m.pos)
        // remember args1, args2
        val guardArgsType = MultisetType(a.argType)
        val guardArgsLbls1 = FuncApp(actionGuardNames.get(lt).get.get(actionName).get._1 + "$args", Seq(lockExp, lbls1))(m.pos, m.info, guardArgsType, errT = NoTrafos)
        val guardArgsLbls2 = FuncApp(actionGuardNames.get(lt).get.get(actionName).get._1 + "$args", Seq(lockExp, lbls2))(m.pos, m.info, guardArgsType, errT = NoTrafos)
        val oldGuardArgsName = "$oldGuardArgs$" + getFreshInt()
        val oldGuardArgsDecl1 = LocalVarDecl(oldGuardArgsName + "$1", guardArgsType)()
        val oldGuardArgsAssign1 = LocalVarAssign(oldGuardArgsDecl1.localVar, guardArgsLbls1)()
        val oldGuardArgsDecl2 = LocalVarDecl(oldGuardArgsName + "$2", guardArgsType)()
        val oldGuardArgsAssign2 = LocalVarAssign(oldGuardArgsDecl2.localVar, guardArgsLbls2)()
        // exhale guards
        val exhaleGuards = Exhale(And(guardPredAccLbls1, guardPredAccLbls2)(m.pos))(m.pos)
        // inhale guard(lbls1 ++ lbls2, args1 ++ args2)
        val guardPredAfter = PredicateAccess(Seq(lockExp, AnySetUnion(lbls1, lbls2)()), actionGuardNames.get(lt).get.get(actionName).get._1)()
        val guardPredAfterAcc = PredicateAccessPredicate(guardPredAfter, fp)()
        val inhaleAfter = Inhale(guardPredAfterAcc)()
        val guardArgsAfter = FuncApp(actionGuardNames.get(lt).get.get(actionName).get._1 + "$args", Seq(lockExp, AnySetUnion(lbls1, lbls2)()))(m.pos, m.info, guardArgsType, errT = NoTrafos)
        val assumeArgsAfter = Inhale(EqCmp(guardArgsAfter, AnySetUnion(oldGuardArgsDecl1.localVar, oldGuardArgsDecl2.localVar)())())()
        Seqn(Seq(assertEmptyIntersect, assertGuards, oldGuardArgsAssign1, oldGuardArgsAssign2, exhaleGuards, inhaleAfter, assumeArgsAfter), Seq(oldGuardArgsDecl1, oldGuardArgsDecl2))()
      }
      case s@Split(lt, actionName, lockExp, lbls1, lbls2, args1, args2) => {
        // split[lt, actionName](lockExp, lbls1, lbls2, args1, args2) is encoded as
        // assert lbls1 intersect lbls2 == Set()
        // assert guard_a(lockExp, lbls1 union lbls2)
        // assert guardArgs_a(lockExp, lbls1 union lbls2) == args1 union args2
        // inhale guard_a(lockExp, lbls1) && guard_a(lockExp, lbls2)
        // assume guardArgs_a(lockExp, lbls1) == args1 && guardArgs_a(lockExp, lbls2) == args2

        val lockSpec = lockSpecs.get(lt).get
        val a = lockSpec.actions.find(la => la.name == actionName).get
        // assert intersect lbls1, lbls2 == empty
        val assertEmptyIntersect = Assert(EqCmp(AnySetIntersection(lbls1, lbls2)(), EmptySet(viper.silver.ast.Int)())(s.pos))(s.pos)

        // assert guard(lbls ++ lbls2)
        val guardPredCombined = PredicateAccess(Seq(lockExp, AnySetUnion(lbls1, lbls2)()), actionGuardNames.get(lt).get.get(actionName).get._1)(s.pos)
        val fp = FullPerm()()
        val guardPredCombinedAcc = PredicateAccessPredicate(guardPredCombined, fp)(s.pos)

        val assertCombined = Assert(guardPredCombinedAcc)(s.pos)

        // assert guardargs == args1 ++ args2
        val guardArgsType = MultisetType(a.argType)
        val guardArgsCombined = FuncApp(actionGuardNames.get(lt).get.get(actionName).get._1 + "$args", Seq(lockExp, AnySetUnion(lbls1, lbls2)()))(s.pos, s.info, guardArgsType, errT = NoTrafos)
        val assertCombinedSum = Assert(EqCmp(guardArgsCombined, AnySetUnion(args1, args2)())(s.pos))(s.pos)

        // exhale guard
        val exhaleCombined = Exhale(guardPredCombinedAcc)(s.pos)


        // inhale guard(lbls1), guard(lbls2)
        val guardPredLbls1 = PredicateAccess(Seq(lockExp, lbls1), actionGuardNames.get(lt).get.get(actionName).get._1)()
        val guardPredAccLbls1 = PredicateAccessPredicate(guardPredLbls1, fp)()
        val guardPredLbls2 = PredicateAccess(Seq(lockExp, lbls2), actionGuardNames.get(lt).get.get(actionName).get._1)()
        val guardPredAccLbls2 = PredicateAccessPredicate(guardPredLbls2, fp)()
        val inhaleGuards = Inhale(And(guardPredAccLbls1, guardPredAccLbls2)())()
        // assume new guard args
        val guardArgsLbls1 = FuncApp(actionGuardNames.get(lt).get.get(actionName).get._1 + "$args", Seq(lockExp, lbls1))(s.pos, s.info, guardArgsType, errT = NoTrafos)
        val guardArgsLbls2 = FuncApp(actionGuardNames.get(lt).get.get(actionName).get._1 + "$args", Seq(lockExp, lbls2))(s.pos, s.info, guardArgsType, errT = NoTrafos)
        val assumeGuardArgs1 = Inhale(EqCmp(guardArgsLbls1, args1)())()
        val assumeGuardArgs2 = Inhale(EqCmp(guardArgsLbls2, args2)())()

        Seqn(Seq(assertEmptyIntersect, assertCombined, assertCombinedSum, exhaleCombined, inhaleGuards, assumeGuardArgs1, assumeGuardArgs2), Seq())()
      }
      case f@Fork(m, token, args) => {
        // token := fork[m](args) is encoded as
        // exhale m.pre[args/params]
        // havoc(token)
        // inhale acc(joinable_m(token))
        // <for i in 0 ..|args|>
        //   assume joinable_m_i(token) == args(i)

        val havocToken = MethodCall(havocNames.get(Ref).get, Seq(), Seq(token))(f.pos, f.info, NoTrafos)
        val errTrafo = ErrTrafo({
          case ExhaleFailed(_, reason, _) => ForkFailed(f, reason)
        })
        val method = input.findMethod(m)
        var pres = method.pres
        for (i <- 0 until args.length) {
          pres = pres.map(pre => pre.replace(method.formalArgs(i).localVar, args(i)))
        }
        val exhalePres = pres.map(pre => Exhale(pre)(f.pos, errT = errTrafo))
        var joinablePred: Exp = PredicateAccessPredicate(PredicateAccess(Seq(token), joinableNames.get(m).get)(), FullPerm()())(f.pos)
        for (i <- 0 until args.length) {
          val funcApp = FuncApp(joinableFunctions.get(m).get(i), Seq(token))(f.pos)
          val eq = EqCmp(funcApp, args(i))(f.pos)
          joinablePred = And(joinablePred, eq)(f.pos)
        }
        val inhaleJoinable = Inhale(joinablePred)(f.pos)
        Seqn(exhalePres ++ Seq(havocToken, inhaleJoinable), Seq())(f.pos)
      }
      case j@Join(m, resVars, token) => {
        // resVars := join[m](token) is encoded as
        // assert joinable_m(token)
        // <for i in 0 .. |resVars|>
        //   havoc(resVars(i))
        // inhale m.posts[joinable_m_i(token)/params(i)][resVars(j)/m.outParams(j)]
        // exhale joinable_m(token)

        val method = input.findMethod(m)
        val havocTargets = ListBuffer[MethodCall]()
        var posts = method.posts
        val joinablePred = PredicateAccess(Seq(token), joinableNames.get(m).get)()
        val joinableTrafo = NodeTrafo(Joinable(m, token, method.formalArgs.map(fa => AnyValue(fa.typ)()))(j.pos))
        val errTrafo = ErrTrafo({
          case AssertFailed(_, reason, _) => JoinFailed(j, reason)
        })
        val assertJoinable = Assert(PredicateAccessPredicate(joinablePred, FullPerm()())(j.pos, errT = joinableTrafo))(j.pos, errT = errTrafo)
        for (i <- 0 until resVars.length) {
          val havocCall = MethodCall(havocNames.get(resVars(i).typ).get, Seq(), Seq(resVars(i)))(j.pos, j.info, NoTrafos)
          havocTargets.append(havocCall)
          posts = posts.map(post => post.replaceT(method.formalReturns(i).localVar, resVars(i)))
        }
        for (i <- 0 until method.formalArgs.length) {
          val argFuncApp = FuncApp(joinableFunctions.get(m).get(i), Seq(token))()
          posts = posts.map(post => post.replace(method.formalArgs(i).localVar, argFuncApp))
        }
        val exhaleJoinable = Exhale(PredicateAccessPredicate(joinablePred, FullPerm()())())()
        val inhalePosts = posts.map(post => Inhale(post)())
        Seqn(Seq(assertJoinable) ++ havocTargets ++ inhalePosts ++ Seq(exhaleJoinable), Seq())(j.pos)
      }
    }

    // Transform statements, assertions, and expressions.
    var res = withAdded.transform(transformExp orElse transformStmt, Traverse.TopDown)

    // Add intervalSet function and allPre function
    res = res.copy(functions = res.functions.filter(f => f.name != "intervalSet") ++ Seq(getIntervalSetFunction()),
      domains = res.domains ++ Seq(generateAllPre(lockSpecs.values.toSeq)))(res.pos, res.info, res.errT)

    // Construct product program
    val productRes = SIFExtendedTransformer.transform(res, false)

    // Transform quantified permission assertions to normal form.
    // Viper normally does this itself, but because of the way we're invoking Viper that step is skipped and we have
    // to manually perform this step.
    val qpTransformed = productRes.transform({
      case fa: Forall => {
        if (fa.isPure) {
          fa
        } else {
          val desugaredForalls = QuantifiedPermissions.desugarSourceQuantifiedPermissionSyntax(fa)
          desugaredForalls.tail.foldLeft(desugaredForalls.head: Exp)((conjuncts, forall) =>
            And(conjuncts, forall)(fa.pos, fa.info, fa.errT))
        }
      }
    })
    qpTransformed
  }

  /*
   * Creates a domain that declares, for every action a in every given lock specification, a function
   * allPre_a(args1, args2): Bool
   * as well as several axioms to constrain that function.
   * These axioms are not just the general definition of allPre given in the paper, but essentially various special
   * cases of that definition that are useful in practice.
   */
  def generateAllPre(lockSpecs: Seq[LockSpec]): Domain = {
    val domainName = "$all$pre$function$domain"
    val allFuncs: mutable.ListBuffer[DomainFunc] = mutable.ListBuffer()
    val allAxioms: mutable.ListBuffer[DomainAxiom] = mutable.ListBuffer()
    for (lockSpec <- lockSpecs) {
      lockSpec.actions.foreach(a => {
        // generate function declaration
        val fname = "allpre$" + lockSpec.name + "$" + a.name
        val argType = if (a.duplicable) MultisetType(a.argType) else SeqType(a.argType)
        val fstPar = LocalVarDecl("$fst", argType)()
        val sndPar = LocalVarDecl("$snd", argType)()
        val params = Seq(fstPar, sndPar)
        val func = DomainFunc(fname, params, viper.silver.ast.Bool, false)(domainName = domainName)
        allFuncs.append(func)
        val emptyMap = Map[TypeVar, Type]()
        val parFapp = DomainFuncApp(func, Seq(fstPar.localVar, sndPar.localVar), emptyMap)()

        // axiom: allpre(empty, empty)
        val empty_arg: Exp = if (a.duplicable) EmptyMultiset(a.argType)() else EmptySeq(a.argType)()
        val empty_body = DomainFuncApp(func, Seq(empty_arg, empty_arg), emptyMap)()
        val empty_axiom = DomainAxiom("allpre$empty$" + lockSpec.name + "$" + a.name, empty_body)(domainName = domainName)
        allAxioms.append(empty_axiom)

        // axiom: forall v, v' :: allpre({v}, {v'}) == a.pre(v, v')
        val fstVal = LocalVarDecl("$fstV", a.argType)()
        val sndVal = LocalVarDecl("$sndV", a.argType)()
        val fstWrapped = if (a.duplicable) ExplicitMultiset(Seq(fstVal.localVar))() else ExplicitSeq(Seq(fstVal.localVar))()
        val sndWrapped = if (a.duplicable) ExplicitMultiset(Seq(sndVal.localVar))() else ExplicitSeq(Seq(sndVal.localVar))()

        val singletonFapp = DomainFuncApp(func, Seq(fstWrapped, sndWrapped), emptyMap)()
        val ctrlVars = new MethodControlFlowVars(false, false, false, false, scala.Predef.Set[Label]())
        val ctx = TranslationContext(TrueLit()(), TrueLit()(), ctrlVars, null)
        SIFExtendedTransformer.primedNames.update(fstVal.name, sndVal.name)
        val preWithArg = a.pre.replaceT(a.params(1).localVar, fstVal.localVar)
        val preApplied = SIFExtendedTransformer.translateSIFAss(preWithArg, ctx)
        val singletonTrigger = Trigger(Seq(singletonFapp))()
        val singletonBod = EqCmp(singletonFapp, preApplied)()
        val singletonQuant = Forall(Seq(fstVal, sndVal), Seq(singletonTrigger), singletonBod)()
        val singletonAxiom = DomainAxiom("allpre$singleton$" + lockSpec.name + "$" + a.name, singletonQuant)(domainName = domainName)
        allAxioms.append(singletonAxiom)

        if (a.duplicable) {
          if (a.pre == TrueLit()()) {
            // For the special case where a.pre is just true, generate
            // axiom: forall args1, args2 :: allpre(args1, args2) == |args1| == |args2|
            val trueBod = EqCmp(parFapp, EqCmp(AnySetCardinality(fstPar.localVar)(), AnySetCardinality(sndPar.localVar)())())()
            val trueTrigger = Trigger(Seq(parFapp))()
            val trueQuant = Forall(Seq(fstPar, sndPar), Seq(trueTrigger), trueBod)()
            val trueAxiom = DomainAxiom("allpre$true$" + lockSpec.name + "$" + a.name, trueQuant)(domainName = domainName)
            allAxioms.append(trueAxiom)
          } else {
            // For shared action a, generate axiom for adding a single value to each argument multiset:
            // axiom: forall s, s', v, v' :: allpre(s, s') &&  a.pre(v, v') ==> allpre(s union {v}, s' union {v'})
            val fstUnion = AnySetUnion(fstPar.localVar, ExplicitMultiset(Seq(fstVal.localVar))())()
            val sndUnion = AnySetUnion(sndPar.localVar, ExplicitMultiset(Seq(sndVal.localVar))())()
            val unionFapp = DomainFuncApp(func, Seq(fstUnion, sndUnion), emptyMap)()
            val unionTrigger = Trigger(Seq(unionFapp))()
            val unionQuantBod = Implies(And(parFapp, preApplied)(), unionFapp)()
            val unionQuant = Forall(Seq(fstPar, sndPar, fstVal, sndVal), Seq(unionTrigger), unionQuantBod)()
            val unionAxiom = DomainAxiom("allpre$union$" + lockSpec.name + "$" + a.name, unionQuant)(domainName = domainName)
            allAxioms.append(unionAxiom)

            // For shared action a, generate axiom for taking union of argument sets:
            // forall s1, s2, s'1, s'2 :: allpre(s1, s'1) && allpre(s2, s'2) ==> allpre(s1 union s2, s'1 union s'2)
            val fstParP = LocalVarDecl("$fstP", argType)()
            val sndParP = LocalVarDecl("$sndP", argType)()
            val parPFapp = DomainFuncApp(func, Seq(fstParP.localVar, sndParP.localVar), emptyMap)()
            val fstUn = AnySetUnion(fstPar.localVar, fstParP.localVar)()
            val sndUn = AnySetUnion(sndPar.localVar, sndParP.localVar)()
            val unFapp = DomainFuncApp(func, Seq(fstUn, sndUn), emptyMap)()
            val unTrigger = Trigger(Seq(unFapp))()
            val unBody = Implies(And(parFapp, parPFapp)(), unFapp)()
            val unQuant = Forall(Seq(fstPar, sndPar, fstParP, sndParP), Seq(unTrigger), unBody)()
            val unAxiom = DomainAxiom("allpre$un$" + lockSpec.name + "$" + a.name, unQuant)(domainName = domainName)
            allAxioms.append(unAxiom)
          }
        } else {
          if (a.pre == TrueLit()()) {
            // For the special case where a.pre is just true, generate
            // axiom: forall args1, args2 :: allpre(args1, args2) == |args1| == |args2|
            val trueBod = EqCmp(parFapp, EqCmp(SeqLength(fstPar.localVar)(), SeqLength(sndPar.localVar)())())()
            val trueTrigger = Trigger(Seq(parFapp))()
            val trueQuant = Forall(Seq(fstPar, sndPar), Seq(trueTrigger), trueBod)()
            val trueAxiom = DomainAxiom("allpre$true$" + lockSpec.name + "$" + a.name, trueQuant)(domainName = domainName)
            allAxioms.append(trueAxiom)
          } else {
            // For unique action a, generate axiom for adding a single value to each argument sequence:
            // forall s, s', x, x' :: allpre(s, s') && a.pre(x, x') ==> allpre(s ++ [x], s' ++ [x'])
            val fstUnion = SeqAppend(fstPar.localVar, ExplicitSeq(Seq(fstVal.localVar))())()
            val sndUnion = SeqAppend(sndPar.localVar, ExplicitSeq(Seq(sndVal.localVar))())()
            val unionFapp = DomainFuncApp(func, Seq(fstUnion, sndUnion), emptyMap)()
            val unionTrigger = Trigger(Seq(unionFapp))()
            val unionQuantBod = Implies(And(parFapp, preApplied)(), unionFapp)()
            val unionQuant = Forall(Seq(fstPar, sndPar, fstVal, sndVal), Seq(unionTrigger), unionQuantBod)()
            val unionAxiom = DomainAxiom("allpre$append$" + lockSpec.name + "$" + a.name, unionQuant)(domainName = domainName)
            allAxioms.append(unionAxiom)

            // General definition of allpre:
            // forall s, s': allpre(s, s') == |s| == |s'| && forall i: {s[i], s'[i]} i>= 0 && i < |s| ==>  pre(s[i], s'[i])
            val genFapp = DomainFuncApp(func, Seq(fstPar.localVar, sndPar.localVar), emptyMap)()
            val genLenEq = EqCmp(SeqLength(fstPar.localVar)(), SeqLength(sndPar.localVar)())()
            val genInnerVar = LocalVarDecl("_i", viper.silver.ast.Int)()
            val genFirstIndex = SeqIndex(fstPar.localVar, genInnerVar.localVar)()
            val genSecondIndex = SeqIndex(sndPar.localVar, genInnerVar.localVar)()
            val genIndexInBounds = And(GeCmp(genInnerVar.localVar, IntLit(0)())(), LtCmp(genInnerVar.localVar, SeqLength(fstPar.localVar)())())()
            val genPreApplied = preApplied.replace(fstVal.localVar, genFirstIndex).replace(sndVal.localVar, genSecondIndex)
            val genInnerTrigger = Trigger(Seq(genFirstIndex, genSecondIndex))()
            val genInnerForall = Forall(Seq(genInnerVar), Seq(genInnerTrigger), Implies(genIndexInBounds, genPreApplied)())()
            val genBody = And(genLenEq, genInnerForall)()
            val genTrigger = Trigger(Seq(genFapp))()
            val genQuant = Forall(Seq(fstPar, sndPar), Seq(genTrigger), EqCmp(genFapp, genBody)())()
            val genAxiom = DomainAxiom("allpre$seqindex$" + lockSpec.name + "$" + a.name, genQuant)(domainName = domainName)
            allAxioms.append(genAxiom)
          }
        }
      })
    }

    Domain(domainName, allFuncs, allAxioms, Seq())()
  }
}

