package commutativity

import viper.silver.ast.utility.{Expressions, QuantifiedPermissions}
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.{Add, And, Assert, Bool, CondExp, CurrentPerm, EqCmp, ErrTrafo, Exhale, Exp, FieldAccess, FieldAccessPredicate, Forall, FullPerm, FuncApp, Function, GeCmp, GtCmp, Implies, Inhale, IntLit, LeCmp, Let, LocalVar, LocalVarAssign, LocalVarDecl, LtCmp, Method, MethodCall, NoPerm, NoTrafos, Node, NodeTrafo, Perm, PermGeCmp, PermGtCmp, Predicate, PredicateAccess, PredicateAccessPredicate, Program, Ref, Result, Seqn, Stmt, Trafos, Trigger, TrueLit, Type, While, WildcardPerm}
import viper.silver.parser.FastParser._
import viper.silver.parser._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.sif.{SIFExtendedTransformer, SIFLowEventExp, SIFLowExp}
import viper.silver.verifier._
import viper.silver.verifier.errors._

import scala.collection.mutable.ListBuffer
import scala.collection.{Set, mutable}

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

class CommutativityPlugin extends ParserPluginTemplate with SilverPlugin {
  import Extensions._
  var nameCtr = 0

  override val White = PWrapper {
    import fastparse.all._
    NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }
  import White._
  import fastparse.noApi._

  override lazy val newDeclAtEnd = P(lockSpec | barrierSpec)
  override lazy val newExpAtStart = P(pointsToPred | joinable | low | lowEvent | locked | lock | barrier | guard)
  override lazy val newStmtAtStart = P(fork | join | newLock | newBarrier | acquire | release | share | waitStmt)

  lazy val cStyleMethod : P[PMethod] = P(ctyp ~ idndef ~ parens(cvardecl.rep(sep=",")) ~ "{" ~ "}").map{
    case (t, name, params) => PMethod(name, params, Seq(PFormalArgDecl(PIdnDef("$res"), t)), Seq(), Seq(), None)
  }

  lazy val cvardecl : P[PFormalArgDecl] = P(ctyp ~ idndef).map{
    case (t, name) => PFormalArgDecl(name, t)
  }

  lazy val ctyp : P[PType] = P(keyword("int").map(_ => PPrimitiv("Int")) | keyword("bool").map(_ => PPrimitiv("Bool")) | idnuse.map(_ => PPrimitiv("Ref")))

  lazy val fork : P[PFork] = P(idnuse ~ ":=" ~ "fork" ~/ idnuse ~ parens(actualArgList)).map{
    case (t, m, args) => PFork(m, t, args)
  }

  lazy val join : P[PJoin] = P((idnuse.rep(sep = ",") ~ ":=").? ~ "join" ~/ "[" ~ idnuse ~ "]" ~ parens(exp)).map{
    case (targets, m, token) => PJoin(m, if (targets.isDefined) targets.get else Seq(), token)
  }

  lazy val newLock: P[PNewLock] = P(idnuse ~ ":=" ~ "newLock" ~/ "[" ~ idnuse ~ "]" ~ parens(idnuse.rep(sep = ","))).map{
    case (target, lockType, fields) => PNewLock(lockType, target, fields)
  }

  lazy val newBarrier: P[PNewBarrier] = P(idnuse ~ ":=" ~ "newBarrier" ~/ "[" ~ idnuse ~ "]" ~ parens(exp) ~ parens(idnuse.rep(sep = ","))).map{
    case (target, barrierType, n, fields) => PNewBarrier(barrierType, target, n, fields)
  }

  lazy val acquire: P[PAcquire] = P("acquire" ~/ "[" ~ idnuse ~ "]" ~ parens(exp)).map{
    case (lockType, arg) => PAcquire(lockType, arg)
  }

  lazy val release: P[PRelease] = P("release" ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ ("," ~/ idnuse ~ parens(exp)).?)).map{
    case (lockType, (arg, act)) => PRelease(lockType, arg, act)
  }

  lazy val share: P[PShare] = P("share" ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp)).map{
    case (lockType, (arg, value)) => PShare(lockType, arg, value)
  }

  lazy val waitStmt: P[PWait] = P("wait" ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp ~ "," ~ exp)).map{
    case (barrierType, (arg, value, total)) => PWait(barrierType, arg, value, total)
  }

  lazy val lockSpec : P[PLockSpec] = P("lockType" ~/ idndef ~ "{" ~ "type" ~ typ ~ invariantDecl("invariant", 2) ~ alphaDecl ~ (invariantDecl("histInvariant", 2)).? ~ actionDeclList ~ actionDef.rep ~ proof.rep  ~ "}").map{
    case (name, t, i, al, hist, alist, actions, proofs) => PLockSpec(name, t, i, al, hist, alist, actions, proofs)
  }
  lazy val barrierSpec : P[PBarrierSpec] = P("barrierType" ~/ idndef ~ "{" ~ invariantDecl("in", 3) ~ invariantDecl("totalInAfter", 3) ~ invariantDecl("totalOutAfter", 3) ~ invariantDecl("out", 3) ~ "}").map{
    case (name, in, totalIn, totalOut,  out) => PBarrierSpec(name, in, totalIn, totalOut, out)
  }
  def invariantDecl(name: String, nParams: Int) : P[PInvariantDef] = P(name ~/ parens(idndef.rep(sep=",", exactly = nParams)) ~ "=" ~ exp).map{
    case (params, e) => PInvariantDef(params, e)
  }

  lazy val alphaDecl : P[PAlphaDef] = P("alpha" ~/ parens(idndef) ~ ":" ~ typ ~ "=" ~ exp).map{
    case (param, t, e) => PAlphaDef(param, t, e)
  }
  lazy val actionDeclList = P("actions" ~/ "=" ~  "[" ~ actionDecl.rep(sep=",") ~ "]")
  lazy val actionDecl : P[PLockActionDecl] = P("(" ~ idndef ~ "," ~ typ ~ "," ~ (dupl | nondupl) ~ ")").map{
    case (id, t1, d) => PLockActionDecl(id, t1, d.equals("duplicable"))
  }
  lazy val dupl : P[String] = P(keyword("duplicable")).!
  lazy val nondupl : P[String] = P(keyword("unique")).!
  lazy val actionDef : P[PLockActionDef] = P("action" ~/ idnuse ~ parens(idndef.rep(exactly=2, sep=",")) ~
    keyword("requires") ~ exp ~
    "{" ~ exp ~ "}").map{
    case (name, params, pre, newVal) => PLockActionDef(name, params, newVal, pre)
  }
  lazy val proof : P[PProof] = P("proof" ~/ proofType ~ "[" ~ idnuse.rep(sep=",") ~ "]" ~ parens(idndef.rep(sep=",")) ~ "{" ~  stmts ~ "}").map{
    case (ptype, actions, params, pstmt) => PProof(ptype, actions, params, PSeqn(pstmt))
  }
  lazy val proofType : P[String] = P("commutativity".! | "preservation".!)
  lazy val pointsToPred : P[PExp] = P(pointsToPred1 | pointsToPred2)
  lazy val pointsToPred1 : P[PSimplePointsToPredicate] = P("[" ~ fieldAcc ~ ("|->" | ("|-[" ~ term ~ "]->")) ~ (anyVal | exp) ~ "]").map{
    case (fa, p, rhs) => {
      val perm = if (p.isInstanceOf[PExp]) p.asInstanceOf[PExp] else PFullPerm()
      PSimplePointsToPredicate(fa, perm, rhs)
    }
  }
  lazy val pointsToPred2 : P[PVarDefiningPointsToPredicate] = P("[" ~ fieldAcc ~ ("|->" | ("|-[" ~ term ~ "]->")) ~ "?" ~ idndef ~ "&&" ~ exp ~ "]").map{
    case (fa, p, id, body) => {
      val perm = if (p.isInstanceOf[PExp]) p.asInstanceOf[PExp] else PFullPerm()
      PVarDefiningPointsToPredicate(fa, perm, PLet(fa, PLetNestedScope(PFormalArgDecl(id, PUnknown()), body)))
    }
  }

  lazy val anyVal : P[PExp] = P("_").map{case _ => PAnyVal()}
  lazy val joinable : P[PJoinable] = P(keyword("joinable") ~/ "[" ~ idnuse ~ "]" ~ parens(exp.rep(min=1, sep=","))).map{
    case (method, args) => PJoinable(method, args(0), args.tail)
  }
  lazy val low : P[PLow] = P(keyword("low") ~/ parens(exp)).map{
    case arg => PLow(arg)
  }
  lazy val lowEvent : P[PLowEvent] = P(keyword("lowEvent")).map{
    case arg => PLowEvent()
  }
  lazy val locked : P[PLocked] = P(keyword("locked") ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp)).map{
    case (ltype, (argLock, argVal)) => PLocked(ltype, argLock, argVal)
  }
  lazy val seen : P[PSeen] = P(keyword("seen") ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp)).map{
    case (ltype, (argLock, argVal)) => PSeen(ltype, argLock, argVal)
  }
  lazy val lock : P[PLock] = P(keyword("lock") ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp)).map{
    case (ltype, (argLock, argVal)) => PLock(ltype, argLock, argVal)
  }
  lazy val guard : P[PGuard] = P(keyword("guard") ~/ "[" ~ idnuse ~"," ~ idnuse ~ "]" ~ parens(exp)).map{
    case (ltype, argLock, argVal) => PGuard(ltype, argLock, argVal)
  }
  lazy val barrier : P[PBarrier] = P(keyword("barrier") ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp ~ "," ~ exp)).map{
    case (btype, (argBarrier, index, total)) => PBarrier(btype, argBarrier, index, total)
  }

  override lazy val extendedKeywords = Set("lockType", "action", "invariant", "alpha", "proof", "reordering", "commutativity", "preservation", "locked", "lock", "guard", "joinable", "duplicable", "unique")

  override def beforeParse(input: String, isImported: Boolean): String = {
    ParserExtension.addNewDeclAtEnd(newDeclAtEnd)
    ParserExtension.addNewExpAtStart(newExpAtStart)
    ParserExtension.addNewKeywords(extendedKeywords)
    ParserExtension.addNewStmtAtStart(newStmtAtStart)
    input
  }

  override def beforeResolve(input: PProgram): PProgram = {
    input.transform({
      case PDomainType(name, args) if name.name == "Lock" && args.length == 0 => PPrimitiv("Ref")
      case PDomainType(name, args) if name.name == "Thread" && args.length == 0 => PPrimitiv("Ref")
      case PDomainType(name, args) if name.name == "Barrier" && args.length == 0 => PPrimitiv("Ref")
      case PAssume(e) => PInhale(e)
    })()
  }

  def getFreshInt(): Int = {
    nameCtr += 1
    nameCtr - 1
  }


  override def beforeConsistencyCheck(input: Program): Program = {

    val lockSpecs = mutable.HashMap[String, LockSpec]()
    val barrierSpecs = mutable.HashMap[String, BarrierSpec]()
    val lockPredNames = mutable.HashMap[String, String]()
    val lockedPredNames = mutable.HashMap[String, String]()
    val barrierPredNames = mutable.HashMap[String, String]()
    val lockedFuncNames = mutable.HashMap[String, String]()
    val seenFuncNames = mutable.HashMap[String, String]()
    val actionGuardNames = mutable.HashMap[String, mutable.HashMap[String, String]]()
    val bottomFuncNames = mutable.HashMap[String, String]()

    input.extensions.foreach{
      case l@LockSpec(name, t, inv, alpha, hist, actions, proofs) => {
        if (!Expressions.isPure(alpha.exp)){
          reportError(TypecheckerError("Abstraction function must be pure", alpha.exp.pos))
        }
        if (hist.isDefined && !Expressions.isPure(hist.get.inv)){
          reportError(TypecheckerError("History invariant must be pure", hist.get.inv.pos))
        }
        inv.inv.visit{
          case _: Lock => reportError(TypecheckerError("Invariants must not contain lock() assertions.", inv.inv.pos))
          case _: Locked => reportError(TypecheckerError("Invariants must not contain locked() assertions.", inv.inv.pos))
          case _: Barrier => reportError(TypecheckerError("Invariants must not contain barrier() assertions.", inv.inv.pos))
        }

        lockSpecs.update(name, l)
        lockPredNames.update(name, "$lockpred$" + name)
        lockedPredNames.update(name, "$lockedpred$" + name)
        lockedFuncNames.update(name, "$lockedfunc$" + name)
        seenFuncNames.update(name, "$seenfunc$" + name)
        bottomFuncNames.update(name, "$bottomfunc$" + name)
        val guardNames = mutable.HashMap[String, String]()
        actionGuardNames.update(name, guardNames)


        for (a <- actions){
          guardNames.update(a.name, "$guard$"+name+"$"+a.name)
          if (!Expressions.isPure(a.pre)){
            reportError(TypecheckerError("Precondition must be pure", a.pre.pos))
          }
          if (a.pre.existsDefined{
            case LocalVar(name, _) if name == a.params(0).name => true
          }) {
            reportError(TypecheckerError("Precondition must not constrain lock state", a.pre.pos))
          }
          if (!Expressions.isPure(a.newVal)){
            reportError(TypecheckerError("Action definition must be pure", a.newVal.pos))
          }
        }
      }
      case b@BarrierSpec(name, in, totalIn, totalOut, out) => {
        Seq(in, totalIn, totalOut, out).foreach(i =>
          i.inv.visit{
            case _: Barrier => reportError(TypecheckerError("Barrier assertions must not contain barrier() assertions.", i.inv.pos))
            case _: Lock => reportError(TypecheckerError("Barrier assertions must not contain lock() assertions.", i.inv.pos))
          }
        )
        barrierSpecs.update(name, b)
        barrierPredNames.update(name, "$barrierpred$" + name)
      }
    }
    val newMethods = ListBuffer[Method]()
    val havocNames = mutable.HashMap[Type, String]()
    val joinableNames = mutable.HashMap[String, String]()
    val joinablePreds = mutable.HashMap[String, Predicate]()
    val joinableFunctions = mutable.HashMap[String, ListBuffer[Function]]()
    for (m <- input.methods) {
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
      val name = "$$havoc$" + getFreshInt()
      havocNames.update(Ref, name)
      val resVar = LocalVarDecl(name + "$res", Ref)()
      val newMethod = Method(name, Seq(), Seq(resVar), Seq(), Seq(), None)()
      newMethods.append(newMethod)
      for (arg <- m.formalReturns) {
        if (!havocNames.contains(arg.typ)){
          val name = "$$havoc$" + getFreshInt()
          havocNames.update(arg.typ, name)
          val resVar = LocalVarDecl(name + "$res", arg.typ)()
          val newMethod = Method(name, Seq(), Seq(resVar), Seq(), Seq(), None)()
          newMethods.append(newMethod)
        }
      }
    }
    val lockPreds = lockPredNames.map(n => Predicate(n._2, Seq(LocalVarDecl("$rec", Ref)()), None)())
    val lockedPreds = lockedPredNames.map(n => Predicate(n._2, Seq(LocalVarDecl("$rec", Ref)()), None)())
    val lockedFuncs = lockedFuncNames.map(e => Function(e._2, Seq(LocalVarDecl("$rec", Ref)()), lockSpecs.get(e._1).get.t, Seq(PredicateAccessPredicate(PredicateAccess(Seq(LocalVar("$rec", Ref)()), lockedPredNames.get(e._1).get)(), FullPerm()())()), Seq(), None)())
    val seenFuncs = seenFuncNames.map(e => Function(e._2, Seq(LocalVarDecl("$rec", Ref)(), LocalVarDecl("val", lockSpecs.get(e._1).get.t)()), Bool, Seq(), Seq(), None)())
    val guardPreds = actionGuardNames.map(ls => ls._2.map(a => Predicate(a._2, Seq(LocalVarDecl("$rec", Ref)()), None)())).flatten
    val bottomFuncs = bottomFuncNames.map(n => Function(n._2, Seq(), lockSpecs.get(n._1).get.t, Seq(), Seq(), None)())
    val barrierPreds = barrierPredNames.map(n => Predicate(n._2, Seq(LocalVarDecl("$rec", Ref)(), LocalVarDecl("$ind", viper.silver.ast.Int)(), LocalVarDecl("$tot", viper.silver.ast.Int)()), None)())


    val newPredicates : Seq[Predicate] = input.predicates ++ joinablePreds.values ++ lockPreds ++ lockedPreds ++ guardPreds ++ barrierPreds
    val newFunctions : Seq[Function] = input.functions ++ bottomFuncs ++ lockedFuncs ++ joinableFunctions.values.flatten ++ seenFuncs

    input.methods.foreach(newMethods.append(_))


    input.extensions.foreach{
      case l@LockSpec(name, t, inv, alpha, hist, actions, proofs) => {

        if (hist.isDefined) {
          ////// history invariant is reflexive and transitive
          // declare 2 locks, 2 value vars
          val transLockVar1 = LocalVarDecl("$transVar1$" + getFreshInt(), Ref)()
          val transLockVar2 = LocalVarDecl("$transVar2$" + getFreshInt(), Ref)()
          val transLockVar3 = LocalVarDecl("$transVar3$" + getFreshInt(), Ref)()
          val transVal1 = LocalVarDecl("$transVar1$" + getFreshInt(), t)()
          val transVal2 = LocalVarDecl("$transVar2$" + getFreshInt(), t)()
          val transVal3 = LocalVarDecl("$transVar3$" + getFreshInt(), t)()

          // inhale inv
          val transInv1 = inv.withArgs(Seq(transLockVar1.localVar, transVal1.localVar))
          val transInv2 = inv.withArgs(Seq(transLockVar2.localVar, transVal2.localVar))
          val transInv3 = inv.withArgs(Seq(transLockVar3.localVar, transVal3.localVar))

          // reflexive
          val transRefl = hist.get.withArgs(Seq(transVal1.localVar, transVal1.localVar))

          // transitive assumptions
          val transAss1 = hist.get.withArgs(Seq(transVal1.localVar, transVal2.localVar))
          val transAss2 = hist.get.withArgs(Seq(transVal2.localVar, transVal3.localVar))

          // transitive to prove
          val trans = hist.get.withArgs(Seq(transVal1.localVar, transVal3.localVar))
          val transParams = Seq(transLockVar1, transLockVar2, transLockVar3, transVal1, transVal2, transVal3)
          val transPres = Seq(transInv1, transInv2, transInv3)
          val reflTrafo = ErrTrafo({
            case AssertFailed(node, reason, _) => HistoryNotReflexive(name, node, reason)
          })
          val transTrafo = ErrTrafo({
            case AssertFailed(node, reason, _) => HistoryNotTransitive(name, node, reason)
          })
          val transAssertRefl = Assert(transRefl)(l.pos, errT=reflTrafo)
          val transAssumptions = Inhale(And(transAss1, transAss2)(l.pos))(l.pos)
          val transAssertTrans = Assert(trans)(l.pos, errT=transTrafo)
          val transBody = Some(Seqn(Seq(transAssertRefl, transAssumptions, transAssertTrans), Seq())(l.pos))
          val transMethod = Method("$histtrans$" + name + getFreshInt(), transParams, Seq(), transPres, Seq(), transBody)(l.pos)
          newMethods.append(transMethod)
        }

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
        val sameVal = EqCmp(udVal1.localVar, udVal2.localVar)(l.pos, errT=uniquenessTrafo)

        val udMethod = Method("$udCheck$" + name + "$" + getFreshInt(), Seq(udLockVar, udVal1, udVal2), Seq(), Seq(perms, valDef1, valDef2), Seq(sameVal), Some(Seqn(Seq(), Seq())()))(l.pos, errT=uniquenessTrafo)
        newMethods.append(udMethod)

        /////// alpha is well-defined
        val alphaWDV = LocalVarDecl("$alphaWDVar$" + getFreshInt(), t)()
        val alphaWDInv = alpha.lowWithArg(alphaWDV.localVar)
        val alphaWDMethod = Method("$secWD$" + name + "$" + getFreshInt(), Seq(alphaWDV), Seq(), Seq(alphaWDInv), Seq(), None)(l.pos)
        newMethods.append(alphaWDMethod)

        for (a <- actions){

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
          val presFinalValEq = EqCmp(presFinalVar.localVar, presFinalVal)(presFinalVal.pos, errT=NodeTrafo(presFinalVal))

          // assert alpha is low
          val preservationTrafo = ErrTrafo({
            case PostconditionViolated(node, _, reason, _) => PreservationCheckFailed(a.name, node, reason)
          })
          //val presPostcond = a.post.replaceT(a.params(0).localVar, presOrigVar.localVar).replaceT(a.params(1).localVar, presArgVar.localVar).replaceT(Result(a.retType)(), presRetVar.localVar)
          val presSecInvFinal = alpha.lowWithArg(presFinalVar.localVar)
          val presProof = proofs.find(p => p.proofType == "preservation" && p.actions.length == 1 && p.actions(0) == a.name)
          val presBody = presProof match {
            case None => Some(Seqn(Seq(), Seq())())
            case Some(p) => Some(p.body.replaceT(p.params(0).localVar, presOrigVar.localVar).replaceT(p.params(1).localVar, presArgVar.localVar))
          }
          val presPosts = Seq((presSecInvFinal, SIFLowExp(alpha.exp)())).map{case (p: Exp, po: Exp) => EqCmp(TrueLit()(), p)(a.pos, errT=Trafos(List({
            case PostconditionViolated(node, _, reason, _) => PreservationCheckFailed(a.name, node, reason)
          }), List(), Some(po)))}
          val presMethod = Method("$presCheck$" + getFreshInt(), Seq(presOrigVar, presArgVar, presFinalVar), Seq(), Seq(presSecInv, presPrecond, presFinalValEq), presPosts, presBody)(a.pos, errT=preservationTrafo)
          newMethods.append(presMethod)


          if (hist.isDefined) {
            // action preserves inv
            val aHistLockVar = LocalVarDecl("$ahVar$" + getFreshInt(), Ref)()
            val aHistVal = LocalVarDecl("$ahVar$" + getFreshInt(), t)()
            val aHistArg = LocalVarDecl("$ahArg$" + getFreshInt(), a.argType)()
            val aHistRes = LocalVarDecl("$ahRes$" + getFreshInt(), t)()
            val ahInv = inv.withArgs(Seq(aHistLockVar.localVar, aHistVal.localVar))
            val ahPre = a.pre.replaceT(a.params(0).localVar, aHistVal.localVar).replaceT(a.params(1).localVar, aHistArg.localVar)
            val ahResDef = EqCmp(aHistRes.localVar, a.newVal.replaceT(a.params(0).localVar, aHistVal.localVar).replaceT(a.params(1).localVar, aHistArg.localVar))(l.pos)
            val ahHist = hist.get.withArgs(Seq(aHistVal.localVar, aHistRes.localVar))
            val ahParams = Seq(aHistLockVar, aHistVal, aHistArg, aHistRes)
            val ahPres = Seq(ahInv, ahPre, ahResDef)
            val ahError = ErrTrafo({
              case PostconditionViolated(node, _, reason, _) => HistoryNotPreserved(name, a.name, node, reason)
            })
            val ahPosts = Seq(EqCmp(TrueLit()(), ahHist)(l.pos, errT=ahError))
            val ahBody = Some(Seqn(Seq(), Seq())(l.pos))
            val ahMethod = Method("$ah$" + name + "$" + a.name + "$" + getFreshInt(), ahParams, Seq(), ahPres, ahPosts, ahBody)()
            newMethods.append(ahMethod)
          }

          ////// (optional) precondition implies welldef of newVal


          ////// (optional) precondition implies welldef of retVal


          ////// (optional) precondition implies welldef of post

          val a1 = a
          for (a2 <- actions){
            if (actions.indexOf(a1) < actions.indexOf(a2) || (a1 == a2 && a1.duplicable)){
              // for every action with every other action including itself

              /*
              ////// actions can be reordered
              // all vars
              val reoOrigDecl = LocalVarDecl("$reoOrig$" + getFreshInt(), t)()
              val reoArg1Decl = LocalVarDecl("$reoArg1$" + getFreshInt(), a1.argType)()
              val reoArg2Decl = LocalVarDecl("$reoArg2$" + getFreshInt(), a2.argType)()
              val reoTmpOpt1Decl = LocalVarDecl("$reoTmpOpt11$" + getFreshInt(), t)()
              val reoTmpOpt2Decl = LocalVarDecl("$reoTmpOpt2$" + getFreshInt(), t)()

              // assumptions: secinv, opt1 pres hold
              val reoOrigSecInv = secInv.withArgs(Seq(reoOrigDecl.localVar))
              val reoOpt1Pre2 = a2.pre.replaceT(a2.params(0).localVar, reoOrigDecl.localVar).replaceT(a2.params(1).localVar, reoArg2Decl.localVar)
              val reoOpt1TmpVal = a2.newVal.replaceT(a2.params(0).localVar, reoOrigDecl.localVar).replaceT(a2.params(1).localVar, reoArg2Decl.localVar)
              val reoOpt1TmpDef = EqCmp(reoTmpOpt1Decl.localVar, reoOpt1TmpVal)(reoOpt1TmpVal.pos, errT=NodeTrafo(reoOpt1TmpVal))
              val reoOpt1Pre1 = a1.pre.replaceT(a1.params(0).localVar, reoTmpOpt1Decl.localVar).replaceT(a1.params(1).localVar, reoArg1Decl.localVar)

              // opt2 pres hold
              val reorderingTrafo = ErrTrafo({
                case PostconditionViolated(node, _, reason, _) => ReorderingCheckFailed(a1.name, a2.name, node, reason)
              })
              val reoOpt2Pre1: Exp = a1.pre.replaceT(a1.params(0).localVar, reoOrigDecl.localVar).replaceT(a1.params(1).localVar, reoArg1Decl.localVar)
              val reoOpt2TmpVal = a1.newVal.replaceT(a1.params(0).localVar, reoOrigDecl.localVar).replaceT(a1.params(1).localVar, reoArg1Decl.localVar)
              val reoOpt2TmpDef = EqCmp(reoTmpOpt2Decl.localVar, reoOpt2TmpVal)(a1.pos, errT=reorderingTrafo)
              val reoOpt2Pre2 = a2.pre.replaceT(a2.params(0).localVar, reoTmpOpt2Decl.localVar).replaceT(a2.params(1).localVar, reoArg2Decl.localVar)
              val reoOpt2Pre2Impl = Implies(reoOpt2TmpDef, reoOpt2Pre2)(a1.pos, errT=reorderingTrafo)

              val reoName = "$reoCheck$" + a1.name + "$" + a2.name + "$" + getFreshInt()
              val reoParams = Seq(reoOrigDecl, reoArg1Decl, reoArg2Decl, reoTmpOpt1Decl, reoTmpOpt2Decl)
              val reoPres = Seq(reoOrigSecInv, reoOpt1Pre2, reoOpt1TmpDef, reoOpt1Pre1)
              val reoPosts = Seq((reoOpt2Pre1, a1.pre), (reoOpt2Pre2Impl, a2.pre)).map{case (p, po) => EqCmp(TrueLit()(), p)(a1.pos, errT=Trafos(List({
                case PostconditionViolated(node, _, reason, _) => ReorderingCheckFailed(a1.name, a2.name, node, reason)
              }), List(), Some(po)))}

              val reoProof = proofs.find(p => p.proofType == "reordering" && p.actions(0) == a1.name && p.actions(1) == a2.name)
              val reoBody = if (reoProof.isDefined){
                reoProof.get.body.replaceT(reoProof.get.params(0).localVar, reoOrigDecl.localVar).replaceT(reoProof.get.params(1).localVar, reoArg1Decl.localVar).replaceT(reoProof.get.params(2).localVar, reoArg2Decl.localVar)
              }else{
                Seqn(Seq(), Seq())()
              }
              val reoMethod = Method(reoName, reoParams, Seq(), reoPres, reoPosts, Some(reoBody))(a1.pos, errT=reorderingTrafo)
              newMethods.append(reoMethod)

              */

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
              val commResA1 = EqCmp(commRes1Decl.localVar, a1.newVal.replaceT(a1.params(0).localVar, commOrig1Decl.localVar).replaceT(a1.params(1).localVar, commArg1Decl.localVar))(a1.newVal.pos, errT=NodeTrafo(a1.newVal))
              val commResA2 = EqCmp(commRes2Decl.localVar, a2.newVal.replaceT(a2.params(0).localVar, commOrig2Decl.localVar).replaceT(a2.params(1).localVar, commArg2Decl.localVar))(a2.newVal.pos, errT=NodeTrafo(a2.newVal))

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
              val commPres = Seq(commPreA1, commPreA2, commOrigSecInv, commResA1, commResA2, commOptions)
              val commPosts = Seq((commCheckSecInv, SIFLowExp(alpha.exp)())).map{case (p, po) => EqCmp(TrueLit()(), p)(a1.pos, errT=Trafos(List({
                case PostconditionViolated(node, _, reason, _) => CommutativityCheckFailed(a1.name, a2.name, node, reason)
              }), List(), Some(po)))}

              val commProof = proofs.find(p => p.proofType == "commutativity" && p.actions(0) == a1.name && p.actions(1) == a2.name)
              val commBody = if (commProof.isDefined){
                commProof.get.body.replaceT(commProof.get.params(0).localVar, commOrigDecl.localVar).replaceT(commProof.get.params(1).localVar, commArg1Decl.localVar).replaceT(commProof.get.params(2).localVar, commArg2Decl.localVar)
              }else{
                Seqn(Seq(), Seq())()
              }
              val commMethod = Method(commName, commParams, Seq(), commPres, commPosts, Some(commBody))(a1.pos, errT=commutativityTrafo)
              newMethods.append(commMethod)
            }
          }
        }
      }
      case b@BarrierSpec(name, in, totalIn, totalOut, out) => {
        val inOutBarrier = LocalVarDecl("$barrier$" + getFreshInt(), Ref)()
        val inOutN = LocalVarDecl("$nthreads$" + getFreshInt(), viper.silver.ast.Int)()
        val inOutI = LocalVarDecl("$ithreads$" + getFreshInt(), viper.silver.ast.Int)()
        val zero = IntLit(0)()
        val one = IntLit(1)()
        val setToZero = LocalVarAssign(inOutI.localVar, zero)()
        val increment = LocalVarAssign(inOutI.localVar, Add(inOutI.localVar, one)())()
        val iInBoundsInv = And(GeCmp(inOutI.localVar, zero)(), LeCmp(inOutI.localVar, inOutN.localVar)())()
        val iCond = LtCmp(inOutI.localVar, inOutN.localVar)()
        val firstLoopTrafo = ErrTrafo({
          case LoopInvariantNotEstablished(node, reason, _) => BarrierInvalidTotalInTrueAtZero(node, reason)
          case LoopInvariantNotPreserved(node, reason, _) => BarrierInvalidInEstablishesTotalIn(node, reason)
        })
        val secondLoopTrafo = ErrTrafo({
          case LoopInvariantNotEstablished(node, reason, _) => BarrierInvalidTotalInImpliesTotalOut(node, reason)
          case LoopInvariantNotPreserved(node, reason, _) => BarrierInvalidTotalOutEstablishesOut(node, reason)
          case ExhaleFailed(node, reason, _) => BarrierInvalidTotalOutEstablishesOut(node, reason)
        })

        val inToInhale = And(TrueLit()(), in.withArgs(Seq(inOutBarrier.localVar, inOutI.localVar, inOutN.localVar)))(b.pos, errT=firstLoopTrafo)
        val outToExhale = And(TrueLit()(), out.withArgs(Seq(inOutBarrier.localVar, inOutI.localVar, inOutN.localVar)))(b.pos, errT=secondLoopTrafo)
        val totalInInvariant = And(TrueLit()(), totalIn.withArgs(Seq(inOutBarrier.localVar, inOutI.localVar, inOutN.localVar)))(b.pos, errT=firstLoopTrafo)
        val totalOutInvariant = And(TrueLit()(), totalOut.withArgs(Seq(inOutBarrier.localVar, inOutI.localVar, inOutN.localVar)))(b.pos, errT=secondLoopTrafo)
        val firstBody = Seqn(Seq(Inhale(inToInhale)(b.pos), increment), Seq())()
        val secondBody = Seqn(Seq(Exhale(outToExhale)(b.pos, errT=secondLoopTrafo), increment), Seq())(b.pos, errT=secondLoopTrafo)
        val firstLoop = While(iCond, Seq(iInBoundsInv, totalInInvariant), firstBody)(b.pos, errT=firstLoopTrafo)
        val secondLoop = While(iCond, Seq(iInBoundsInv, totalOutInvariant), secondBody)(b.pos, errT=secondLoopTrafo)
        val totalBody = Seqn(Seq(setToZero, firstLoop, setToZero, secondLoop), Seq(inOutI))()
        val nIsPositive = GtCmp(inOutN.localVar, zero)()
        val inOutName = "$inOut$" + name + getFreshInt()
        val inOutMethod = Method(inOutName, Seq(inOutBarrier, inOutN), Seq(), Seq(nIsPositive), Seq(), Some(totalBody))()
        newMethods.append(inOutMethod)
      }
    }

    val withAdded = input.copy(extensions = Seq(), predicates = newPredicates, functions = newFunctions, methods = newMethods)(input.pos, input.info, input.errT)

    val res = withAdded.transform({
      case pt@PointsToPredicate(fa, p, None) => FieldAccessPredicate(fa, p)(pt.pos, errT=NodeTrafo(pt))
      case pt@PointsToPredicate(fa, p, Some(e)) => And(FieldAccessPredicate(fa, p)(), EqCmp(fa, e)(pt.pos, errT=NodeTrafo(pt)))(pt.pos, errT=NodeTrafo(pt))
      case pt@VarDefiningPointsToPredicate(fa, p, v, Some(b)) => And(FieldAccessPredicate(fa, p)(pt.pos, errT=NodeTrafo(pt)), Let(v, fa, b)(pt.pos, errT=NodeTrafo(pt)))(pt.pos, errT=NodeTrafo(pt))
      case pt@VarDefiningPointsToPredicate(fa, p, v, None) => FieldAccessPredicate(fa, p)(pt.pos, errT=NodeTrafo(pt))
      case pt@Joinable(m, e, args) => {
        val pa = PredicateAccess(Seq(e), joinableNames.get(m).get)()
        val pap = PredicateAccessPredicate(pa, FullPerm()())(pt.pos, errT=NodeTrafo(pt))
        var res : Exp =  pap
        for (i <- 0 until args.length){
          val funcApp = EqCmp(FuncApp(joinableFunctions.get(m).get(i), Seq(e))(pt.pos, errT=NodeTrafo(pt)), args(i))(pt.pos, errT=NodeTrafo(pt))
          res = And(res, funcApp)(pt.pos, errT=NodeTrafo(pt))
        }
        res
      }
      case pt@Lock(lt, r, amount) => {
        val pa = PredicateAccess(Seq(r), lockPredNames.get(lt).get)()
        PredicateAccessPredicate(pa, amount)(pt.pos, errT=NodeTrafo(pt))
      }
      case pt@Barrier(bt, r, index, total) => {
        val pa = PredicateAccess(Seq(r, index, total), barrierPredNames.get(bt).get)()
        PredicateAccessPredicate(pa, FullPerm()())(pt.pos, errT=NodeTrafo(pt))
      }
      case l@Locked(lt, r, value) => {
        val pt = l
        val pa = PredicateAccess(Seq(r), lockedPredNames.get(lt).get)()
        val pap = PredicateAccessPredicate(pa, FullPerm()())(pt.pos, errT=NodeTrafo(pt))
        val funcApp = FuncApp(lockedFuncNames.get(lt).get, Seq(r))(l.pos, l.info, lockSpecs.get(lt).get.t, NoTrafos)
        val eq = EqCmp(funcApp, value)(pt.pos, errT=NodeTrafo(pt))
        And(pap, eq)(pt.pos, errT=NodeTrafo(pt))
      }
      case l@Seen(lt, r, value) => {
        val pt = l
        val fa = FuncApp(seenFuncNames.get(lt).get, Seq(r, value))(pt.pos, pt.info, Bool, NodeTrafo(l))
        fa
      }
      case pt@Guard(lt, g, lock) => {
        val action = lockSpecs.get(lt).get.actions.find(a => a.name == g).get
        val pa = PredicateAccess(Seq(lock), actionGuardNames.get(lt).get.get(g).get)()
        PredicateAccessPredicate(pa, if (action.duplicable) WildcardPerm()() else FullPerm()())(pt.pos, errT=NodeTrafo(pt))
      }
      case nl@NewLock(lt, target, fields) => {
        val pt = nl
        val lockSpec = lockSpecs.get(lt).get
        val newStmt = MethodCall(havocNames.get(Ref).get, Seq(), Seq(target))(nl.pos, nl.info, NoTrafos)
        val fp = FullPerm()()
        val fieldPermInhales = ListBuffer[Inhale]()
        for (field <- fields) {
          val predAcc = FieldAccessPredicate(FieldAccess(target, field)(), fp)()
          fieldPermInhales.append(Inhale(predAcc)())
        }
        val lockPredAcc = PredicateAccess(Seq(target), lockPredNames.get(lt).get)()
        val lockPred = PredicateAccessPredicate(lockPredAcc, fp)()
        val bottomApp = FuncApp(bottomFuncNames.get(lt).get, Seq())(nl.pos, nl.info, lockSpecs.get(lt).get.t, NoTrafos)
        val lockedPredAcc = PredicateAccess(Seq(target), lockedPredNames.get(lt).get)()
        val lockedPred = PredicateAccessPredicate(lockedPredAcc, fp)(pt.pos, errT=NodeTrafo(pt))
        val lockedValue = FuncApp(lockedFuncNames.get(lt).get, Seq(target))(nl.pos, nl.info, lockSpec.t, NoTrafos)
        val lockedBottom = EqCmp(lockedValue, bottomApp)(pt.pos, errT=NodeTrafo(pt))
        val inhale = Inhale(And(lockPred, And(lockedPred, lockedBottom)(pt.pos, errT=NodeTrafo(pt)))(pt.pos, errT=NodeTrafo(pt)))(pt.pos, errT=NodeTrafo(pt))
        val guardInhales = ListBuffer[Inhale]()
        val guardNames = actionGuardNames.get(lt).get
        for (a <- lockSpec.actions){
          val pa = PredicateAccess(Seq(target), guardNames.get(a.name).get)()
          guardInhales.append(Inhale(PredicateAccessPredicate(pa, fp)(pt.pos, errT=NodeTrafo(pt)))(pt.pos, errT=NodeTrafo(pt)))
        }
        Seqn(Seq(newStmt, inhale) ++ fieldPermInhales ++ guardInhales, Seq())(pt.pos, errT=NodeTrafo(pt))
      }
      case nl@NewBarrier(bt, target, n, fields) => {
        val pt = nl
        val nPositive = GtCmp(n, IntLit(0)())(nl.pos)
        val errTrafo = ErrTrafo({
          case AssertFailed(_, error, _) => NewBarrierFailed(nl, error)
        })
        val assertNPositive = Assert(nPositive)(nl.pos, errT=errTrafo)
        val barrierSpec = barrierSpecs.get(bt).get
        val newStmt = MethodCall(havocNames.get(Ref).get, Seq(), Seq(target))(nl.pos, nl.info, NoTrafos)
        val fp = FullPerm()()
        val fieldPermInhales = ListBuffer[Inhale]()
        for (field <- fields) {
          val predAcc = FieldAccessPredicate(FieldAccess(target, field)(), fp)()
          fieldPermInhales.append(Inhale(predAcc)())
        }
        val iDecl = LocalVarDecl("$newbarrier$i$" + getFreshInt(), viper.silver.ast.Int)()
        val zero = IntLit(0)()
        val iInBounds = And(GeCmp(iDecl.localVar, zero)(), LtCmp(iDecl.localVar, n)())(nl.pos)
        val barrierPredAcc = PredicateAccess(Seq(target, iDecl.localVar, n), barrierPredNames.get(bt).get)(nl.pos)
        val barrierPred = PredicateAccessPredicate(barrierPredAcc, fp)(nl.pos)
        val impl = Implies(iInBounds, barrierPred)(nl.pos)
        val quantifier = Forall(Seq(iDecl), Seq(), impl)(nl.pos)
        val inhaleBarrierPreds = Inhale(quantifier)(nl.pos)
        Seqn(Seq(assertNPositive, newStmt, inhaleBarrierPreds) ++ fieldPermInhales, Seq())(pt.pos, errT=NodeTrafo(pt))
      }
      case w@Wait(bt, barrierExp, index, total) => {
        val errTrafo = ErrTrafo({
          case AssertFailed(_, reason, _) => WaitFailed(w, reason)
          case ExhaleFailed(_, reason, _) => WaitFailed(w, reason)
        })
        val barrierSpec = barrierSpecs.get(bt).get
        val barrierPred = PredicateAccess(Seq(barrierExp, index, total), barrierPredNames.get(bt).get)(w.pos)
        val barrierTrafo = NodeTrafo(Barrier(bt, barrierExp, index, total)(w.pos))
        val assertBarrierPred = Assert(PredicateAccessPredicate(barrierPred, FullPerm()())(w.pos, errT=barrierTrafo))(w.pos, errT=errTrafo)
        val exhaleIn = Exhale(barrierSpec.in.withArgs(Seq(barrierExp, index, total)))(w.pos, errT=errTrafo)
        val inhaleOut = Inhale(barrierSpec.out.withArgs(Seq(barrierExp, index, total)))(w.pos)
        Seqn(Seq(assertBarrierPred, exhaleIn, inhaleOut), Seq())()
      }
      case a@Acquire(lt, lockExp) => {
        val lockSpec = lockSpecs.get(lt).get
        val invValVarName = "$invVal$" + getFreshInt()
        val invValVarDecl = LocalVarDecl(invValVarName, lockSpec.t)()
        val errTrafo = ErrTrafo({
          case AssertFailed(_, reason, _) => AcquireFailed(a, reason)
        })
        val lockPredAcc = PredicateAccess(Seq(lockExp), lockPredNames.get(lt).get)()
        val lockPerm = CurrentPerm(lockPredAcc)()
        // check lock type
        val lockErrorNode =  Lock(lt, lockExp, AnyValue(Perm)())(a.pos)
        val anyLockPerm = PermGtCmp(lockPerm, NoPerm()())(a.pos, errT=Trafos(errTrafo.eTransformations, List(), Some(lockErrorNode)))
        val checkSomeLockPerm = Assert(anyLockPerm)(a.pos, errT=errTrafo)
        // inhale inv
        val inv = lockSpec.invariant.withArgs(Seq(lockExp, invValVarDecl.localVar))
        val inhaleInv = Inhale(inv)()
        // assume seen current
        val seen = FuncApp(seenFuncNames.get(lt).get, Seq(lockExp, invValVarDecl.localVar))(a.pos, a.info, Bool, NoTrafos)
        val assumeSeen = Inhale(seen)(a.pos)
        // if full lock perm inhale secinv
        val secInv = lockSpec.alpha.lowWithArg(invValVarDecl.localVar)
        val hasFullLockPerm = PermGeCmp(lockPerm, FullPerm()())()
        val inhaleSecInv = Inhale(Implies(hasFullLockPerm, secInv)())()
        // inhale locked
        val lockedAccess = PredicateAccess(Seq(lockExp), lockedPredNames.get(lt).get)()
        val lockedPredAcc = PredicateAccessPredicate(lockedAccess, FullPerm()())()
        val lockedValFuncApp = FuncApp(lockedFuncNames.get(lt).get, Seq(lockExp))(a.pos, a.info, lockSpec.t, NoTrafos)
        val inhaleLocked = Inhale(And(lockedPredAcc, EqCmp(lockedValFuncApp, invValVarDecl.localVar)())())()
        var acquireStmts = Seq(checkSomeLockPerm, inhaleInv, assumeSeen, inhaleSecInv, inhaleLocked)
        if (lockSpec.hist.isDefined){
          val qVarName = "$histVal$" + getFreshInt()
          val qVarDecl = LocalVarDecl(qVarName, lockSpec.t)()
          val seenFuncApp = FuncApp(seenFuncNames.get(lt).get, Seq(lockExp, qVarDecl.localVar))(a.pos, a.info, Bool, NoTrafos)
          val trigger = Trigger(Seq(seenFuncApp))()
          val histAssert = lockSpec.hist.get.withArgs(Seq(qVarDecl.localVar, invValVarDecl.localVar))
          val impl = Implies(seenFuncApp, histAssert)(a.pos)
          val quant = Forall(Seq(qVarDecl), Seq(trigger), impl)(a.pos)
          val assumeHist = Inhale(quant)(a.pos)
          acquireStmts = acquireStmts ++ Seq(assumeHist)
        }
        Seqn(acquireStmts, Seq(invValVarDecl))(errT=NodeTrafo(a))
      }
      case s@Share(lt, lockExp, lockVal) => {
        val lockSpec = lockSpecs.get(lt).get
        val invPerms = lockSpec.invariant.withArgs(Seq(lockExp, lockVal))
        val errTrafo = ErrTrafo({
          case AssertFailed(_, reason, _) => ShareFailed(s, reason)
        })
        val seen = FuncApp(seenFuncNames.get(lt).get, Seq(lockExp, lockVal))(s.pos, s.info, Bool, NoTrafos)
        val assumeSeen = Inhale(seen)(s.pos)
        val assertInv = Assert(invPerms)(s.pos, errT=errTrafo)
        val exhaleInv = Exhale(invPerms)(s.pos)
        val lockedTrafo = NodeTrafo(Locked(lt, lockExp, AnyValue(lockSpec.t)())(s.pos))
        val fp = FullPerm()()
        val lockedPred = PredicateAccessPredicate(PredicateAccess(Seq(lockExp), lockedPredNames.get(lt).get)(), fp)(s.pos, errT=lockedTrafo)
        val lockPredAcc = PredicateAccess(Seq(lockExp), lockPredNames.get(lt).get)()
        val lockTrafo = NodeTrafo(Lock(lt, lockExp, AnyValue(Perm)())(s.pos))
        val hasLockPerm = PermGtCmp(CurrentPerm(lockPredAcc)(), NoPerm()())(s.pos, errT=lockTrafo)
        val assertLockPerm = Assert(hasLockPerm)(s.pos, errT=errTrafo)
        val lockedVal = FuncApp(lockedFuncNames.get(lt).get, Seq(lockExp))(s.pos, s.info, lockSpec.t, NoTrafos)
        val assertLocked = Assert(lockedPred)(s.pos, errT=errTrafo)
        val exhaleLocked = Exhale(lockedPred)(s.pos)

        val bottomApp = FuncApp(bottomFuncNames.get(lt).get, Seq())(s.pos, s.info, lockSpecs.get(lt).get.t, NoTrafos)
        val bottomTrafo = NodeTrafo(Locked(lt, lockExp, BottomVal(lockSpec.t)(s.pos))(s.pos))
        val assertLockedBottom = Assert(EqCmp(lockedVal, bottomApp)(s.pos, errT=bottomTrafo))(s.pos, errT=errTrafo)
        val assertSecInv = Assert(lockSpec.alpha.lowWithArg(lockVal))(s.pos, errT=errTrafo)
        val assertLowEvent = Assert(SIFLowEventExp()(s.pos))(s.pos, errT=errTrafo)
        Seqn(Seq(assertInv, assertLocked, assertLockPerm, assertLockedBottom, assertLowEvent, assertSecInv, assumeSeen, exhaleInv, exhaleLocked), Seq())(s.pos)
      }
      case r@Release(lt, lockExp, opAction) => {
        val lockSpec = lockSpecs.get(lt).get
        val invValDummyName = "$invVal$" + getFreshInt()
        val invValDummyDecl = LocalVarDecl(invValDummyName, lockSpec.t)()
        val invPerms = lockSpec.invariant.permissionsWithArgs(Seq(lockExp, invValDummyDecl.localVar))
        val errTrafo = ErrTrafo({
          case AssertFailed(_, reason, _) => ReleaseFailed(r, reason)
        })
        val assertInvPerms = Assert(invPerms)(r.pos, errT=errTrafo)
        val exhaleInvPerms = Exhale(invPerms)(r.pos)

        // either bottom or unchanged
        val fp = FullPerm()()
        val lockedTrafo = NodeTrafo(Locked(lt, lockExp, AnyValue(lockSpec.t)())(r.pos))
        val lockedPred = PredicateAccessPredicate(PredicateAccess(Seq(lockExp), lockedPredNames.get(lt).get)(), fp)(r.pos, errT=lockedTrafo)
        val lockedVal = FuncApp(lockedFuncNames.get(lt).get, Seq(lockExp))(r.pos, r.info, lockSpec.t, NoTrafos)
        val assertLocked = Assert(lockedPred)(r.pos, errT=errTrafo)
        val exhaleLocked = Exhale(lockedPred)(r.pos)
        // assert perm(lock(lockExp)) > 0
        val lockTrafo = NodeTrafo(Lock(lt, lockExp, AnyValue(Perm)())(r.pos))
        val lockPredAcc = PredicateAccess(Seq(lockExp), lockPredNames.get(lt).get)()
        val hasLockPerm = PermGtCmp(CurrentPerm(lockPredAcc)(), NoPerm()())(r.pos, errT=lockTrafo)
        val assertLockPerm = Assert(hasLockPerm)(r.pos, errT=errTrafo)
        var assertInvPure : Assert = null


        val (actionChecks: Seq[Stmt], actionDecls: Seq[LocalVarDecl]) = opAction match {
          case None => {
            assertInvPure = Assert(lockSpec.invariant.pureWithArgs(Seq(lockExp, lockedVal)))(r.pos, errT=errTrafo)
            (Seq(), Seq())
          }
          case Some((actionName, actionArg)) => {
            val action = lockSpec.actions.find(a => a.name == actionName).get
            // assert LowEvent
            val checkLowEvent = Assert(SIFLowEventExp()())(r.pos, errT=errTrafo)
            // assert perm(guard(action, lockExp)) >= 1
            val guardTrafo = NodeTrafo(Guard(lt, actionName, lockExp)(r.pos))
            val guardPredAcc = PredicateAccess(Seq(lockExp), actionGuardNames.get(lt).get.get(actionName).get)()
            val hasGuardPerm = if (action.duplicable) PermGtCmp(CurrentPerm(guardPredAcc)(), NoPerm()())(r.pos, errT=guardTrafo) else PermGeCmp(CurrentPerm(guardPredAcc)(), fp)(r.pos, errT=guardTrafo)
            val assertGuardPerm = Assert(hasGuardPerm)(r.pos, errT=errTrafo)
            // var oldVal
            val oldValVarName = "$oldVal$" + getFreshInt()
            val oldValVarDecl = LocalVarDecl(oldValVarName, lockSpec.t)()
            val oldVarDef = Inhale(EqCmp(oldValVarDecl.localVar, lockedVal)())(r.pos)
            // exhale       actionPre(oldVal, arg)
            //              current == actionFunc(oldVal, arg) &&
            //              locked(lockExp, oldVal)
            val assertActionPre = Assert(action.pre.replaceT(action.params(0).localVar, oldValVarDecl.localVar).replace(action.params(1).localVar, actionArg))(r.pos, errT=errTrafo)
            val actionNewVal = action.newVal.replaceT(action.params(0).localVar, oldValVarDecl.localVar).replace(action.params(1).localVar, actionArg)
            assertInvPure = Assert(lockSpec.invariant.pureWithArgs(Seq(lockExp, actionNewVal)))(r.pos, errT=errTrafo)
            // assume seen new val
            val seen = FuncApp(seenFuncNames.get(lt).get, Seq(lockExp, actionNewVal))(r.pos, r.info, Bool, NoTrafos)
            val assumeSeen = Inhale(seen)(r.pos)
            val stmtSeq = Seq(checkLowEvent, assertGuardPerm, oldVarDef, assertActionPre, assumeSeen)
            (stmtSeq, Seq(oldValVarDecl))
          }
        }

        Seqn(Seq(assertInvPerms, assertLocked, assertLockPerm) ++ actionChecks ++ Seq(assertInvPure, exhaleInvPerms, exhaleLocked), Seq(invValDummyDecl) ++ actionDecls)(r.pos)
      }
      case f@Fork(m, token, args) => {
        val havocToken = MethodCall(havocNames.get(Ref).get, Seq(), Seq(token))(f.pos, f.info, NoTrafos)
        val errTrafo = ErrTrafo({
          case ExhaleFailed(_, reason, _) => ForkFailed(f, reason)
        })
        val method = input.findMethod(m)
        var pres = method.pres
        for (i <- 0 until args.length){
          pres = pres.map(pre => pre.replace(method.formalArgs(i).localVar, args(i)))
        }
        val exhalePres = pres.map(pre => Exhale(pre)(f.pos, errT=errTrafo))
        var joinablePred : Exp = PredicateAccessPredicate(PredicateAccess(Seq(token), joinableNames.get(m).get)(), FullPerm()())(f.pos)
        for (i <- 0 until args.length) {
          val funcApp = FuncApp(joinableFunctions.get(m).get(i), Seq(token))(f.pos)
          val eq = EqCmp(funcApp, args(i))(f.pos)
          joinablePred = And(joinablePred, eq)(f.pos)
        }
        val inhaleJoinable = Inhale(joinablePred)(f.pos)
        Seqn(exhalePres ++ Seq(havocToken, inhaleJoinable), Seq())(f.pos)
      }
      case j@Join(m, resVars, token) => {
        val method = input.findMethod(m)
        val havocTargets = ListBuffer[MethodCall]()
        var posts = method.posts
        val joinablePred = PredicateAccess(Seq(token), joinableNames.get(m).get)()
        val joinableTrafo = NodeTrafo(Joinable(m, token, method.formalArgs.map(fa => AnyValue(fa.typ)()))(j.pos))
        val errTrafo = ErrTrafo({
          case AssertFailed(_, reason, _) => JoinFailed(j, reason)
        })
        val assertJoinable = Assert(PredicateAccessPredicate(joinablePred, FullPerm()())(j.pos, errT=joinableTrafo))(j.pos, errT=errTrafo)
        for (i <- 0 until resVars.length){
          val havocCall =  MethodCall(havocNames.get(resVars(i).typ).get, Seq(), Seq(resVars(i)))(j.pos, j.info, NoTrafos)
          havocTargets.append(havocCall)
          posts = posts.map(post => post.replaceT(method.formalReturns(i).localVar, resVars(i)))
        }
        for (i <- 0 until method.formalArgs.length){
          val argFuncApp = FuncApp(joinableFunctions.get(m).get(i), Seq(token))()
          posts = posts.map(post => post.replace(method.formalArgs(i).localVar, argFuncApp))
        }
        val exhaleJoinable = Exhale(PredicateAccessPredicate(joinablePred, FullPerm()())())()
        val inhalePosts = posts.map(post => Inhale(post)())
        Seqn(Seq(assertJoinable) ++ havocTargets ++ inhalePosts ++ Seq(exhaleJoinable), Seq())(j.pos)
      }
      //case Threadtype() => Ref
      //case Locktype() => Ref
    }, Traverse.TopDown)


    val productRes = SIFExtendedTransformer.transform(res, false)
    //println(productRes)
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
    println(qpTransformed)
    qpTransformed
  }

  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    input match {
      case Failure(errors) => Failure(errors.map(e => if (e.isInstanceOf[AbstractVerificationError]) e.asInstanceOf[AbstractVerificationError].transformedError() else e))
      case Success => input
    }
  }
}
