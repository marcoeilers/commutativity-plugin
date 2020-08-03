package commutativity

import viper.silver.ast._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.verifier.{ConsistencyError, VerificationResult}
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, parens, show, ssep, text}
import viper.silver.sif.SIFLowExp


case class AlphaDef(param: LocalVarDecl, typ: Type, exp: Exp)  {
  def subnodes = Seq(param, typ, exp)

  def withArg(arg: Exp) : Exp = InvariantDef.arbitraryExpWithArgs(exp, Seq(param), Seq(arg))

  def lowWithArg(arg: Exp) : Exp = SIFLowExp(InvariantDef.arbitraryExpWithArgs(exp, Seq(param), Seq(arg)))()
}

object InvariantDef {
  def arbitraryExpWithArgs(e: Exp, params: Seq[LocalVarDecl], args: Seq[Exp]) : Exp = {
    import Extensions._
    var res = e
    if (args.length != params.length){
      throw new IllegalArgumentException
    }
    for (i <- 0 until args.length){
      res = if (args(i).isInstanceOf[LocalVar]) res.replaceT(params(i).localVar, args(i).asInstanceOf[LocalVar]) else res.replace(params(i).localVar, args(i))
    }
    res
  }
}
case class InvariantDef(params: Seq[LocalVarDecl], inv: Exp){
  def subnodes = Seq(inv) ++ params

  def expWithArgs(e: Exp, args: Seq[Exp]) : Exp = InvariantDef.arbitraryExpWithArgs(e, params, args)

  def permissionsWithArgs(args: Seq[Exp]) : Exp = expWithArgs(permissions, args)
  def pureWithArgs(args: Seq[Exp]) : Exp = expWithArgs(noPerms, args)
  def withArgs(args: Seq[Exp]) : Exp = expWithArgs(inv, args)

  private def permsOnly(e: Exp): Exp = {
    e match {
      case And(e1, e2) => And(permsOnly(e1), permsOnly(e2))()
      case Implies(e1, e2) => Implies(e1, permsOnly(e2))()
      case _: FieldAccessPredicate => e
      case _: PredicateAccessPredicate => e
      case PointsToPredicate(rec, perm, _) => PointsToPredicate(rec, perm, None)()
      case VarDefiningPointsToPredicate(rec, perm, decl, None) => e
      case VarDefiningPointsToPredicate(rec, perm, decl, Some(b)) => VarDefiningPointsToPredicate(rec, perm, decl, Some(permsOnly(b)))()
      case CondExp(e1, e2, e3) => CondExp(e1, permsOnly(e2), permsOnly(e3))()
      case Forall(vars, triggers, body) => Forall(vars, triggers, permsOnly(body))()
      case Let(v, e, body) => Let(v, e, permsOnly(body))()
      case _ => TrueLit()()
    }
  }

  private def withoutPerms(exp: Exp) : Exp = {
    val res = exp.transform({
      case _: FieldAccessPredicate => TrueLit()()
      case _: PredicateAccessPredicate => TrueLit()()
      case PointsToPredicate(rec, perm, None) => TrueLit()()
      case PointsToPredicate(rec, perm, Some(e)) => EqCmp(rec, e)()
      case VarDefiningPointsToPredicate(rec, perm, decl, None) => TrueLit()()
      case VarDefiningPointsToPredicate(rec, perm, decl, Some(body)) => body.replace(decl.localVar, rec)
    })
    res
  }

  lazy val permissions : Exp = permsOnly(inv)
  lazy val noPerms : Exp = withoutPerms(inv)

}
case class LockAction(name: String, argType: Type, duplicable: Boolean, params: Seq[LocalVarDecl], newVal: Exp, pre: Exp)(val pos: Position) {
  def subnodes = Seq(argType, newVal, pre) ++ params
}
case class Proof(proofType: String, actions: Seq[String], params: Seq[LocalVarDecl], body: Seqn) {
  def subnodes = Seq(body) ++ params
}

case class LockSpec(name: String, t: Type, invariant: InvariantDef, alpha: AlphaDef, hist: Option[InvariantDef], actions: Seq[LockAction], proofs: Seq[Proof])(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionMember  {
  override def extensionSubnodes: Seq[Node] = Seq(t) ++ invariant.subnodes ++ alpha.subnodes ++ (if (hist.isDefined) hist.get.subnodes else Seq()) ++ (actions map (_.subnodes)).flatten ++ (proofs map (_.subnodes)).flatten
  override lazy val checkTransitively: Seq[ConsistencyError] = Seq()
  val scopedDecls : Seq[Declaration] = Seq()

}

case class BarrierSpec(name: String, in: InvariantDef, totalIn: InvariantDef, totalOut: InvariantDef, out: InvariantDef)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionMember  {
  override def extensionSubnodes: Seq[Node] = in.subnodes ++ out.subnodes ++ totalIn.subnodes ++ totalOut.subnodes
  override lazy val checkTransitively: Seq[ConsistencyError] = Seq()
  val scopedDecls : Seq[Declaration] = Seq()
}

case class PointsToPredicate(receiver: FieldAccess, perm: Exp, arg: Option[Exp])(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(receiver, perm) ++ (if (arg.isDefined) Seq(arg.get) else Seq())
  def prettyPrint : PrettyPrintPrimitives#Cont =  text("[") <> show(receiver) <+> (if (perm.isInstanceOf[FullPerm]) text("|->") else (text("|-[") <> show(perm) <> text("]->"))) <+> (if (arg.isDefined) show(arg.get) else text("_")) <> text("]")
  override def verifyExtExp(): VerificationResult = ???
}

case class VarDefiningPointsToPredicate(receiver: FieldAccess, perm: Exp, varDecl: LocalVarDecl, conjunct: Option[Exp])(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(receiver, perm, varDecl) ++ (if (conjunct.isDefined) Seq(conjunct.get) else Seq())
  def prettyPrint : PrettyPrintPrimitives#Cont = text("[") <> show(receiver) <+> (if (perm.isInstanceOf[FullPerm]) text("|->") else (text("|-[") <> show(perm) <> text("]->"))) <+> text("?") <> show(varDecl.localVar) <+> (if (conjunct.isDefined) text("&&") <+> show(conjunct.get) else text("")) <> text("]")
  override def verifyExtExp(): VerificationResult = ???
}

case class Joinable(method: String, e: Exp, args: Seq[Exp])(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(e) ++ args
  def prettyPrint : PrettyPrintPrimitives#Cont = text("joinable[" + method + "]") <> parens(ssep((Seq(e) ++ args) map show, text(", ")))
  override def verifyExtExp(): VerificationResult = ???
}

case class Lock(lockType: String, lockRef: Exp, amount: Exp)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(lockRef, amount)
  def prettyPrint : PrettyPrintPrimitives#Cont = text("lock[" + lockType + "]") <> parens(ssep((Seq(lockRef, amount) ) map show, text(", ")))
  override def verifyExtExp(): VerificationResult = ???
}

case class Barrier(barrierType: String, barrierRef: Exp, index: Exp, total: Exp)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(barrierRef, index, total)
  def prettyPrint : PrettyPrintPrimitives#Cont = text("barrier[" + barrierType + "]") <> parens(ssep((Seq(barrierRef, index, total) ) map show, text(", ")))
  override def verifyExtExp(): VerificationResult = ???
}

case class AnyValue(typ: Type)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val extensionIsPure: Boolean = true
  val extensionSubnodes : Seq[Node] = Seq(typ)
  def prettyPrint : PrettyPrintPrimitives#Cont = text("_")
  override def verifyExtExp(): VerificationResult = ???
}

case class BottomVal(typ: Type)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val extensionIsPure: Boolean = true
  val extensionSubnodes : Seq[Node] = Seq(typ)
  def prettyPrint : PrettyPrintPrimitives#Cont = text("bottom")
  override def verifyExtExp(): VerificationResult = ???
}

case class Locked(lockType: String, lockRef: Exp, value: Exp)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(lockRef, value)
  def prettyPrint : PrettyPrintPrimitives#Cont = text("locked[" + lockType + "]") <> parens(ssep((Seq(lockRef, value) ) map show, text(", ")))
  override def verifyExtExp(): VerificationResult = ???
}

case class Seen(lockType: String, lockRef: Exp, value: Exp)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = true
  val extensionSubnodes : Seq[Node] = Seq(lockRef, value)
  def prettyPrint : PrettyPrintPrimitives#Cont = text("seen[" + lockType + "]") <> parens(ssep((Seq(lockRef, value) ) map show, text(", ")))
  override def verifyExtExp(): VerificationResult = ???
}

case class Guard(lockType: String, guardName: String, lock: Exp)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionExp {
  val typ : Type = Bool
  val extensionIsPure: Boolean = false
  val extensionSubnodes : Seq[Node] = Seq(lock)
  def prettyPrint : PrettyPrintPrimitives#Cont = text("guard[" + lockType + "," + guardName +  "]") <> parens(show(lock))
  override def verifyExtExp(): VerificationResult = ???
}


// Statements
case class NewLock(lockType: String, target: LocalVar, fields: Seq[Field])(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionStmt {
  val extensionSubnodes : Seq[Node] = Seq(target) ++ fields
  def prettyPrint : PrettyPrintPrimitives#Cont = show(target) <+> text(":=") <+> text("newLock[" + lockType + "]") <> parens(ssep((fields.map(_.name)) map text, text(", ")))
}

case class NewBarrier(barrierType: String, target: LocalVar, n: Exp, fields: Seq[Field])(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionStmt {
  val extensionSubnodes : Seq[Node] = Seq(target, n) ++ fields
  def prettyPrint : PrettyPrintPrimitives#Cont = show(target) <+> text(":=") <+> text("newBarrier[" + barrierType + "]") <> parens(show(n)) <> parens(ssep((fields.map(_.name)) map text, text(", ")))
}

case class Fork(m: String, tokenVar: LocalVar, args: Seq[Exp])(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionStmt {
  val extensionSubnodes : Seq[Node] = Seq(tokenVar) ++ args
  def prettyPrint : PrettyPrintPrimitives#Cont = show(tokenVar) <+> text(":=") <+> text("fork") <+> text(m) <> parens(ssep(args map show, text(", ")))
}

case class Join(m: String, resVars: Seq[LocalVar], tokenArg: Exp)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionStmt {
  val extensionSubnodes : Seq[Node] = Seq(tokenArg) ++ resVars
  def prettyPrint : PrettyPrintPrimitives#Cont = ssep(resVars map show, text(", ")) <+> text(":=") <+> text("join") <+> show(tokenArg)
}

case class Release(lockType: String, lockExp: Exp, action: Option[(String, Exp)])(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionStmt {
  val extensionSubnodes : Seq[Node] = Seq(lockExp) ++ (if (action.isDefined) Seq(action.get._2) else Seq())
  def prettyPrint : PrettyPrintPrimitives#Cont = text("release[" + lockType + "]") <> (if (action.isDefined) parens(show(lockExp) <> text(", ") <> text(action.get._1) <> parens(show(action.get._2))) else parens(show(lockExp)))
}

case class Share(lockType: String, lockExp: Exp, lockVal: Exp)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionStmt {
  val extensionSubnodes : Seq[Node] = Seq(lockExp, lockVal)
  def prettyPrint : PrettyPrintPrimitives#Cont = text("share[" + lockType + "]") <>  parens(show(lockExp) <> text(", ") <> show(lockVal))
}

case class Wait(barrierType: String, barrierExp: Exp, index: Exp, total: Exp)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionStmt {
  val extensionSubnodes : Seq[Node] = Seq(barrierExp, index)
  def prettyPrint : PrettyPrintPrimitives#Cont = text("wait[" + barrierType + "]") <>  parens(show(barrierExp) <> text(", ") <> show(index) <> text(", ") <> show(total))
}

case class Acquire(lockType: String, lockExp: Exp)(val pos: Position=NoPosition, val info: Info=NoInfo, val errT: ErrorTrafo=NoTrafos) extends ExtensionStmt {
  val extensionSubnodes : Seq[Node] = Seq(lockExp)
  def prettyPrint : PrettyPrintPrimitives#Cont = text("acquire[" + lockType + "]") <> parens(show(lockExp))
}

case class Locktype() extends ExtensionType {
  override def isConcrete: Boolean = true

  override def substitute(typVarsMap: Map[TypeVar, Type]): Type = this

  override def toString() = "Lock"
}

case class Threadtype() extends ExtensionType {
  override def isConcrete: Boolean = true

  override def substitute(typVarsMap: Map[TypeVar, Type]): Type = this

  override def toString(): String = "Thread"
}