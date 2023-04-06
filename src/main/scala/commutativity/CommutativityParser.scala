package commutativity

import viper.silver.parser.FastParser.{PWrapper, actualArgList, exp, idndef, idnuse, keyword, parens, block, typ, stmts, fieldAcc, term}
import viper.silver.parser.{PExp, PFormalArgDecl, PFullPerm, PLet, PLetNestedScope, PPrimitiv, PSeqn, PType, PUnknown}
import viper.silver.plugin.ParserPluginTemplate

import scala.collection.Set

/*
 * Extends the standard Viper parser to also parse lock specifications as  well as statements and expressions/assertions
 * related to threads, locks, and information flow.
 */
trait CommutativityParser extends ParserPluginTemplate {

  override val White = PWrapper {
    import fastparse.all._
    NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }

  import White._
  import fastparse.noApi._

  override lazy val newDeclAtEnd = P(lockSpec)
  override lazy val newExpAtStart = P(pointsToPred | joinable | low | lowEvent | uguard | sguard | uguardargs | sguardargs | allpre)
  override lazy val newStmtAtStart = P(fork | join | withcmd | share | unshare | merge | split)


  lazy val ctyp: P[PType] = P(keyword("int").map(_ => PPrimitiv("Int")) | keyword("bool").map(
    _ => PPrimitiv("Bool")) | idnuse.map(_ => PPrimitiv("Ref"))
  )

  lazy val fork: P[PFork] = P(idnuse ~ ":=" ~ "fork" ~/ idnuse ~ parens(actualArgList)).map {
    case (t, m, args) => PFork(m, t, args)
  }

  lazy val join: P[PJoin] = P((idnuse.rep(sep = ",") ~ ":=").? ~ "join" ~/ "[" ~ idnuse ~ "]" ~ parens(exp)).map {
    case (targets, m, token) => PJoin(m, if (targets.isDefined) targets.get else Seq(), token)
  }

  lazy val withcmd: P[PWith] = P("with" ~/ "[" ~ idnuse ~ "]" ~ exp ~ ("when" ~ exp).? ~
    "performing" ~ idnuse ~ parens(exp) ~ ("at" ~ exp).? ~ block).map {
    case (lockType, lockExp, whenExp, actionName, actionArg, lbl, stmt) =>
      PWith(lockType, lockExp, whenExp, actionName, actionArg, lbl, stmt)
  }

  lazy val unshare: P[PUnshare] = P("unshare" ~/ "[" ~ idnuse ~ "]" ~ parens(exp)).map {
    case (lockType, arg) => PUnshare(lockType, arg)
  }

  lazy val share: P[PShare] = P("share" ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp)).map {
    case (lockType, (arg, value)) => PShare(lockType, arg, value)
  }

  lazy val merge: P[PMerge] = P("merge" ~/ "[" ~ idnuse ~ "," ~ idnuse ~ "]" ~
    parens(exp ~ "," ~ exp ~ "," ~ exp)).map {
    case (lockType, action, (lockExp, lbls1, lbls2)) => PMerge(lockType, action, lockExp, lbls1, lbls2)
  }

  lazy val split: P[PSplit] = P("split" ~/ "[" ~ idnuse ~ "," ~ idnuse ~ "]" ~
    parens(exp ~ "," ~ exp ~ "," ~ exp ~ "," ~ exp ~ "," ~ exp)).map {
    case (lockType, action, (lockExp, lbls1, lbls2, args1, args2)) =>
      PSplit(lockType, action, lockExp, lbls1, lbls2, args1, args2)
  }

  lazy val lockSpec: P[PLockSpec] = P("lockType" ~/ idndef ~ "{" ~ "type" ~ typ ~
    invariantDecl("invariant", 2) ~ alphaDecl ~
    (invariantDecl("histInvariant", 2)).? ~ // currently unused
    actionDeclList ~ actionDef.rep ~ proof.rep ~ "noLabels" ~ "=" ~ exp ~ "}").map {
    case (name, t, i, al, hist, alist, actions, proofs, nlabels) => PLockSpec(name, t, i, al, hist, alist, actions, proofs, nlabels)
  }

  def invariantDecl(name: String, nParams: Int): P[PInvariantDef] =
    P(name ~/ parens(idndef.rep(sep = ",", exactly = nParams)) ~ "=" ~ exp).map {
    case (params, e) => PInvariantDef(params, e)
  }

  lazy val alphaDecl: P[PAlphaDef] = P("alpha" ~/ parens(idndef) ~ ":" ~ typ ~ "=" ~ exp).map {
    case (param, t, e) => PAlphaDef(param, t, e)
  }

  lazy val actionDeclList = P("actions" ~/ "=" ~ "[" ~ actionDecl.rep(sep = ",") ~ "]")

  lazy val actionDecl: P[PLockActionDecl] = P("(" ~ idndef ~ "," ~ typ ~ "," ~ (dupl | nondupl) ~ ")").map {
    case (id, t1, d) => PLockActionDecl(id, t1, d.equals("duplicable"))
  }

  lazy val dupl: P[String] = P(keyword("duplicable")).!

  lazy val nondupl: P[String] = P(keyword("unique")).!

  lazy val actionDef: P[PLockActionDef] = P("action" ~/ idnuse ~ parens(idndef.rep(exactly = 2, sep = ",")) ~
    keyword("requires") ~ exp ~
    "{" ~ exp ~ "}").map {
    case (name, params, pre, newVal) => PLockActionDef(name, params, newVal, pre)
  }

  lazy val proof: P[PProof] = P("proof" ~/ proofType ~ "[" ~ idnuse.rep(sep = ",") ~ "]" ~ parens(idndef.rep(sep = ",")) ~ "{" ~ stmts ~ "}").map {
    case (ptype, actions, params, pstmt) => PProof(ptype, actions, params, PSeqn(pstmt))
  }

  lazy val proofType: P[String] = P("commutativity".! | "preservation".!)

  lazy val pointsToPred: P[PExp] = P(pointsToPred1 | pointsToPred2)

  lazy val pointsToPred1: P[PSimplePointsToPredicate] = P("[" ~ fieldAcc ~ ("|->" | ("|-[" ~ term ~ "]->")) ~ (anyVal | exp) ~ "]").map {
    case (fa, p, rhs) => {
      val perm = if (p.isInstanceOf[PExp]) p.asInstanceOf[PExp] else PFullPerm()
      PSimplePointsToPredicate(fa, perm, rhs)
    }
  }

  lazy val pointsToPred2: P[PVarDefiningPointsToPredicate] = P("[" ~ fieldAcc ~ ("|->" | ("|-[" ~ term ~ "]->")) ~ "?" ~ idndef ~ "&&" ~ exp ~ "]").map {
    case (fa, p, id, body) => {
      val perm = if (p.isInstanceOf[PExp]) p.asInstanceOf[PExp] else PFullPerm()
      PVarDefiningPointsToPredicate(fa, perm, PLet(fa, PLetNestedScope(PFormalArgDecl(id, PUnknown()), body)))
    }
  }

  lazy val anyVal: P[PExp] = P("_").map { case _ => PAnyVal() }

  lazy val joinable: P[PJoinable] = P(keyword("joinable") ~/ "[" ~ idnuse ~ "]" ~ parens(exp.rep(min = 1, sep = ","))).map {
    case (method, args) => PJoinable(method, args(0), args.tail)
  }

  lazy val low: P[PLow] = P(keyword("low") ~/ parens(exp)).map {
    case arg => PLow(arg)
  }

  lazy val lowEvent: P[PLowEvent] = P(keyword("lowEvent")).map {
    case _ => PLowEvent()
  }

  lazy val seen: P[PSeen] = P(keyword("seen") ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp)).map {
    case (ltype, (argLock, argVal)) => PSeen(ltype, argLock, argVal)
  }

  lazy val lock: P[PLock] = P(keyword("lock") ~/ "[" ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp)).map {
    case (ltype, (argLock, argVal)) => PLock(ltype, argLock, argVal)
  }

  lazy val allpre: P[PAllPre] = P(keyword("allPre") ~/ "[" ~ idnuse ~ "," ~ idnuse ~ "]" ~ parens(exp)).map {
    case (ltype, action, args) => PAllPre(ltype, action, args)
  }

  lazy val uguard: P[PUGuard] = P(keyword("uguard") ~/ "[" ~ idnuse ~ "," ~ idnuse ~ "]" ~ parens(exp)).map {
    case (ltype, action, lockExp) => PUGuard(ltype, action, lockExp)
  }

  lazy val sguard: P[PSGuard] = P(keyword("sguard") ~/ "[" ~ idnuse ~ "," ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp)).map {
    case (ltype, action, (lockExp, lbls)) => PSGuard(ltype, action, lockExp, lbls)
  }

  lazy val uguardargs: P[PUGuardArgs] = P(keyword("uguardArgs") ~/ "[" ~ idnuse ~ "," ~ idnuse ~ "]" ~ parens(exp)).map {
    case (ltype, action, lockExp) => PUGuardArgs(ltype, action, lockExp)
  }

  lazy val sguardargs: P[PSGuardArgs] = P(keyword("sguardArgs") ~/ "[" ~ idnuse ~ "," ~ idnuse ~ "]" ~ parens(exp ~ "," ~ exp)).map {
    case (ltype, action, (lockExp, lbls)) => PSGuardArgs(ltype, action, lockExp, lbls)
  }

  override lazy val extendedKeywords = Set("lockType", "action", "invariant", "alpha", "proof", "reordering",
    "commutativity", "preservation", "locked", "lock", "guard", "joinable", "duplicable", "unique")
}
