package commutativity

import viper.silver.ast._
import viper.silver.parser._
import viper.silver.sif.{SIFLowEventExp, SIFLowExp}

import scala.collection.mutable.ListBuffer


case class PSimplePointsToPredicate(receiver: PFieldAccess, perm: PExp, arg: PExp) extends PExtender with PExp {

  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def transform(go: PNode => PNode): PExtender = {
    PSimplePointsToPredicate(go(receiver).asInstanceOf[PFieldAccess], go(perm).asInstanceOf[PExp], go(arg).asInstanceOf[PExp])
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser):Option[Seq[String]] = {
    t.checkTopTyped(receiver, None)
    t.checkTopTyped(perm, Some(PPrimitiv("Perm")))
    arg match {
      case _:PAnyVal => None
      case _ => {
       t.checkTopTyped(arg.asInstanceOf[PExp], Some(receiver.typ))
      }
    }
    this.typ = PPrimitiv("Bool")
    None
  }
  override def namecheck(n: NameAnalyser) = ???
  override def translateExp(t: Translator): Exp = {
    var translatedReceiver = t.exp(receiver).asInstanceOf[FieldAccess]
    val tPerm = t.exp(perm)
    arg match {
      case PAnyVal() => PointsToPredicate(translatedReceiver, tPerm, None)(t.liftPos(this))
      case e => PointsToPredicate(translatedReceiver, tPerm, Some(t.exp(e.asInstanceOf[PExp])))(t.liftPos(this))
    }
  }

  override def subnodes: Seq[PNode] = getsubnodes()
  override def getsubnodes(): Seq[PNode] = Seq(receiver, perm, arg)
}

case class PVarDefiningPointsToPredicate(receiver: PFieldAccess, perm: PExp, var arg: PLet) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions


  override def transform(go: PNode => PNode): PExtender = {
    PVarDefiningPointsToPredicate(go(receiver).asInstanceOf[PFieldAccess], go(perm).asInstanceOf[PExp], go(arg).asInstanceOf[PLet])
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser):Option[Seq[String]] = {
    t.checkTopTyped(receiver, None)
    t.checkTopTyped(perm, Some(PPrimitiv("Perm")))
    t.checkTopTyped(arg, Some(PPrimitiv("Bool")))
    this.typ = PPrimitiv("Bool")
    None
  }
  override def namecheck(n: NameAnalyser) = ???
  override def translateExp(t: Translator): Exp = {
    var translatedReceiver = t.exp(receiver).asInstanceOf[FieldAccess]
    val tPerm = t.exp(perm)
    val tLet = t.exp((arg)).asInstanceOf[Let]
    VarDefiningPointsToPredicate(translatedReceiver, tPerm, tLet.variable, Some(tLet.body))(t.liftPos(this))
  }

  override def subnodes: Seq[PNode] = getsubnodes()
  override def getsubnodes(): Seq[PNode] = Seq(receiver, perm, arg)
}

case class PAnyVal() extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typeSubstitutions: Seq[PTypeSubstitution] = ???

  override def getsubnodes(): Seq[PNode] = Seq()

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = None

  override def transform(go: PNode => PNode): PExtender = this
}

case class PAlphaDef(arg: PIdnDef, typ: PType, exp: PExp) {
  def subnodes: Seq[PNode] = Seq(arg, typ, exp)

  def typecheckAlpha(t: TypeChecker, na: NameAnalyser, locktype: String, valueType: PType) = {
    val params = Seq(PFormalArgDecl(PIdnDef(arg.name), valueType))
    val fakeFunc = PFunction(PIdnDef(locktype + "$alpha"), params, typ, Seq(), Seq(), Some(exp))
    na.namesInScope(fakeFunc, None)
    t.checkDeclaration(fakeFunc)
    t.checkBody(fakeFunc)
  }

  def translateAlpha(t: Translator, parTyp: Type) : AlphaDef = {
    AlphaDef(LocalVarDecl(arg.name, parTyp)(t.liftPos(arg)), t.ttyp(typ), t.exp(exp))
  }

  def transform(go: PNode => PNode): PAlphaDef = {
    PAlphaDef(go(arg).asInstanceOf[PIdnDef], go(typ).asInstanceOf[PType], go(exp).asInstanceOf[PExp])
  }
}

case class PInvariantDef(args: Seq[PIdnDef], inv: PExp) {
  def subnodes: Seq[PNode] = args ++ Seq(inv)

  def typecheckBarrierAssertion(t: TypeChecker, na: NameAnalyser, locktype: String, checkType: String) : Unit = {
    val bool = PPrimitiv("Bool")
    val ref = PPrimitiv("Ref")
    val int = PPrimitiv("Int")
    val params = Seq(PFormalArgDecl(PIdnDef(args(0).name), ref), PFormalArgDecl(PIdnDef(args(1).name), int), PFormalArgDecl(PIdnDef(args(2).name), int))
    val fakeFunc = PFunction(PIdnDef(locktype + "$barrier$" + checkType), params, bool, Seq(), Seq(), Some(inv))
    na.namesInScope(fakeFunc, None)
    t.checkDeclaration(fakeFunc)
    t.checkBody(fakeFunc)
  }

  def typecheckInvariant(t: TypeChecker, na: NameAnalyser, typ: PType, locktype: String) : Unit = {
    val bool = PPrimitiv("Bool")
    val ref = PPrimitiv("Ref")
    val params = Seq(PFormalArgDecl(PIdnDef(args(0).name), ref), PFormalArgDecl(PIdnDef(args(1).name), typ))
    val fakeFunc = PFunction(PIdnDef(locktype + "$inv"), params, bool, Seq(), Seq(), Some(inv))
    na.namesInScope(fakeFunc, None)
    t.checkDeclaration(fakeFunc)
    t.checkBody(fakeFunc)
  }

  def typecheckHist(t: TypeChecker, na: NameAnalyser, typ: PType, locktype: String) : Unit = {
    val bool = PPrimitiv("Bool")
    val ref = PPrimitiv("Ref")
    val params = Seq(PFormalArgDecl(PIdnDef(args(0).name), typ), PFormalArgDecl(PIdnDef(args(1).name), typ))
    val fakeFunc = PFunction(PIdnDef(locktype + "$hist"), params, bool, Seq(), Seq(), Some(inv))
    na.namesInScope(fakeFunc, None)
    t.checkDeclaration(fakeFunc)
    t.checkBody(fakeFunc)
  }

  def translateBarrierAss(t: Translator) : InvariantDef = {
    InvariantDef(Seq(LocalVarDecl(args(0).name, Ref)(t.liftPos(args(0))), LocalVarDecl(args(1).name, viper.silver.ast.Int)(t.liftPos(args(1))), LocalVarDecl(args(2).name, viper.silver.ast.Int)(t.liftPos(args(2)))), t.exp(inv))
  }

  def translateInvariant(t: Translator, typ: Type) : InvariantDef = {
    InvariantDef(Seq(LocalVarDecl(args(0).name, Ref)(t.liftPos(args(0))), LocalVarDecl(args(1).name, typ)(t.liftPos(args(1)))), t.exp(inv))
  }

  def translateHist(t: Translator, typ: Type) : InvariantDef = {
    InvariantDef(Seq(LocalVarDecl(args(0).name, typ)(t.liftPos(args(0))), LocalVarDecl(args(1).name, typ)(t.liftPos(args(1)))), t.exp(inv))
  }

  def transform(go: PNode => PNode): PInvariantDef = {
    PInvariantDef(args map (go(_).asInstanceOf[PIdnDef]), go(inv).asInstanceOf[PExp])
  }
}
case class PLockActionDecl(val idndef: PIdnDef, argType: PType, duplicable: Boolean) extends PExtender with PMember{
  override def getsubnodes: Seq[PNode] = Seq(idndef, argType)

  override def transform(go: PNode => PNode): PExtender = {
    PLockActionDecl(go(idndef).asInstanceOf[PIdnDef], go(argType).asInstanceOf[PType], duplicable)
  }
}
case class PLockActionDef(name: PIdnUse, args: Seq[PIdnDef], newVal: PExp, pre: PExp) extends FastPositioned {
  def subnodes: Seq[PNode] = args ++ Seq(name, newVal, pre)

  def transform(go: PNode => PNode): PLockActionDef = {
    PLockActionDef(go(name).asInstanceOf[PIdnUse], args map (go(_).asInstanceOf[PIdnDef]), go(newVal).asInstanceOf[PExp], go(pre).asInstanceOf[PExp])
  }
}
case class PProof(proofType: String, actions: Seq[PIdnUse], params: Seq[PIdnDef], body: PSeqn) {
  def subnodes: Seq[PNode] = actions ++ params ++ Seq(body)
  def translate(t: Translator, actionDecls: Seq[LockAction], typ: Type) : Proof = {
    val types : Seq[Type] = proofType match {
      case "preservation" => {
        val action = actionDecls.find(ad => ad.name == actions(0).name).get
        Seq(typ, action.argType)
      }
      case "commutativity" => {
        val a1 = actionDecls.find(ad => ad.name == actions(0).name).get
        val a2 = actionDecls.find(ad => ad.name == actions(1).name).get
        Seq(typ, a1.argType, a2.argType)
      }
    }
    Proof(proofType, actions map (_.name), (0 until params.length) map (i => LocalVarDecl(params(i).name, types(i))(t.liftPos(params(i)))), t.stmt(body).asInstanceOf[Seqn])
  }

  def typecheck(tc: TypeChecker, ns: NameAnalyser, actionDecls: Seq[PLockActionDecl], t: PType, locktype: String) : Seq[String] = {
    proofType match {
      case "preservation" => {
        if (actions.length != 1){
          return Seq("Wrong number of actions for preservation proof.")
        }else if (params.length != 2){
          return Seq("Wrong number of parameters for preservation proof.")
        }
        val actionDecl = actionDecls.find(ad => ad.idndef.name == actions(0).name)
        if (actionDecl.isEmpty){
          return Seq("Unknown action: " + actions(0).name)
        }
        val fakeParams = Seq(PFormalArgDecl(PIdnDef(params(0).name), t), PFormalArgDecl(PIdnDef(params(1).name), actionDecl.get.argType))
        val fakeMethod = PMethod(PIdnDef(locktype + "$" + actionDecl.get.idndef.name + "$proof$pres$"), fakeParams, Seq(), Seq(), Seq(), Some(body))
        ns.namesInScope(fakeMethod, None)
        tc.checkDeclaration(fakeMethod)
        tc.checkBody(fakeMethod)
        Seq()
      }
      case "commutativity" => {
        if (actions.length != 2){
          return Seq("Wrong number of actions for commutativity proof.")
        }else if (params.length != 3){
          return Seq("Wrong number of parameters for commutativity proof.")
        }
        val a1 = actionDecls.find(ad => ad.idndef.name == actions(0).name)
        if (a1.isEmpty){
          return Seq("Unknown action: " + actions(0).name)
        }
        val a2 = actionDecls.find(ad => ad.idndef.name == actions(1).name)
        if (a2.isEmpty){
          return Seq("Unknown action: " + actions(1).name)
        }
        if (actionDecls.indexOf(a1.get) > actionDecls.indexOf(a2.get)){
          return Seq("Incorrect action order in commutativity proof: " + actions(0).name + ", " + actions(1).name)
        }
        val fakeParams = Seq(PFormalArgDecl(PIdnDef(params(0).name), t), PFormalArgDecl(PIdnDef(params(1).name), a1.get.argType), PFormalArgDecl(PIdnDef(params(2).name), a2.get.argType))
        val fakeMethod = PMethod(PIdnDef(locktype + "$" + "$proof$comm$" + a1.get.idndef.name + "$" + a2.get.idndef.name), fakeParams, Seq(), Seq(), Seq(), Some(body))
        ns.namesInScope(fakeMethod, None)
        tc.checkDeclaration(fakeMethod)
        tc.checkBody(fakeMethod)
        Seq()
      }
    }
  }

  def transform(go: PNode => PNode): PProof = {
    PProof(proofType, actions map (go(_).asInstanceOf[PIdnUse]), params map (go(_).asInstanceOf[PIdnDef]), go(body).asInstanceOf[PSeqn])
  }
}

case class PLockSpec(idndef: PIdnDef, t: PType, invariant: PInvariantDef, alpha: PAlphaDef, hist: Option[PInvariantDef], actionList: Seq[PLockActionDecl], actions: Seq[PLockActionDef], proofs: Seq[PProof], nlabels: PExp) extends PExtender with PMember {
  override def getsubnodes: Seq[PNode] = Seq(idndef, nlabels) ++ invariant.subnodes ++ alpha.subnodes ++ (if (hist.isDefined) hist.get.subnodes else Seq()) ++ (actionList map (_.subnodes)).flatten ++ (actions map (_.subnodes)).flatten ++ (proofs map (_.subnodes)).flatten

  override def typecheck(tc: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    val allErrors = ListBuffer[String]()
    tc.checkTopTyped(nlabels, Some(PPrimitiv("Int")))
    if (actionList.length != actions.length || actionList.exists(decl => !actions.exists(d => d.name.name == decl.idndef.name))){
      allErrors.append(idndef.name + ": Action declarations and action definitions do not match.")
    }else{
      actionList.foreach(decl => typecheckAction(tc, n, decl, actions.find(d => d.name.name == decl.idndef.name).get))
    }
    invariant.typecheckInvariant(tc, n, t, idndef.name)
    alpha.typecheckAlpha(tc, n, idndef.name, t)
    if (hist.isDefined) {
      hist.get.typecheckHist(tc, n, t, idndef.name)
    }
    for (proof <- proofs) {
      allErrors ++= proof.typecheck(tc, n, actionList, t, idndef.name)
    }
    if (allErrors.isEmpty)
      None
    else
      Some(allErrors)
  }

  def typecheckAction(tc: TypeChecker, na: NameAnalyser, decl: PLockActionDecl, d: PLockActionDef) = {
    val bool = PPrimitiv("Bool")
    val ref = PPrimitiv("Ref")
    val params = Seq(PFormalArgDecl(PIdnDef(d.args(0).name), t), PFormalArgDecl(PIdnDef(d.args(1).name), decl.argType))
    val newValFunc = PFunction(PIdnDef(idndef.name + "$newVal$" + decl.idndef.name), params, t, Seq(d.pre), Seq(), Some(d.newVal))
    na.namesInScope(newValFunc, None)
    tc.checkDeclaration(newValFunc)
    tc.checkBody(newValFunc)
  }

  override def translateMemberSignature(t: Translator): Member = LockSpec(idndef.name, null, null, null, null, Seq(), Seq(), null)()

  override def translateMember(t: Translator): Member = {
    val typ = t.ttyp(this.t)
    val inv = invariant.translateInvariant(t, typ)
    val alpha = this.alpha.translateAlpha(t, typ)
    val tActions = actionList.map(decl => translateAction(t, decl, actions.find(d => d.name.name == decl.idndef.name).get, typ))
    val tProofs = proofs.map(_.translate(t, tActions, typ))
    val tHist = if (hist.isDefined) Some(hist.get.translateHist(t, typ)) else None
    LockSpec(idndef.name, typ, inv, alpha, tHist, tActions, tProofs, t.exp(nlabels))(t.liftPos(this))
  }

  def translateAction(t: Translator, decl: PLockActionDecl, d: PLockActionDef, typ: Type) : LockAction = {
    val params = Seq(LocalVarDecl(d.args(0).name, typ)(t.liftPos(d.args(0))), LocalVarDecl(d.args(1).name, t.ttyp(decl.argType))(t.liftPos(d.args(1))))
    val newVal = t.exp(d.newVal)
    val pre = t.exp(d.pre)
    LockAction(decl.idndef.name, t.ttyp(decl.argType), decl.duplicable, params, newVal, pre)(t.liftPos(d))
  }

  override def transform(go: PNode => PNode): PExtender = {
    PLockSpec(go(idndef).asInstanceOf[PIdnDef], go(t).asInstanceOf[PType], invariant.transform(go), alpha.transform(go), if (hist.isDefined) Some(hist.get.transform(go)) else None, actionList map (go(_).asInstanceOf[PLockActionDecl]), actions map (_.transform(go)), proofs map (_.transform(go)), go(nlabels).asInstanceOf[PExp])
  }
}

case class PBarrierSpec(idndef: PIdnDef, in: PInvariantDef, totalIn: PInvariantDef, totalOut: PInvariantDef, out: PInvariantDef) extends PExtender with PMember {
  override def getsubnodes: Seq[PNode] = Seq(idndef) ++ in.subnodes ++ out.subnodes ++ totalIn.subnodes ++ totalOut.subnodes

  override def typecheck(tc: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    in.typecheckBarrierAssertion(tc, n, idndef.name, "in")
    out.typecheckBarrierAssertion(tc, n, idndef.name, "out")
    totalIn.typecheckBarrierAssertion(tc, n, idndef.name, "totalIn")
    totalOut.typecheckBarrierAssertion(tc, n, idndef.name, "totalOut")
    None
  }

  override def translateMemberSignature(t: Translator): Member = BarrierSpec(idndef.name, null, null, null, null)()

  override def translateMember(t: Translator): Member = {
    val tIn = in.translateBarrierAss(t)
    val tOut = out.translateBarrierAss(t)
    val tTotalIn = totalIn.translateBarrierAss(t)
    val tTotalOut = totalOut.translateBarrierAss(t)
    BarrierSpec(idndef.name, tIn, tTotalIn, tTotalOut, tOut)(t.liftPos(this))
  }

  override def transform(go: PNode => PNode): PExtender = {
    PBarrierSpec(go(idndef).asInstanceOf[PIdnDef], in.transform(go), totalIn.transform(go), totalOut.transform(go), out.transform(go))
  }

}


case class PLow(e: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(e)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(e, None)
    this.typ = PPrimitiv("Bool")
    None
  }

  override def translateExp(t: Translator): Exp = {
    SIFLowExp(t.exp(e), None)(t.liftPos(this))
  }

  override def transform(go: PNode => PNode): PExtender = {
    PLow(go(e).asInstanceOf[PExp])
  }
}

//case class PRel(e: PIdnUse, i: PIntLit) extends PExtender with PExp {
//  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
//    _typeSubstutions = Seq(ts)
//  }
//
//  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)
//
//  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions
//
//  override def getsubnodes(): Seq[PNode] = Seq(e, i)
//
//  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
//    t.checkTopTyped(e, None)
//    this.typ = e.typ
//    if (i.i != 0 && i.i != 1)
//      Some(Seq("Only executions 0 and one are valid in rel-expressions"))
//    else
//      None
//  }
//
//  override def translateExp(t: Translator): Exp = {
//    SIFRelExp(t.exp(e).asInstanceOf[LocalVar], t.exp(i).asInstanceOf[IntLit])(t.liftPos(this))
//  }
//
//  override def transform(go: PNode => PNode): PExtender = {
//    PRel(go(e).asInstanceOf[PIdnUse], go(i).asInstanceOf[PIntLit])
//  }
//}

case class PLowEvent() extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq()

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    this.typ = PPrimitiv("Bool")
    None
  }

  override def translateExp(t: Translator): Exp = {
    SIFLowEventExp()(t.liftPos(this))
  }

  override def transform(go: PNode => PNode): PExtender = {
    this
  }
}

case class PJoinable(method: PIdnUse, e: PExp, arguments: Seq[PExp]) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(method, e) ++ arguments

  override def translateExp(t: Translator): Exp = {
    Joinable(method.name, t.exp(e), arguments map (t.exp(_)))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(e, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(method) match {
      case m: PMethod => {
        if (m.formalArgs.length == arguments.length){
          for (i <- 0 until arguments.length) {
            t.checkTopTyped(arguments(i), Some(m.formalArgs(i).typ))
          }
          this.typ = PPrimitiv("Bool")
          None
        }else{
          Some(Seq("Wrong number of arguments in joinable[" + method.name + "]"))
        }
      }
      case _ => Some(Seq("Unknown method: " + method.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PJoinable(go(method).asInstanceOf[PIdnUse], go(e).asInstanceOf[PExp], arguments map (go(_).asInstanceOf[PExp]))
  }
}

case class PLock(lockType: PIdnUse, lockRef: PExp, amount: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockRef, amount)

  override def translateExp(t: Translator): Exp = {
    Lock(lockType.name, t.exp(lockRef), t.exp(amount))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockRef, Some(PPrimitiv("Ref")))
    t.checkTopTyped(amount, Some(PPrimitiv("Perm")))
    n.definition(t.curMember)(lockType) match {
      case _: PLockSpec => {
        this.typ = PPrimitiv("Bool")
        None
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PLock(go(lockType).asInstanceOf[PIdnUse], go(lockRef).asInstanceOf[PExp], go(amount).asInstanceOf[PExp])
  }
}

case class PLocked(lockType: PIdnUse, lockRef: PExp, value: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockRef, value)

  override def translateExp(t: Translator): Exp = {
    Locked(lockType.name, t.exp(lockRef), t.exp(value))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockRef, Some(PPrimitiv("Ref")))

    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        t.checkTopTyped(value, Some(ls.t))
        this.typ = PPrimitiv("Bool")
        None
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PLocked(go(lockType).asInstanceOf[PIdnUse], go(lockRef).asInstanceOf[PExp], go(value).asInstanceOf[PExp])
  }
}

case class PSeen(lockType: PIdnUse, lockRef: PExp, value: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockRef, value)

  override def translateExp(t: Translator): Exp = {
    Seen(lockType.name, t.exp(lockRef), t.exp(value))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockRef, Some(PPrimitiv("Ref")))

    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        t.checkTopTyped(value, Some(ls.t))
        this.typ = PPrimitiv("Bool")
        None
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PSeen(go(lockType).asInstanceOf[PIdnUse], go(lockRef).asInstanceOf[PExp], go(value).asInstanceOf[PExp])
  }
}


case class PBarrier(barrierType: PIdnUse, barrierRef: PExp, indexExp: PExp, totalExp: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(barrierType, barrierRef, indexExp, totalExp)

  override def translateExp(t: Translator): Exp = {
    Barrier(barrierType.name, t.exp(barrierRef), t.exp(indexExp), t.exp(totalExp))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(barrierRef, Some(PPrimitiv("Ref")))
    t.checkTopTyped(indexExp, Some(PPrimitiv("Int")))
    t.checkTopTyped(totalExp, Some(PPrimitiv("Int")))
    n.definition(t.curMember)(barrierType) match {
      case ls: PBarrierSpec => {
        this.typ = PPrimitiv("Bool")
        None
      }
      case _ => Some(Seq("Unknown barrier type: " + barrierType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PBarrier(go(barrierType).asInstanceOf[PIdnUse], go(barrierRef).asInstanceOf[PExp], go(indexExp).asInstanceOf[PExp], go(totalExp).asInstanceOf[PExp])
  }
}

case class PSGuard(lockType: PIdnUse, guardName: PIdnUse, lockRef: PExp, labels: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockRef, labels)

  override def translateExp(t: Translator): Exp = {
    SGuard(lockType.name, guardName.name, t.exp(lockRef), t.exp(labels))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockRef, Some(PPrimitiv("Ref")))

    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        ls.actionList.find(la => la.idndef.name == guardName.name) match {
          case Some(a) => {
            if (a.duplicable) {
              t.checkTopTyped(labels, Some(PSetType(PPrimitiv("Int"))))
              this.typ = PPrimitiv("Bool")
              None
            }else{
              Some(Seq("Action not shared: " + guardName.name))
            }
          }
          case None => Some(Seq("Unknown action: " + guardName.name))
        }
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PSGuard(go(lockType).asInstanceOf[PIdnUse], go(guardName).asInstanceOf[PIdnUse], go(lockRef).asInstanceOf[PExp], go(labels).asInstanceOf[PExp])
  }
}

case class PSGuardArgs(lockType: PIdnUse, guardName: PIdnUse, lockRef: PExp, labels: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockRef, labels)

  override def translateExp(t: Translator): Exp = {
    SGuardArgs(lockType.name, guardName.name, t.exp(lockRef), t.exp(labels), t.ttyp(this.typ))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockRef, Some(PPrimitiv("Ref")))

    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        ls.actionList.find(la => la.idndef.name == guardName.name) match {
          case Some(a) => {
            if (a.duplicable) {
              t.checkTopTyped(labels, Some(PSetType(PPrimitiv("Int"))))
              this.typ = PMultisetType(a.argType)
              None
            }else{
              Some(Seq("Action not shared: " + guardName.name))
            }
          }
          case None => Some(Seq("Unknown action: " + guardName.name))
        }
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PSGuardArgs(go(lockType).asInstanceOf[PIdnUse], go(guardName).asInstanceOf[PIdnUse], go(lockRef).asInstanceOf[PExp], go(labels).asInstanceOf[PExp])
  }
}

case class PUGuard(lockType: PIdnUse, guardName: PIdnUse, lockRef: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockRef)

  override def translateExp(t: Translator): Exp = {
    UGuard(lockType.name, guardName.name, t.exp(lockRef))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockRef, Some(PPrimitiv("Ref")))

    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        ls.actionList.find(la => la.idndef.name == guardName.name) match {
          case Some(a) => {
            if (!a.duplicable) {
              this.typ = PPrimitiv("Bool")
              None
            }else{
              Some(Seq("Action not unique: " + guardName.name))
            }
          }
          case None => Some(Seq("Unknown action: " + guardName.name))
        }
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PUGuard(go(lockType).asInstanceOf[PIdnUse], go(guardName).asInstanceOf[PIdnUse], go(lockRef).asInstanceOf[PExp])
  }
}

case class PUGuardArgs(lockType: PIdnUse, guardName: PIdnUse, lockRef: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockRef)

  override def translateExp(t: Translator): Exp = {
    UGuardArgs(lockType.name, guardName.name, t.exp(lockRef), t.ttyp(this.typ))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockRef, Some(PPrimitiv("Ref")))

    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        ls.actionList.find(la => la.idndef.name == guardName.name) match {
          case Some(a) => {
            if (!a.duplicable) {
              this.typ = PSeqType(a.argType)
              None
            }else{
              Some(Seq("Action not unique: " + guardName.name))
            }
          }
          case None => Some(Seq("Unknown action: " + guardName.name))
        }
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PUGuardArgs(go(lockType).asInstanceOf[PIdnUse], go(guardName).asInstanceOf[PIdnUse], go(lockRef).asInstanceOf[PExp])
  }
}

case class PAllPre(lockType: PIdnUse, guardName: PIdnUse, argsExp: PExp) extends PExtender with PExp {
  override def forceSubstitution(ts: PTypeSubstitution): Unit = {
    _typeSubstutions = Seq(ts)
  }

  var _typeSubstutions : Seq[PTypeSubstitution] = Seq(PTypeSubstitution.id)

  override def typeSubstitutions: Seq[PTypeSubstitution] = _typeSubstutions

  override def getsubnodes(): Seq[PNode] = Seq(lockType, argsExp)

  override def translateExp(t: Translator): Exp = {
    AllPre(lockType.name, guardName.name, t.exp(argsExp))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        ls.actionList.find(la => la.idndef.name == guardName.name) match {
          case Some(a) => {
            if (!a.duplicable) {
              t.checkTopTyped(argsExp, Some(PSeqType(a.argType)))
              this.typ = PPrimitiv("Bool")
              None
            }else{
              t.checkTopTyped(argsExp, Some(PMultisetType(a.argType)))
              this.typ = PPrimitiv("Bool")
              None
            }
          }
          case None => Some(Seq("Unknown action: " + guardName.name))
        }
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PAllPre(go(lockType).asInstanceOf[PIdnUse], go(guardName).asInstanceOf[PIdnUse], go(argsExp).asInstanceOf[PExp])
  }
}

case class PLocktype() extends PExtender with PType {

  override def getsubnodes(): Seq[PNode] = subNodes

  override def subNodes: Seq[PType] = Seq()

  override def substitute(ts: PTypeSubstitution): PType = this

  override def isValidOrUndeclared: Boolean = true

  override def transform(go: PNode => PNode): PExtender = {
    this
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = None

  override def translateType(t: Translator): Type = Locktype()
}

case class PThreadtype() extends PExtender with PType {

  override def getsubnodes(): Seq[PNode] = subNodes

  override def subNodes: Seq[PType] = Seq()

  override def substitute(ts: PTypeSubstitution): PType = this

  override def isValidOrUndeclared: Boolean = true

  override def transform(go: PNode => PNode): PExtender = {
    this
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = None

  override def translateType(t: Translator): Type = Threadtype()
}

case class PFork(method: PIdnUse, target: PIdnUse, args: Seq[PExp]) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(method, target) ++ args

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(target, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(method) match {
      case m: PMethod => {
        if (m.formalArgs.length == args.length){
          for (i <- 0 until args.length){
            t.checkTopTyped(args(i), Some(m.formalArgs(i).typ))
          }
          None
        }else {
          Some(Seq("Incorrect number of arguments"))
        }
      }
      case _ => Some(Seq("Unknown method: " + method.name))
    }
  }

  override def translateStmt(t: Translator): Stmt = {
    Fork(method.name, t.exp(target).asInstanceOf[LocalVar], args map (t.exp(_)))(t.liftPos(this))
  }

  override def transform(go: PNode => PNode): PExtender = {
    PFork(go(method).asInstanceOf[PIdnUse], go(target).asInstanceOf[PIdnUse], args map (go(_).asInstanceOf[PExp]))
  }
}

case class PJoin(method: PIdnUse, resVars: Seq[PIdnUse], token: PExp) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(method, token) ++ resVars

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(token, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(method) match {
      case m: PMethod => {
        if (m.formalReturns.length == resVars.length){
          for (i <- 0 until resVars.length){
            t.checkTopTyped(resVars(i), Some(m.formalReturns(i).typ))
          }
          var hasOld = false
          m.posts.foreach(post => post.visit({
            case _: POld => hasOld = true
          }))
          if (hasOld){
            Some(Seq("Joining methods with old expressions in postcondition is not supported."))
          }else{
            None
          }
        }else {
          Some(Seq("Incorrect number of target variables"))
        }
      }
      case _ => Some(Seq("Unknown method: " + method.name))
    }
  }

  override def translateStmt(t: Translator): Stmt = {
    Join(method.name, resVars map (t.exp(_).asInstanceOf[LocalVar]), t.exp(token))(t.liftPos(this))
  }

  override def transform(go: PNode => PNode): PExtender = {
    PJoin(go(method).asInstanceOf[PIdnUse], resVars map (go(_).asInstanceOf[PIdnUse]),  go(token).asInstanceOf[PExp])
  }
}

case class PNewLock(lockType: PIdnUse, target: PIdnUse, fields: Seq[PIdnUse]) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(lockType, target) ++ fields

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(target, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        for (f <- fields){
          n.definition(t.curMember)(f) match {
            case fieldDef:PField => f.typ = fieldDef.typ
            case _ => return Some(Seq("Expected field: " + f.name))
          }
        }
        None
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def translateStmt(t: Translator): Stmt = {
    NewLock(lockType.name, LocalVar(target.name, t.ttyp(target.typ))(t.liftPos(target)), fields map (f => Field(f.name, t.ttyp(f.typ))(t.liftPos(f))))(t.liftPos(this))
  }

  override def transform(go: PNode => PNode): PExtender = {
    PNewLock(go(lockType).asInstanceOf[PIdnUse], go(target).asInstanceOf[PIdnUse], fields map (go(_).asInstanceOf[PIdnUse]))
  }
}

case class PNewBarrier(barrierType: PIdnUse, target: PIdnUse, num: PExp, fields: Seq[PIdnUse]) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(barrierType, target, num) ++ fields

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(target, Some(PPrimitiv("Ref")))
    t.checkTopTyped(num, Some(PPrimitiv("Int")))
    n.definition(t.curMember)(barrierType) match {
      case ls: PBarrierSpec => {
        for (f <- fields){
          n.definition(t.curMember)(f) match {
            case fieldDef:PField => f.typ = fieldDef.typ
            case _ => return Some(Seq("Expected field: " + f.name))
          }
        }
        None
      }
      case _ => Some(Seq("Unknown barrier type: " + barrierType.name))
    }
  }

  override def translateStmt(t: Translator): Stmt = {
    NewBarrier(barrierType.name, LocalVar(target.name, t.ttyp(target.typ))(t.liftPos(target)), t.exp(num), fields map (f => Field(f.name, t.ttyp(f.typ))(t.liftPos(f))))(t.liftPos(this))
  }

  override def transform(go: PNode => PNode): PExtender = {
    PNewBarrier(go(barrierType).asInstanceOf[PIdnUse], go(target).asInstanceOf[PIdnUse], go(num).asInstanceOf[PExp], fields map (go(_).asInstanceOf[PIdnUse]))
  }
}

case class PWith(lockType: PIdnUse, lockExp: PExp, whenExp: Option[PExp], actionName: PIdnUse, actionArg: PExp, lbl: Option[PExp], bod: PStmt) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockExp, actionArg, bod) ++ whenExp.toIterator ++ lbl.toIterator

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockExp, Some(PPrimitiv("Ref")))
    if (whenExp.isDefined){
      t.checkTopTyped(whenExp.get, Some(PPrimitiv("Bool")))
    }
    t.check(bod)
    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        val actionDecl = ls.actionList.find(a => a.idndef.name == actionName.name)
        if (actionDecl.isDefined) {
          t.checkTopTyped(actionArg, Some(actionDecl.get.argType))
          if (actionDecl.get.duplicable){
            if (lbl.isDefined){
              t.checkTopTyped(lbl.get, Some(PPrimitiv("Int")))
              None
            }else{
              Some(Seq("Missing label expression for with-statement performing shared action : " + actionName.name))
            }
          }else{
            if (lbl.isDefined){
              Some(Seq("Got label expression for with-statement performing unique action : " + actionName.name))
            }else{
              None
            }
          }
        }else {
          Some(Seq("Unknown action: " + actionName.name))
        }
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def translateStmt(t: Translator): Stmt = {
    With(lockType.name, t.exp(lockExp), if (whenExp.isDefined) Some(t.exp(whenExp.get)) else None, actionName.name, t.exp(actionArg), if (lbl.isDefined) Some(t.exp(lbl.get)) else None, t.stmt(bod))(t.liftPos(this))
  }

  override def transform(go: PNode => PNode): PExtender = {
    PWith(go(lockType).asInstanceOf[PIdnUse], go(lockExp).asInstanceOf[PExp], whenExp.flatMap(w => Some(go(w).asInstanceOf[PExp])), go(actionName).asInstanceOf[PIdnUse], go(actionArg).asInstanceOf[PExp], lbl.flatMap(l => Some(go(l).asInstanceOf[PExp])), go(bod).asInstanceOf[PStmt])
  }
}

case class PAcquire(lockType: PIdnUse, lockExp: PExp) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockExp)

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockExp, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => None
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def translateStmt(t: Translator): Stmt = {
    Acquire(lockType.name, t.exp(lockExp))(t.liftPos(this))
  }

  override def transform(go: PNode => PNode): PExtender = {
    PAcquire(go(lockType).asInstanceOf[PIdnUse], go(lockExp).asInstanceOf[PExp])
  }
}

case class PRelease(lockType: PIdnUse, lockExp: PExp, action: Option[(PIdnUse, PExp)]) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockExp) ++ (if (action.isDefined) Seq(action.get._1, action.get._2) else Seq())

  override def translateStmt(t: Translator): Stmt = {
    Release(lockType.name, t.exp(lockExp), if (action.isDefined) Some((action.get._1.name, t.exp(action.get._2))) else None)(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockExp, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        if (action.isDefined){
          val actionDecl = ls.actionList.find(a => a.idndef.name == action.get._1.name)
          if (actionDecl.isDefined) {
            t.checkTopTyped(action.get._2, Some(actionDecl.get.argType))
            None
          }else{
            Some(Seq("Unknown action: " + action.get._1.name))
          }
        }else{
          None
        }
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PRelease(go(lockType).asInstanceOf[PIdnUse], go(lockExp).asInstanceOf[PExp], if (action.isDefined) Some((go(action.get._1).asInstanceOf[PIdnUse], go(action.get._2).asInstanceOf[PExp])) else None)
  }
}

case class PUnshare(lockType: PIdnUse, lockExp: PExp) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockExp)

  override def translateStmt(t: Translator): Stmt = {
    Unshare(lockType.name, t.exp(lockExp))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockExp, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        None
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PUnshare(go(lockType).asInstanceOf[PIdnUse], go(lockExp).asInstanceOf[PExp])
  }
}

case class PShare(lockType: PIdnUse, lockExp: PExp, lockVal: PExp) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockExp, lockVal)

  override def translateStmt(t: Translator): Stmt = {
    Share(lockType.name, t.exp(lockExp), t.exp(lockVal))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockExp, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        t.checkTopTyped(lockVal, Some(ls.t))
        None
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PShare(go(lockType).asInstanceOf[PIdnUse], go(lockExp).asInstanceOf[PExp], go(lockVal).asInstanceOf[PExp])
  }
}

case class PMerge(lockType: PIdnUse, action: PIdnUse, lockExp: PExp, lbls1: PExp, lbls2: PExp) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockExp, lbls1, lbls2)

  override def translateStmt(t: Translator): Stmt = {
    Merge(lockType.name, action.name, t.exp(lockExp), t.exp(lbls1), t.exp(lbls2))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockExp, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        val actionDecl = ls.actionList.find(a => a.idndef.name == action.name)
        if (actionDecl.isDefined) {
          if (actionDecl.get.duplicable){
            t.checkTopTyped(lbls1, Some(PSetType(PPrimitiv("Int"))))
            t.checkTopTyped(lbls2, Some(PSetType(PPrimitiv("Int"))))
            None
          }else{
            Some(Seq("Cannot merge guards for unique action " + action.name))
          }
        }else{
          Some(Seq("Unknown action: " + action.name))
        }
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PMerge(go(lockType).asInstanceOf[PIdnUse], go(action).asInstanceOf[PIdnUse], go(lockExp).asInstanceOf[PExp], go(lbls1).asInstanceOf[PExp], go(lbls2).asInstanceOf[PExp])
  }
}

case class PSplit(lockType: PIdnUse, action: PIdnUse, lockExp: PExp, lbls1: PExp, lbls2: PExp, args1: PExp, args2: PExp) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(lockType, lockExp, lbls1, lbls2, args1, args2)

  override def translateStmt(t: Translator): Stmt = {
    Split(lockType.name, action.name, t.exp(lockExp), t.exp(lbls1), t.exp(lbls2), t.exp(args1), t.exp(args2))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(lockExp, Some(PPrimitiv("Ref")))
    n.definition(t.curMember)(lockType) match {
      case ls: PLockSpec => {
        val actionDecl = ls.actionList.find(a => a.idndef.name == action.name)
        if (actionDecl.isDefined) {
          if (actionDecl.get.duplicable){
            t.checkTopTyped(lbls1, Some(PSetType(PPrimitiv("Int"))))
            t.checkTopTyped(lbls2, Some(PSetType(PPrimitiv("Int"))))
            t.checkTopTyped(args1, Some(PMultisetType(actionDecl.get.argType)))
            t.checkTopTyped(args2, Some(PMultisetType(actionDecl.get.argType)))
            None
          }else{
            Some(Seq("Cannot merge guards for unique action " + action.name))
          }
        }else{
          Some(Seq("Unknown action: " + action.name))
        }
      }
      case _ => Some(Seq("Unknown lock type: " + lockType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PSplit(go(lockType).asInstanceOf[PIdnUse], go(action).asInstanceOf[PIdnUse], go(lockExp).asInstanceOf[PExp], go(lbls1).asInstanceOf[PExp], go(lbls2).asInstanceOf[PExp], go(args1).asInstanceOf[PExp], go(args2).asInstanceOf[PExp])
  }
}

case class PWait(barrierType: PIdnUse, barrierExp: PExp, indexExp: PExp, totalExp: PExp) extends PExtender with PStmt {
  override def getsubnodes(): Seq[PNode] = Seq(barrierType, barrierExp, indexExp, totalExp)

  override def translateStmt(t: Translator): Stmt = {
    Wait(barrierType.name, t.exp(barrierExp), t.exp(indexExp), t.exp(totalExp))(t.liftPos(this))
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkTopTyped(barrierExp, Some(PPrimitiv("Ref")))
    t.checkTopTyped(indexExp, Some(PPrimitiv("Int")))
    t.checkTopTyped(totalExp, Some(PPrimitiv("Int")))
    n.definition(t.curMember)(barrierType) match {
      case ls: PBarrierSpec => {
        None
      }
      case _ => Some(Seq("Unknown barrier type: " + barrierType.name))
    }
  }

  override def transform(go: PNode => PNode): PExtender = {
    PWait(go(barrierType).asInstanceOf[PIdnUse], go(barrierExp).asInstanceOf[PExp], go(indexExp).asInstanceOf[PExp], go(totalExp).asInstanceOf[PExp])
  }
}