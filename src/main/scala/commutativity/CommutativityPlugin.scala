package commutativity

import viper.silver.ast.Program
import viper.silver.parser._
import viper.silver.plugin.SilverPlugin
import viper.silver.verifier._


class CommutativityPlugin extends CommutativityParser with CommutativityTransformer with SilverPlugin {

  override def beforeParse(input: String, isImported: Boolean): String = {
    ParserExtension.addNewDeclAtEnd(newDeclAtEnd)
    ParserExtension.addNewExpAtStart(newExpAtStart)
    ParserExtension.addNewKeywords(extendedKeywords)
    ParserExtension.addNewStmtAtStart(newStmtAtStart)
    input
  }

  override def beforeResolve(input: PProgram): PProgram = {
    val transformed = input.transform({
      case PDomainType(name, args) if name.name == "Lock" && args.length == 0 => PPrimitiv("Ref")
      case PDomainType(name, args) if name.name == "Thread" && args.length == 0 => PPrimitiv("Ref")
      case PDomainType(name, args) if name.name == "Barrier" && args.length == 0 => PPrimitiv("Ref")
      case PAssume(e) => PInhale(e)
    })()

    val pfunc = PFunction(PIdnDef("intervalSet"), Seq(PFormalArgDecl(PIdnDef("$frm"), PPrimitiv("Int")), PFormalArgDecl(PIdnDef("$ntl"), PPrimitiv("Int"))), PSetType(PPrimitiv("Int")), Seq(), Seq(), None)
    transformed.copy(functions=transformed.functions ++ Seq(pfunc))
  }

  override def beforeConsistencyCheck(input: Program): Program = {
    encodeProgram(input)
  }

  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    input match {
      case Failure(errors) => Failure(errors)
      case Success => input
    }
  }
}
