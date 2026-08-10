package uk.ac.man.cs.lethe.internal.dl.refutation

import uk.ac.man.cs.lethe.internal.dl.datatypes.extended.ExtendedABoxClause
import uk.ac.man.cs.lethe.internal.dl.datatypes.{Individual, RoleAssertion}
import uk.ac.man.cs.lethe.internal.dl.forgetting.direct.{AbstractDerivation, ConceptClause, ConceptLiteral}

case class LiteralTBoxDerivation(premises: Seq[ConceptClause], literals: Seq[ConceptLiteral], conclusion: ConceptClause)
  extends AbstractDerivation(premises, Some(conclusion), "TBox inference") {
  override def copy: AbstractDerivation = new LiteralTBoxDerivation(premises, literals, conclusion)

  override val getRuleName = "inference on " + literals.map(_.concept).toSet.mkString(", ")

}

case class LiteralABoxDerivation(premises: Seq[ExtendedABoxClause], literals: Seq[ConceptLiteral], individual: Individual,
                            conclusion: ExtendedABoxClause)
  extends AbstractDerivation(premises, Some(conclusion), "ABox inference") {
  override def copy: AbstractDerivation = new LiteralABoxDerivation(premises, literals, individual, conclusion)

  override val getRuleName = "inference on "+individual+" and "+literals.map(_.concept).toSet.mkString(", ")
}


case class LiteralMixedDerivation(aboxPremises: Seq[ExtendedABoxClause],
                             tboxPremises: Seq[ConceptClause],
                             aboxLiterals: Seq[ConceptLiteral],
                             individual: Individual,
                             tboxLiterals: Seq[ConceptLiteral],
                            conclusion: ExtendedABoxClause)
  extends AbstractDerivation(aboxPremises++tboxPremises, Some(conclusion), "Mixed inference"){
  override def copy: AbstractDerivation = {
    new LiteralMixedDerivation(aboxPremises, tboxPremises, aboxLiterals, individual, tboxLiterals, conclusion)
  }

  override val getRuleName = "inference on "+individual+" and " +
    (aboxLiterals++tboxLiterals).map(_.concept).toSet.mkString(", ")

}

case class RoleAssertionABoxDerivation(raPremise: Option[ExtendedABoxClause],
                                  rrPremise: ExtendedABoxClause,
                                  raLiteral: RoleAssertion,
                                  rrLiteral: ConceptLiteral,
                                  conclusion: ExtendedABoxClause)
extends AbstractDerivation(Seq(rrPremise)++raPremise, Some(conclusion), "RA-ABox Inference") {
  override def copy: AbstractDerivation =
    new RoleAssertionABoxDerivation(raPremise, rrPremise, raLiteral, rrLiteral, conclusion)
}


case class RoleAssertionTBoxDerivation(raPremise: ExtendedABoxClause,
                                  rrPremise: Option[ConceptClause],
                                  raLiteral: RoleAssertion,
                                  rrLiteral: ConceptLiteral,
                                  conclusion: ExtendedABoxClause)
  extends AbstractDerivation(Seq(raPremise)++rrPremise, Some(conclusion), "RA-TBox Inference") {
  override def copy: AbstractDerivation =
    new RoleAssertionTBoxDerivation(raPremise, rrPremise, raLiteral, rrLiteral, conclusion)
}
