package uk.ac.man.cs.lethe.internal.dl.learning

import com.sun.org.apache.xalan.internal.lib.ExsltBase
import uk.ac.man.cs.lethe.internal.dl.datatypes.extended.{ExtendedABoxClause, ExtendedABoxClausification}
import uk.ac.man.cs.lethe.internal.dl.datatypes.{BaseConcept, BaseRole, ExistentialRoleRestriction, Individual, Nominal, Ontology, UniversalRoleRestriction}
import uk.ac.man.cs.lethe.internal.dl.forgetting.abox.ABoxClause
import uk.ac.man.cs.lethe.internal.dl.forgetting.direct.{ALCFormulaPreparations, AdvancedSymbolOrderings, ConceptClause, ConceptLiteral, ConceptLiteralOrdering}

case class LearningProblem(ontology: Ontology, positiveExamples: Set[Individual], negativeExamples: Set[Individual])

object LearningTools {

  def orderingForRefutation(ontology: Ontology): Ordering[ConceptLiteral] = {
    val orderedSymbols =
      AdvancedSymbolOrderings.orderByNumOfOccurrences(ontology.signature, ontology).reverse

    orderingForRefutation(orderedSymbols.toSeq)
  }

  def orderingForRefutation(toSeq: Seq[String]) = {

    val position = Map() ++ toSeq.map(x => (x, toSeq.indexOf(x)))

    new Ordering[ConceptLiteral]() {
      override def compare(x: ConceptLiteral, y: ConceptLiteral): Int = (x, y) match {
        case (ConceptLiteral(_, Nominal(ind1)), ConceptLiteral(_, Nominal(ind2))) => compare(ind1, ind2)
        case (ConceptLiteral(_, _: Nominal), _) => -1
        case (_, ConceptLiteral(_, _: Nominal)) => +1
        case (ConceptLiteral(false, _), ConceptLiteral(true, _)) => +1
        case (ConceptLiteral(true, _), ConceptLiteral(false, _)) => -1
        case (ConceptLiteral(_, BaseConcept(c1)), ConceptLiteral(_, BaseConcept(c2))) => compare(c1, c2)
        case (_, ConceptLiteral(_, BaseConcept(c2))) => +1
        case (ConceptLiteral(_, BaseConcept(c2)),_) => -1
        case (ConceptLiteral(_, ExistentialRoleRestriction(BaseRole(r1),BaseConcept(c1))),
              ConceptLiteral(_, ExistentialRoleRestriction(BaseRole(r2),BaseConcept(c2)))) =>
          if(r1==r2)
            compare(c1,c2)
          else
            position(r1) - position(r2)
        case (ConceptLiteral(_, UniversalRoleRestriction(BaseRole(r1), BaseConcept(c1))),
              ConceptLiteral(_, UniversalRoleRestriction(BaseRole(r2), BaseConcept(c2)))) =>
          if (r1 == r2)
            compare(c1, c2)
          else {
            position(r1) - position(r2)
          }
        case (ConceptLiteral(_, _ : UniversalRoleRestriction), _) => -1
        case (_, ConceptLiteral(_, _: UniversalRoleRestriction)) => +1
        case other => throw new AssertionError("Unexpected literal: "+other)
      }

      def compare(ind1: Individual, ind2: Individual) = {
        ind1.name.compareTo(ind2.name)
      }
      def compare(name1: String, name2: String) = {
        if(position.contains(name1) && position.contains(name2))
          position(name1) - position(name2)
        else if (position.contains(name1))
          -1
        else if (position.contains(name2))
          +1
        else
          name1.compareTo(name2)
      }
    }
  }

  def toClauseUnsatisfiability(problem: LearningProblem):
  (Set[ExtendedABoxClause], Set[ConceptClause], ExtendedABoxClause, ExtendedABoxClause) = {
    ALCFormulaPreparations.initDefinitions()

    val ordering = orderingForRefutation(problem.ontology)

    var (aboxClauses, tboxClauses) =
      ExtendedABoxClausification.clausify(problem.ontology.abox.assertions, ordering)

    tboxClauses ++= ALCFormulaPreparations.clauses(problem.ontology.tbox.axioms, ordering)

    val root = freshIndividual(problem.ontology) //
    val posClause = new ExtendedABoxClause(
      Map(root -> new ConceptClause(
        problem.positiveExamples.map(ind => ConceptLiteral(true, Nominal(ind)))
      )))
    val negClause = new ExtendedABoxClause(
      Map(root -> new ConceptClause(
        problem.negativeExamples.map(ind => ConceptLiteral(true, Nominal(ind)))
      )))

    //aboxClauses += posClause
    //aboxClauses += negClause

    (aboxClauses, tboxClauses, posClause, negClause)
  }

  def freshIndividual(ontology: Ontology) = {
    var name = "a"
    var fresh = Individual(name)
    val individuals = ontology.individuals()

    while(individuals(fresh)){
      name += "*"
      fresh = Individual(name)
    }

    fresh
  }
}