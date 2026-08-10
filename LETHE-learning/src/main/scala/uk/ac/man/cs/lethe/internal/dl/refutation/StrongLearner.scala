package uk.ac.man.cs.lethe.internal.dl.refutation

import uk.ac.man.cs.lethe.internal.dl.datatypes.extended.ExtendedABoxClause
import uk.ac.man.cs.lethe.internal.dl.datatypes.{Concept, Individual, Nominal, Ontology}
import uk.ac.man.cs.lethe.internal.dl.forgetting.direct.{ConceptClause, ConceptLiteral}

class StrongLearner(ontology: Ontology) {
  def learn(positiveExamples: Set[Individual], negativeExamples: Set[Individual]): LearningResult = {

    val root = Individual("a")
    val posClause = new ExtendedABoxClause(
      Map(root -> new ConceptClause(
        positiveExamples.map(ind => ConceptLiteral(true, Nominal(ind)))
    )))
    val negClause = new ExtendedABoxClause(
      Map(root -> new ConceptClause(
        negativeExamples.map(ind => ConceptLiteral(true, Nominal(ind)))
      )))


    throw new AssertionError("Not implemented!")
  }
}

trait LearningResult

/**
 * A concept that should satisfy all positive examples, while its negation satisfies all negative examples
 * @param concept
 */
case class LearnedConcept(concept: Concept) extends LearningResult

/**
 * In case strong learning fails, there should be a pair of individual names that cannot be separated
 */
case class Unseparable(positiveExample: Individual, negativeExample: Individual)