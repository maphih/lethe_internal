import org.junit.Assert._
import uk.ac.man.cs.lethe.internal.dl.datatypes.{Individual, Ontology, Subsumption, TBox}
import uk.ac.man.cs.lethe.internal.dl.forgetting.direct.{ALCFormulaPreparations, AdvancedSymbolOrderings, ConceptLiteralOrdering}
import uk.ac.man.cs.lethe.internal.dl.parsing.DLParser

import scala.io.Source
import org.junit.Test
import uk.ac.man.cs.lethe.internal.dl.datatypes.extended.ExtendedABoxClause
import uk.ac.man.cs.lethe.internal.dl.learning.{Interpolation, LearningProblem, LearningTools}
import uk.ac.man.cs.lethe.internal.dl.proofs.InferenceLogger
import uk.ac.man.cs.lethe.internal.dl.refutation.RefutationProver

class ReasoningExamples {

  @Test
  def testConversion() = {
    val (abox, tbox, positive, negative) = LearningTools.toClauseUnsatisfiability(learningProblem1)

    println("TBox:")
    tbox.foreach(println)
    println()
    println("ABox:")
    abox.foreach(println)
    println()
    println("Positive: "+positive)
    println("Negative: "+negative)
  }

  @Test
  def testRefutationProver() = {

    val problem = learningProblem1

    val (abox, tbox, posClause, negClause) = LearningTools.toClauseUnsatisfiability(problem)

    val refutationProver = new RefutationProver()
    refutationProver.setLiteralOrdering(LearningTools.orderingForRefutation(problem.ontology))
    refutationProver.addABoxClauses(abox)
    refutationProver.addTBoxClauses(tbox)
    refutationProver.addABox(problem.ontology.abox)
    refutationProver.setFocusSet(Set(posClause, negClause))
    refutationProver.setInferenceLogger(InferenceLogger)

    println("Start reasoning...")

    assertFalse(refutationProver.reason())

    println()
    println("Inferences: ")
    println("============")
    println()
    InferenceLogger.derivations.foreach(println)

    val interpolator = new Interpolation(InferenceLogger)
    interpolator.computeInterpolant(posClause, negClause)
  }

  def learningProblem1 = {
    // Parent example to strongly learn "Mother" as concept
    //
    // Positive: Hanna, Eva
    // Negative: Erica, Tom
    // kids: Peter, Jim
    //
    // hasChild(Hanna, Peter)
    // Female(Hanna)
    // Female(Eva)
    // Parent(Eva)
    //
    // Female(Erica)
    // Childless(Erica)
    // hasChild(Tom, Peter)
    // Male(Tom)
    //
    // Parent = EhasChild.Person
    // Person = Female or Male
    // Male and Female <= BOTTOM
    // Childless <= ¬EhasChild.TOP
    //
    LearningProblem(
      DLParser.parse(
        Source.fromResource("strongLearningExample1.dl")),
        Set("hanna", "eva").map(Individual),
        Set("erica","tom").map(Individual)
    )
/*
  */
  }
}
