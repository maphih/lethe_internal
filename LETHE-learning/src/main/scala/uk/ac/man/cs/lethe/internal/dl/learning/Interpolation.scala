package uk.ac.man.cs.lethe.internal.dl.learning

import uk.ac.man.cs.lethe.internal.dl.datatypes.{BaseConcept, BottomConcept, Concept, ConceptComplement, ConceptConjunction, ConceptDisjunction, DLHelpers, DLStatement, ExistentialRoleRestriction, Expression, Individual, RoleAssertion, TopConcept, UniversalRoleRestriction}
import uk.ac.man.cs.lethe.internal.dl.datatypes.extended.ExtendedABoxClause
import uk.ac.man.cs.lethe.internal.dl.forgetting.direct.{AbstractDerivation, ConceptLiteral}
import uk.ac.man.cs.lethe.internal.dl.proofs.AbstractInferenceLogger
import uk.ac.man.cs.lethe.internal.dl.datatypes.Substitution
import uk.ac.man.cs.lethe.internal.dl.refutation.{LiteralABoxDerivation, LiteralMixedDerivation, RoleAssertionABoxDerivation}

class Interpolation(inferenceLogger: AbstractInferenceLogger) {

  var processedClauses = Map[Expression, Marker]()

  var unprocessedDerivations = Set[AbstractDerivation]()

  val keepsPositive = Set(POSITIVE,NEUTRAL)
  val keepsNegative = Set(NEGATIVE,NEUTRAL)


  def computeInterpolant(positiveClause: ExtendedABoxClause, negativeClause: ExtendedABoxClause) = {
    processedClauses = Map[Expression, Marker]()

    processedClauses += (positiveClause -> POSITIVE)
    processedClauses += (negativeClause -> NEGATIVE)

    inferenceLogger.inputClauses.foreach(cl => {
      if (!processedClauses.contains(cl))
        processedClauses += (cl -> NEUTRAL)
    })

    unprocessedDerivations = Set() ++ inferenceLogger.derivations
    var derivationQueue = List[AbstractDerivation]()

    while (!unprocessedDerivations.isEmpty) {
      if (derivationQueue.isEmpty) {
        println("New round!")
        derivationQueue = List() ++ unprocessedDerivations
      }
      val derivation = derivationQueue.head
      derivationQueue = derivationQueue.tail

      if (derivation.premisses().forall(processedClauses.contains)) {

        unprocessedDerivations -= (derivation)
        val newMarker: Marker = determineMarker(derivation)

        println()
        println("New marker: " + newMarker)
        println()
        derivation.conclusions().foreach { conclusion =>
          if (!processedClauses.contains(conclusion)
            || better(newMarker, processedClauses(conclusion))) {
            if (processedClauses.contains(conclusion)) {
              println("Replacing " + processedClauses(conclusion) + " with " + newMarker)
            }
            processedClauses += ((conclusion -> newMarker))
          }
        }
      }

    }
  }

  def better(marker1: Marker, marker2: Marker): Boolean = {
    if(marker1.isInstanceOf[Error]) {
      false
    } else if(marker2.isInstanceOf[Error]) {
      true
    } else if(marker1.isInstanceOf[Mixed] && !marker2.isInstanceOf[Mixed]) {
      false
    } else if(marker2.isInstanceOf[Mixed] && !marker1.isInstanceOf[Mixed]) {
      true
    } else if(marker1.isInstanceOf[Mixed] && marker2.isInstanceOf[Mixed]) {
      val c1 = marker1.asInstanceOf[Mixed].concept
      val c2 = marker2.asInstanceOf[Mixed].concept
      return c1.size<c2.size
    } else
      false
  }

  def determineMarker(derivation: AbstractDerivation): Marker = {
    val markers = derivation.premisses().map(processedClauses)
    println()
    println("Derivation: " + derivation)
    println("Markers: " + markers)
    println()

    if (markers.exists(_.isInstanceOf[Error]))
      Error("inherited error")
    else if (markers.forall(_.equals(NEUTRAL)))
      NEUTRAL
    else if (markers.forall(keepsPositive) && !derivation.isInstanceOf[RoleAssertionABoxDerivation]) {
      POSITIVE
    } else if (markers.forall(keepsNegative) && !derivation.isInstanceOf[RoleAssertionABoxDerivation]) {
      NEGATIVE
    } else derivation match {
      case RoleAssertionABoxDerivation(raPremise, rrPremise, RoleAssertion(r, root, successor), rrLiteral, conclusion) =>
        if (raPremise.isEmpty) { // in this case, the premise is from the shared ABox, so we keep the marker
          processedClauses(rrPremise)
        } else {
          if (positive(raPremise.get) && negative(rrPremise)) {
            val filler = freshConcept()
            Mixed(ExistentialRoleRestriction(r, filler), root, Map(successor -> filler))
          } else if (negative(raPremise.get) && positive(rrPremise)) {
            val filler = freshConcept()
            Mixed(UniversalRoleRestriction(r, filler), root, Map(successor -> filler))
          } else if (markers.forall(keepsPositive)) {
            val filler = freshConcept()
            Mixed(ExistentialRoleRestriction(r, filler), root, Map(successor -> filler))
          } else if (markers.forall(keepsNegative)) {
            val filler = freshConcept()
            Mixed(UniversalRoleRestriction(r, filler), root, Map(successor -> filler))
          } else if (mixed(raPremise.get) && positive(rrPremise)) {
            val mixed = processedClauses(raPremise.get).asInstanceOf[Mixed]
            val filler = mixed.mapPositive.getOrElse(successor, freshConcept())
            // TODO check this case!
            mixed.insert(root, ExistentialRoleRestriction(r, filler), successor -> filler)
          } else if (positive(raPremise.get) && mixed(rrPremise)) {
            val mixed = processedClauses(rrPremise).asInstanceOf[Mixed]
            val filler = mixed.mapPositive.getOrElse(successor, freshConcept())
            // TODO check this case!
            mixed.insert(root, ExistentialRoleRestriction(r, filler), successor -> filler)
          } else if (mixed(raPremise.get) && negative(rrPremise)) {
            val mixed = processedClauses(raPremise.get).asInstanceOf[Mixed]
            val filler = mixed.mapPositive.getOrElse(successor, freshConcept())
            mixed.insert(root, ExistentialRoleRestriction(r, filler), successor -> filler)
          } else if (negative(raPremise.get) && mixed(rrPremise)) {
            val mixed = processedClauses(rrPremise).asInstanceOf[Mixed]
            val filler = mixed.mapPositive.getOrElse(successor, freshConcept())
            mixed.insert(root, UniversalRoleRestriction(r, filler), successor -> filler)
          } else if (mixed(raPremise.get) && mixed(rrPremise)) {
            val mixed1 = processedClauses(raPremise.get).asInstanceOf[Mixed]
            val mixed2 = processedClauses(raPremise.get).asInstanceOf[Mixed]
            val merged = combine(Set(mixed1, mixed2))
            val filler = merged.mapPositive.getOrElse(successor, freshConcept())
            // TODO check: disjunction or conjunction?
            merged.insert(root, ExistentialRoleRestriction(r, filler), successor -> filler)
          } else {
            Error("Not supported: " + processedClauses(raPremise.get) + " with " + processedClauses(rrPremise))
          }
        }
      case LiteralMixedDerivation(aboxPremises, tboxPremises, aboxLiterals, individual, tboxLiterals, conclusion) =>
        determineMarker(LiteralABoxDerivation(aboxPremises,aboxLiterals,individual,conclusion)) // ignore TBox part, which is neutral by definition
      case LiteralABoxDerivation(premises, literals, individual, _) =>
        literals match {
          /* case Seq(ConceptLiteral(p1, a1: BaseConcept), ConceptLiteral(p2, a2: BaseConcept)) =>
             (processedClauses(premises(0)), processedClauses(premises(1))) match {
               case (POSITIVE, NEGATIVE) => new Mixed(toConcept(p1, a1), individual)
               case (NEGATIVE, POSITIVE) => new Mixed(toConcept(p2, a2), individual)
               case (POSITIVE, m: Mixed) => m.insert(individual, toConcept(p1, a1))
               case (m: Mixed, POSITIVE) => m.insert(individual, toConcept(p2, a2))
               case (NEGATIVE, m: Mixed) => m.insert(individual, toConcept(!p1, a1))
               case (m: Mixed, NEGATIVE) => m.insert(individual, toConcept(!p2, a2))
               case (m1: Mixed, m2: Mixed) => m1.combine(m2)
               case other => Error(other + " Not supported yet!")
             }*/
          case literals: Seq[ConceptLiteral] =>

            var positives = literals
              .indices
              .filter(i => positive(premises(i)))
              .map(literals(_))
            val negatives = literals
              .indices
              .filter(i => negative(premises(i)))
              .map(literals(_))
            val mixeds = literals
              .indices
              .filter(i => mixed(premises(i)))
              .map(literals(_))

            if (mixeds.isEmpty) // this also means that positive is non-empty
              new Mixed(conjunction(positives), individual)
            /* else if(mixeds.size==1) {
               val focus = premises.map(processedClauses)
                 .filter(_.isInstanceOf[Mixed])
                 .map(_.asInstanceOf[Mixed])
                 .head
               focus.insert(individual, conjunction(positives :+ mixeds(0)))
             }*/
            else if (negatives.isEmpty && individual.equals(Individual("a"))) { // TODO use of constant
              // no negatives to take care of -> literals resolved upon not relevant, we only need to aggregate
              // the mixed markings
              println("No negatives!")
              println("and individual is "+individual)
              combine(literals.indices
                .filter(i => mixed(premises(i)))
                .map(i =>
                  processedClauses(premises(i))
                    .asInstanceOf[Mixed]
                ))
            }
            else { // we have negatives to take care of -> this means the literals resolved upon are relevant
                   // later comment: the literals may always be relevant
              println("Negatives: " + negatives)
              println("and individual is " + individual)
              combine(literals.indices
                .filter(i => positive(premises(i)) || mixed(premises(i)) || neutral(premises(i)))
                .map(i => {
                  if (positive(premises(i)) || neutral(premises(i))) {
                    new Mixed(toConcept(literals(i)), individual)
                  } else { // mixed(premises(i))
                    processedClauses(premises(i))
                      .asInstanceOf[Mixed]
                      .insert(individual, toConcept(literals(i)))
                  }
                }))
            }

          // pos: A u Er.D1,   B u Ar.D2,    Ar.D3
          // neg: Ar.D4, ¬A,  ¬B
          // neutral: ¬D1 u ¬D2 u ¬D3 u ¬D4
          //
          // Er.D1   [Mixed(A) ]
          // Ar.D2   [Mixed(B) ]
          // BOTTOM  [Mixed((A u Er.D1) n (B u Ar.D2) n Ar.D3)]

          // pos: A u Er.D1,   B u Ar.D2,    Ar.D3
          // neg: ¬A,  ¬B
          // neutral: ¬D1 u ¬D2 u ¬D3
          //
          // Er.D1   [Mixed(A) ]
          // Ar.D2   [Mixed(B) ]
          // BOTTOM  [Mixed(A n B)]
        }
      case other => Error(other + " Not supported yet!")
    }
  }


  // Invariant for clauses marked with Mixed(concept, root, _) without other individuals:
  // clear: Clause v concept(root) is entailed by the positive and neutral clauses
  // concept(root) entails the negation of the negative clauses
  //
  // with individuals in the map:
  // for every individual a the corresponding concept name with the negation of the sub-clauses containing that individual
  // for the resulting concept, the claim should still hold
  //
  //
  // consider:
  // positive:  r(a,b)     A(b)
  // negative:  forall r.D1(a)
  // neutral:   ¬D1 or ¬A
  //
  // D1(b)      [Mixed(exists r.X1), a, b -> X1]  ---> (exists r.¬D1)(a)
  // ¬A(b)      [Mixed(exists r.X1), a, b -> X1]  ---> (exists r.¬¬A)(a)
  // BOTTOM     [Mixed(exists r.(X1 or A)), a, b -> X1]  ---> (exists r.A)(a)

  def toConcept(polarity: Boolean, concept: Concept) = {
    if (polarity) concept
    else DLHelpers.neg(concept)
  }

  def toConcept(literal: ConceptLiteral): Concept =
    toConcept(literal.polarity, literal.concept)

  def combine(marker: Iterable[Mixed]): Mixed = {
    println("Combining: "+marker)
    if(marker.size==1)
      marker.head
    else
      marker.reduce{ (a,b) => a.combine(b) }
  }

  def conjunction(literals: Iterable[ConceptLiteral]): Concept =
    DLHelpers.conjunction(literals.map(toConcept).toSet)

  def negative(clause: ExtendedABoxClause) =
    processedClauses(clause).equals(NEGATIVE)

  def positive(clause: ExtendedABoxClause) =
    processedClauses(clause).equals(POSITIVE)

  def neutral(clause: ExtendedABoxClause) =
    processedClauses(clause).equals(NEUTRAL)

  def mixed(clause: ExtendedABoxClause) =
    processedClauses(clause).isInstanceOf[Mixed]

  var counter = 0
  def freshConcept() = {
    // TODO: ensure we don't use an existing name!
    counter+=1
    BaseConcept("_X"+counter)
  }
}

trait Marker
object POSITIVE extends Marker {
  override def toString = "Positive"
}
object NEGATIVE extends Marker {
  override def toString = "Negative"
}

object NEUTRAL extends Marker {
  override def toString = "Neutral"
}

case class Mixed(concept: Concept, root: Individual,
                 mapPositive: Map[Individual, BaseConcept]) extends Marker {
  def this(concept: Concept, root: Individual) =
    this(concept, root, Map[Individual, BaseConcept]())

  def insert(individual: Individual, toInsert: Concept) = {
    if(individual.equals(root))
      Mixed(DLHelpers.disjunction(Set(concept,toInsert)), individual, mapPositive)
    else {
      val toReplace = mapPositive(individual)
      val subst = new Substitution(mapPositive(individual), DLHelpers.disjunction(toReplace, toInsert))
      Mixed(subst(concept),root,mapPositive)
    }
  }

  def insert(individual: Individual, toInsert: Concept, mapEntry: (Individual, BaseConcept)) = {
    if (individual.equals(root))
      Mixed(DLHelpers.disjunction(Set(concept, toInsert)), individual, mapPositive+mapEntry)
    else {
      val toReplace = mapPositive(individual)
      val subst = new Substitution(mapPositive(individual), DLHelpers.disjunction(toReplace, concept))
      Mixed(subst(concept), root, mapPositive+mapEntry)
    }
  }

  def combine(other: Mixed) = {
      //  if(!root.equals(other.root))
      //    Error("Different roots not supported")
      //  else {
      var concept2 = other.concept
      var newMap = mapPositive
      other.mapPositive.foreach(tuple => {
        if (mapPositive.contains(tuple._1)) {
          concept2 = new Substitution(tuple._2, mapPositive(tuple._1))(concept2)
        } else {
          newMap += tuple
        }
      })
    if (root.equals(other.root)) {
      Mixed(DLHelpers.conjunction(Set(concept, concept2)), root, newMap)
    } else if(mapPositive.contains(other.root)) {
      Mixed(
        new Substitution(mapPositive(other.root),
          DLHelpers.conjunction(Set(mapPositive(other.root), concept2)))
          .apply(concept), root, newMap
      )
    } else if(other.mapPositive.contains(root)) {
      Mixed(
        new Substitution(other.mapPositive(root),
          DLHelpers.conjunction(Set(other.mapPositive(root), concept)))
          .apply(concept2), other.root, newMap
      )
    } else
      throw new AssertionError("Cannot be combined: "+this+" and "+other)
  }

}

case class Error(message: String) extends Marker