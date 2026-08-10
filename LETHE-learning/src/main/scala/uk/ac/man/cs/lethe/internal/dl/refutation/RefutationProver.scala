package uk.ac.man.cs.lethe.internal.dl.refutation

import uk.ac.man.cs.lethe.internal.dl.datatypes.extended.ExtendedABoxClause
import uk.ac.man.cs.lethe.internal.dl.datatypes.{extended, _}
import uk.ac.man.cs.lethe.internal.dl.forgetting.direct.{ConceptClause, ConceptClauseOrdering, ConceptLiteral}
import uk.ac.man.cs.lethe.internal.dl.learning._
import uk.ac.man.cs.lethe.internal.dl.proofs.{AbstractInferenceLogger, InferenceLogger}

import scala.collection.{SortedSet, mutable}

class RefutationProver {

  val NO_ABOX = true

  val FORWARD_SUBSUMPTION=true
  val BACKWARD_SUBSUMPTION=true
  val SET_OF_SUPPORT=true

  protected var inferenceLogger: AbstractInferenceLogger = InferenceLogger.dummyLogger

  private var aboxClauses: Set[ExtendedABoxClause] = Set()
  private var tbox: Set[ConceptClause] = Set()

  private var toProcess: SortedSet[ExtendedABoxClause] = _
  private var toProcessTBox: SortedSet[ConceptClause] = _
  private var processedTBox: Set[ConceptClause] = Set()

  private var individuals: Set[Individual] = Set()

  // map individual name to concept names in ABox
  private var individual2concept =
    new mutable.HashMap[Individual, mutable.Set[BaseConcept]]()
      with mutable.MultiMap[Individual, BaseConcept]

  private var individual2successor =
    new mutable.HashMap[Individual, mutable.MultiMap[Role,Individual]]()


  private var literal2TBox: mutable.MultiMap[ConceptLiteral, ConceptClause] =
    new mutable.HashMap[ConceptLiteral, mutable.Set[ConceptClause]]()
      with mutable.MultiMap[ConceptLiteral, ConceptClause]

  private var literal2ABox: mutable.MultiMap[(Individual, ConceptLiteral), ExtendedABoxClause] =
    new mutable.HashMap[(Individual,ConceptLiteral), mutable.Set[ExtendedABoxClause]]()
      with mutable.MultiMap[(Individual, ConceptLiteral), ExtendedABoxClause]

  private var roleSuccessors: mutable.MultiMap[(Individual, Role), (RoleAssertion, ExtendedABoxClause)] =
    new mutable.HashMap[(Individual, Role), mutable.Set[(RoleAssertion, ExtendedABoxClause)]]()
      with mutable.MultiMap[(Individual, Role), (RoleAssertion, ExtendedABoxClause)]

  // map each definer to set of others so that their conjunction is unsatisfiable
  private var unsatisfiableDefinerMap: mutable.MultiMap[BaseConcept, Set[BaseConcept]] =
    new mutable.HashMap[BaseConcept, mutable.Set[Set[BaseConcept]]]()
    with mutable.MultiMap[BaseConcept, Set[BaseConcept]]

  private var rangeRestrictions: mutable.MultiMap[Role, BaseConcept] =
    new mutable.HashMap[Role, mutable.Set[BaseConcept]]()
    with mutable.MultiMap[Role, BaseConcept]


  private var unsatisfiableDefinerSets = Set[Set[BaseConcept]]()

  protected var ordering: Ordering[ConceptLiteral] = _

  private var definer2Role = Map[BaseConcept,Role]()
  private var role2definers = new mutable.HashMap[Role, mutable.Set[BaseConcept]] with mutable.MultiMap[Role,BaseConcept]
  private var existentialDefiners = Set[BaseConcept]()

  private var targetClause: Option[ExtendedABoxClause] = None


  def setLiteralOrdering(ordering: Ordering[ConceptLiteral]) = {
    this.ordering=ordering
    this.toProcessTBox = SortedSet()(new ShortFirstClauseOrdering(ordering))
  }

  def addTBoxClauses(tboxClauses: Set[ConceptClause]): Unit = {
    tboxClauses.map(_.withOrdering(ordering)).foreach { clause =>
      newClause(clause)
      clause.literals.foreach(_ match {
        case ConceptLiteral(_, ExistentialRoleRestriction(r,d: BaseConcept)) => existentialDefiners+=d
        case _ => ;
      })
    }
    if(!SET_OF_SUPPORT)
      tboxClauses.foreach(toTBoxFocus)
  }

  def addABox(abox: ABox) = {
    abox.assertions.foreach(_ match {
      case ConceptAssertion(concept: BaseConcept, individual) =>
        individual2concept.addBinding(individual, concept)
        individuals += (individual)
      case RoleAssertion(role, individual1, individual2) =>
        if(!individual2successor.contains(individual1))
          individual2successor.put(
            individual1,
            new mutable.HashMap[Role, mutable.Set[Individual]]()
              with mutable.MultiMap[Role,Individual]
          )
        individual2successor(individual1).addBinding(role,individual2)
        individuals += (individual1)
        individuals += (individual2)
    })
  }

  /**
   * TODO not sure whether actually needed
   */
  def addABoxClauses(aboxClauses: Set[ExtendedABoxClause]) = {
    aboxClauses.map(_.withOrdering(ordering)).foreach{clause =>
      newClause(clause)
      clause.literals.keys.foreach(ind => individuals += (ind))

      clause.literals.values.foreach(_.literals.foreach(_ match {
        case ConceptLiteral(_, ExistentialRoleRestriction(r, d: BaseConcept)) => existentialDefiners += d
        case _ => ;
      }))
    }
  }

  def setFocusSet(aboxClauses: Set[ExtendedABoxClause]) = {
    toProcess = SortedSet[ExtendedABoxClause]()(new ABoxClauseOrdering())
    val ordered = aboxClauses.map(_.withOrdering(ordering))
    ordered.foreach{x =>
      processAdditionalClausesIfNeeded(x);
      newClause(x)
      x.literals.keys.foreach(ind => individuals += (ind))

      x.literals.values.foreach(_.literals.foreach(_ match {
        case ConceptLiteral(_, ExistentialRoleRestriction(r, d: BaseConcept)) => existentialDefiners += d
        case _ => ;
      }))
    }
    toProcess ++= ordered
  }

  def setInferenceLogger(inferenceLogger: AbstractInferenceLogger) = {
    this.inferenceLogger=inferenceLogger
  }

  def getInferredABoxClauses() = {
    aboxClauses
  }

  def setTargetClause(target: ExtendedABoxClause) = {
    this.targetClause = Some(target)
  }


  /**
   * Perform reasoning and return whether it was possible to infer the empty clause or the target clause
   * @return
   */
  def reason(): Boolean = {

    //println("Existentially quantified definers: "+existentialDefiners)

    // TODO mechanism to deal with incoming role edges still missing (does not affect NO_ABOX mode)
    // TODO make sure existential roles come back into the queue after new inconsistent sets are found
    // TODO inferences on role restrictions with TBox clauses might be required
    var reachedTarget = false
    var count = 0

    inferenceLogger.sendInputClauses(aboxClauses)
    inferenceLogger.sendInputClauses(tbox)

    while ((!toProcess.isEmpty || !toProcessTBox.isEmpty) && !reachedTarget) {
      while (!toProcessTBox.isEmpty) {
        val next = toProcessTBox.head
        toProcessTBox -= next
     //   println()
     //   println("TBox clauses: " + toProcessTBox.size)
     //   println("process TBox " + next + " with head "+next.literals.head)
        if(!processedTBox(next)) {
          processedTBox += next
          tboxInferences(next)
       //     .map { x => println("derived " + x); x }
            .filterNot(tbox)
            .filter(acceptedTBoxClause)
            .filter(validTBox)
            .foreach { cl =>
              newClause(cl)
              processAdditionalClausesIfNeeded(cl)
              toProcessTBox += cl
            }
          aboxInferences(next)
        //    .map { x => println("derived: "+x); x}
            .filterNot(aboxClauses)
            .filter(acceptedABoxClause)
            .foreach{ cl =>
              newClause(cl)
              toProcess += cl
              processAdditionalClausesIfNeeded(cl)
              if(cl.isEmpty()||coversTarget(cl)){
                reachedTarget = true
              }
            }
        }
      }
      count += 1
      //if(count==50)
      //  System.exit(0)
      val next = toProcess.head
    //  println()
    //  println("process " + next + " with head "+selectLiteral(next))
      toProcess -= next
      //println("toProcess: " + toProcess.size + ", " + toProcess)
      //println("aboxClauses: " + aboxClauses.size + ", " + aboxClauses)
      inferences(next)//.map { x => println("derived " + x); x }
        .filterNot(aboxClauses)//{x => if(aboxClauses(x)) println("subsumed: "+x); aboxClauses(x)}
        .filter(acceptedABoxClause)//x => if(!acceptedABoxClause(x)) println("not accepted: "+x); acceptedABoxClause(x)}
        .foreach { cl =>
          newClause(cl)
          toProcess += cl

          processAdditionalClausesIfNeeded(cl)

          if (cl.isEmpty() || coversTarget(cl)) {
            reachedTarget = true
          }
        }
    }

 //   println()

    if(reachedTarget) {
      println("Inferred the empty clause or the target clause!")
      //System.exit(0);
    }

    reachedTarget
  }

  private def coversTarget(clause: ExtendedABoxClause) = {
    if(targetClause.isEmpty)
      false
    else {
      val result = clause.literals.forall(pair => {
        targetClause.get.literals.contains(pair._1) &&
          pair._2.literals.forall(targetClause.get.literals(pair._1).literals)
      })
      if(result) {
       // println("satisfied through "+clause)
      }
      result
    }
  }

  protected def validTBox(clause: ConceptClause): Boolean = {
    if(FORWARD_SUBSUMPTION && subsumed(clause)) {
   //   println(clause+" is subsumed!")
      false
    } else if(clause.literals.exists(l =>
      clause.literals.exists(l2 => l.polarity!=l2.polarity && l.concept.equals(l2.concept)))) {
    //  println(clause+" is a tautology!")
      false
    } // tautology
    else
      true
  }

  def subsumed(clause: ConceptClause): Boolean = {
    clause.literals
      .exists(l =>
        subsumes(literal2TBox.getOrElse(l,Set()),
          clause)
      )
    //tbox.exists(_.literals.forall(clause.literals))
  }

  def subsumes(clauses: Iterable[ConceptClause], clause: ConceptClause): Boolean = {
  //  println("Subsuming: "+clauses.filter(subsumes(_,clause)))
    clauses.exists(subsumes(_,clause))
  }

  def subsumes(clause1: ExtendedABoxClause, clause2: ExtendedABoxClause): Boolean = {
    !(clause1.equals(clause2)) &&
      clause1.literals.keys.forall(ind =>
        subsumes(
          clause1.literals(ind),
          clause2.literals.getOrElse(ind, new ConceptClause(Set()))))
  }

  def subsumes(clause1: ConceptClause, clause2: ExtendedABoxClause): Boolean = {
      clause2.literals.keys.exists(ind =>
        subsumes(
          clause1,
          clause2.literals(ind)))
  }

  def subsumes(clause1: ConceptClause, clause2: ConceptClause): Boolean = {
    !clause1.equals(clause2) && clause1.literals.forall(clause2.literals)
  }


  private def acceptedABoxClause(clause: ExtendedABoxClause) = {
    if(clause.literals.exists(entry => !validTBox(entry._2))) {
   //   println("not valid TBox")
      false
    } else if(NO_ABOX){
   //  println("Forward subsumption: "+FORWARD_SUBSUMPTION)
   //   println("TBox subsumed: "+ tbox.filter(subsumes(_,clause)))
   //   println("ABox subsumed: "+aboxClauses.filter(subsumes(_,clause)))
      (!FORWARD_SUBSUMPTION ||
        (!tbox.exists(subsumes(_,clause)) && !aboxClauses.exists(subsumes(_,clause)))
        ) &&
      // we don't want definers in ABox clauses
      clause.literals.keys.forall(ind => clause
        .literalsOf(ind)
        .map(_.concept)
        .filter(_.isInstanceOf[BaseConcept])
        .map(_.asInstanceOf[BaseConcept])
        .forall(c => !isDefiner(c))
      )
    } else
      true
  }

  private def tboxInferences(next: ConceptClause): Set[ConceptClause] = {
    val literal = next.literals.head
  //  println("selected literal: " + literal)
    literal match {
      case ConceptLiteral(false, b: BaseConcept) => resolveNegTBox(next, b)
      case ConceptLiteral(true, b: BaseConcept) => resolvePosTBox(next, b)
      case ConceptLiteral(true, urr: UniversalRoleRestriction) => universalRoleInferencesTBox(next, urr);
      case ConceptLiteral(true, err: ExistentialRoleRestriction) => existentialRoleInferencesTBox(next, err)
    }
  }

  private def acceptedTBoxClause(clause: ConceptClause): Boolean = {
    var definerRole: Option[Role] = None
    var existsDefiner = false

    // we filter out clauses that have negative definer literals with definers
    // - occurring under different roles
    // - or more than one existentially quantified definer
    clause.literals.forall(_ match {
      case ConceptLiteral(false, definer: BaseConcept) if isDefiner(definer) =>
        if(!definer2Role.contains(definer)) {
          // no role restriction with that definer has been inferred yet, so we assume we do not need this clause yet
          // false // <--- I am not sure this preserves completeness

          // we don't know yet whether we need this clause - better to keep it!
          true
        }
        else
        if(definerRole.isEmpty) {
          definerRole = Some(definer2Role(definer))
          true
        } else if (!definerRole.get.equals(definer2Role(definer)))
          false // only negative definers with the same role make sense
        else if(existentialDefiners(definer)){
          if(existsDefiner) // we want maximally one existentially quantified definer
            false
          else {
            existsDefiner=true
            true
          }
        } else {
          true
        }
      case _ => true
    })
  }

  private def resolveNegTBox(clause: ConceptClause, concept: BaseConcept) = {
    val litPos = new ConceptLiteral(true, concept)
    val litNeg = new ConceptLiteral(false, concept)
    literal2TBox.getOrElse(litPos, Set()).map { clause2 =>
      val resolvent = clause.without(litNeg)._with(clause2.without(litPos))

      inferenceLogger.sendInference(LiteralTBoxDerivation(Seq(clause, clause2), Seq(litNeg, litPos), resolvent))

      resolvent
    }.toSet
  }

  private def resolvePosTBox(clause: ConceptClause, concept: BaseConcept) = {
    val litPos = new ConceptLiteral(true, concept)
    val litNeg = new ConceptLiteral(false, concept)
    literal2TBox.getOrElse(litNeg, Set()).map { clause2 =>
      val resolvent = clause.without(litPos)._with(clause2.without(litNeg))

      inferenceLogger.sendInference(new LiteralTBoxDerivation(Seq(clause, clause2), Seq(litPos, litNeg), resolvent))

      resolvent

    }.toSet
  }


  private def existentialRoleInferencesTBox(clause: ConceptClause, existRestriction: ExistentialRoleRestriction) = {
    val literal = ConceptLiteral(true, existRestriction)
    val updatedClause = clause.without(literal)
    val d0 = existRestriction.filler.asInstanceOf[BaseConcept]
    (unsatisfiableDefinerSets
      ++unsatisfiableDefinerMap.getOrElse(d0, Set()))
      .flatMap { dis =>
        val partnerLiterals = dis.map(di => ConceptLiteral(true, UniversalRoleRestriction(existRestriction.role, di))).toList

        var premiseDefiners = dis
        if(unsatisfiableDefinerSets(dis))
          premiseDefiners+=d0
        val lastPremise = new ConceptClause(
          premiseDefiners.map(ConceptLiteral(false,_)))

        combineStepWise(updatedClause, partnerLiterals, List(clause)).map{ conclusionPremisesPair =>
          inferenceLogger.sendInference(
            new LiteralTBoxDerivation(
              (lastPremise::conclusionPremisesPair._2).reverse,
              partnerLiterals,
              conclusionPremisesPair._1)
          )
          conclusionPremisesPair._1
        }
      }.toSet
  }

  private def universalRoleInferencesTBox(clause: ConceptClause, univRestriction: UniversalRoleRestriction) = {

    // WARNING: we assume that we never create unsatisfiable definer sets with more than one existentially quantified variable

    val literal = ConceptLiteral(true, univRestriction)
    val updatedClause = clause.without(literal)
    val d0 = univRestriction.filler.asInstanceOf[BaseConcept]
    val role = univRestriction.role
    unsatisfiableDefinerMap.getOrElse(d0, Set())
      .flatMap { dis =>
        val partnerLiterals = dis.map(di =>
          ConceptLiteral(true,
            if(existentialDefiners(di))
              ExistentialRoleRestriction(role,di)
            else
              UniversalRoleRestriction(role,di)
          )
        ).toList

        var premiseDefiners = dis + (d0)

        val someExistential = dis.exists(existentialDefiners)

        if(someExistential) {
          val lastPremise = new ConceptClause(
            premiseDefiners.map(ConceptLiteral(false, _)))

          combineStepWise(updatedClause, partnerLiterals, List(clause)).map { conclusionPremisesPair =>
            inferenceLogger.sendInference(
              new LiteralTBoxDerivation(
                (lastPremise :: conclusionPremisesPair._2).reverse,
                partnerLiterals,
                conclusionPremisesPair._1)
            )
            conclusionPremisesPair._1
          }
        } else {
          // TODO here we now have to do the same for all existential restrictions over "role"
          Set[ConceptClause]()
        }
      }.toSet
  }

  private def aboxInferences(next: ConceptClause): Set[ExtendedABoxClause] = {
    val literal = next.literals.head
  //  println("selected literal: " + literal)
    literal match {
      case ConceptLiteral(false, b: BaseConcept) => resolveNegABox(next, b)
      case ConceptLiteral(true, b: BaseConcept) => resolvePosABox(next, b)
      case ConceptLiteral(true, urr: UniversalRoleRestriction) => universalRoleInferencesABox(next, urr);
      case ConceptLiteral(true, err: ExistentialRoleRestriction) => existentialRoleInferencesABox(next, err)
    }
  }


  private def resolveNegABox(next: ConceptClause, b: BaseConcept) = {
    val negLiteral = ConceptLiteral(false, b)
    val posLiteral = ConceptLiteral(true, b)
    individuals.flatMap(a =>
      literal2ABox.getOrElse((a, posLiteral), Set()).map { clause =>
        val resolvent = clause
          .replace(a, clause.literals(a)
            .without(posLiteral)
            ._with(next.without(negLiteral)))

        inferenceLogger.sendInference(
          LiteralMixedDerivation(Seq(clause), Seq(next), Seq(posLiteral), a, Seq(negLiteral), resolvent)
        )

        resolvent
      }
    ).toSet
  }

  private def resolvePosABox(next: ConceptClause, b: BaseConcept) = {
    val negLiteral = ConceptLiteral(false, b)
    val posLiteral = ConceptLiteral(true, b)
    individuals.flatMap(a =>
      literal2ABox.getOrElse((a, negLiteral), Set()).map { clause =>
        val resolvent = clause
          .replace(a, clause.literals(a)
            .without(negLiteral)
            ._with(next.without(posLiteral)))

        inferenceLogger.sendInference(
          LiteralMixedDerivation(Seq(clause), Seq(next), Seq(negLiteral), a, Seq(posLiteral), resolvent)
        )

        resolvent
      }
    ).toSet
  }

  private def existentialRoleInferencesABox(clause: ConceptClause, err: ExistentialRoleRestriction)
  : Set[ExtendedABoxClause] = {
    val literal = ConceptLiteral(true, err)
    val r = err.role
    val d0 = err.filler.asInstanceOf[BaseConcept]
    individuals.flatMap{individual =>
    val updatedClause = new ExtendedABoxClause(Map(individual-> clause.without(literal)))
    (unsatisfiableDefinerSets ++ unsatisfiableDefinerMap.getOrElse(d0, Set())).flatMap { dis =>
      var premiseDefiners = dis
      if (!unsatisfiableDefinerSets(dis))
        premiseDefiners += (d0)
      val lastpremise = new ConceptClause(premiseDefiners.map(d => ConceptLiteral(false, d)))
      val partnerLiterals = dis.map(di => ConceptLiteral(true, UniversalRoleRestriction(r, di))).toList

      // inferences are logged by the following method
      combineStepWise(updatedClause, individual, partnerLiterals, List(), List(literal), List(clause,lastpremise), List())
    }}.toSet
  }

  private def universalRoleInferencesABox(clause: ConceptClause, urr: UniversalRoleRestriction)
  : Set[ExtendedABoxClause] = {

    // WARNING: we assume that we never create unsatisfiable definer sets with more than one existentially quantified variable

    val literal = ConceptLiteral(true, urr)
    val r = urr.role
    val d0 = urr.filler.asInstanceOf[BaseConcept]
    individuals.flatMap { individual =>
      val updatedClause = new ExtendedABoxClause(Map(individual -> clause.without(literal)))
      unsatisfiableDefinerMap.getOrElse(d0, Set()).flatMap { dis =>
        var premiseDefiners = dis + (d0)
        val lastpremise = new ConceptClause(premiseDefiners.map(d => ConceptLiteral(false, d)))
        val partnerLiterals = dis.map(di => ConceptLiteral(true,
          if(existentialDefiners(di))
            ExistentialRoleRestriction(r,di)
          else
            UniversalRoleRestriction(r, di))).toList

        if(dis.exists(existentialDefiners)) {
          // inferences are logged by the following method
          combineStepWise(updatedClause, individual, partnerLiterals, List(), List(literal), List(clause, lastpremise), List())
        } else {
          // TODO now we need to do the same for all existentially quantified variables
          Set[ExtendedABoxClause]()
        }
      }
    }.toSet
  }


  private def inferences(next: ExtendedABoxClause): Set[ExtendedABoxClause] = {
    val literal = selectLiteral(next)
 //   println("selected literal: "+literal)
    literal match {
      case Some((a: Individual, ConceptLiteral(false, b: BaseConcept))) => resolveNeg(next, a, b)
      case Some((a: Individual, ConceptLiteral(true, b: BaseConcept))) => resolvePos(next, a, b)
      case Some((a: Individual, ConceptLiteral(true, Nominal(b)))) => nominalInferences(next, a, b)
      case Some((a: Individual, ConceptLiteral(true, UniversalRoleRestriction(r, d: BaseConcept)))) =>
        universalRoleInferences(next, a, r, d)
      case Some((a: Individual, ConceptLiteral(true, ExistentialRoleRestriction(r, d: BaseConcept)))) =>
        existentialRoleInferences(next, a, r, d)
      case None => selectRA(next) match {
        case Some(ra) => roleAssertionInferences(ra, next)
        case None => throw new AssertionError("Unexpected clause: " + next)
      }
      case other => throw new AssertionError("Unexpected case: " + other)
    }
  }

  private def resolveNeg(next: ExtendedABoxClause, a: Individual, b: BaseConcept) = {
      val negLiteral = ConceptLiteral(false, b)
      val posLiteral = ConceptLiteral(true, b)
      literal2TBox.getOrElse(posLiteral, Set()).map{ clause =>
        val resolvent = next.replace(a,
          next.literals(a)
            .without(negLiteral)
            ._with(clause
              .without(posLiteral))
        )
        inferenceLogger.sendInference(
          LiteralMixedDerivation(Seq(next), Seq(clause), Seq(negLiteral), a, Seq(posLiteral), resolvent))
          resolvent
      } ++
        literal2ABox.getOrElse((a, posLiteral), Set()).map { clause =>
          val resolvent = next.without(a, negLiteral)
            .combineWith(clause.without(a, posLiteral))

          inferenceLogger.sendInference(
            LiteralABoxDerivation(Seq(next,clause), Seq(negLiteral, posLiteral), a, resolvent)
          )

          resolvent
        }
    }.toSet


  private def resolvePos(next: ExtendedABoxClause, a: Individual, b: BaseConcept) = {
    val negLiteral = ConceptLiteral(false, b)
    val posLiteral = ConceptLiteral(true, b)
    literal2TBox.getOrElse(negLiteral, Set()).map { clause =>
      val resolvent = next.replace(a,
        next.literals(a)
          .without(posLiteral)
          ._with(clause
            .without(negLiteral))
      )

      inferenceLogger.sendInference(
        new LiteralMixedDerivation(Seq(next), Seq(clause), Seq(posLiteral), a, Seq(negLiteral), resolvent))

      resolvent
    } ++
      literal2ABox.getOrElse((a, negLiteral), Set()).map(clause => {
        val resolvent = next.without(a, posLiteral)
          .combineWith(clause.without(a, negLiteral))

        inferenceLogger.sendInference(
          new LiteralABoxDerivation(Seq(next, clause), Seq(posLiteral, negLiteral), a, resolvent)
        )

        resolvent
      })
  }.toSet

  private def nominalInferences(clause: ExtendedABoxClause, individual1: Individual, individual2: Individual) = {
    val literal = new ConceptLiteral(true, Nominal(individual2))
    var result = individual2concept.getOrElse(individual2, Set())
      .map(c => {
          clause.replace(individual1,
            clause.literals(individual1)
              .without(literal)
              ._with(new ConceptLiteral(true, c))
          )
      })
    if(individual2successor.contains(individual2)) {
      val mmap = individual2successor(individual2)
      result ++= mmap.keys.flatMap(role =>
        mmap(role).map { individual3 =>
          clause.without(individual1, literal)._with(RoleAssertion(role, individual1, individual3))
        }
      )
    }

    // we do not log the second premises here, since it is not relevant for the interpolant
    inferenceLogger.sendInference(
      result.map(newC =>
      new LiteralABoxDerivation(Seq(clause), Seq(literal), individual1, newC)))

    result.toSet
  }


  private def universalRoleInferences(clause: ExtendedABoxClause, individual: Individual, role: Role, d: BaseConcept)
  : Set[ExtendedABoxClause] = {
    val literal = ConceptLiteral(true, UniversalRoleRestriction(role, d))
    var result = Set[ExtendedABoxClause]()

    // first the inferences with the ABox
    if (individual2successor.contains(individual)) {
      result ++= individual2successor(individual).getOrElse(role, Set()).map { successor =>
        val resolvent = clause.without(individual, literal)
          ._with(successor, ConceptLiteral(true, d))

        inferenceLogger.sendInference(
          new RoleAssertionABoxDerivation(None, clause, RoleAssertion(role,individual,successor), literal, resolvent)
        )

        resolvent
      }
    }
    if (roleSuccessors.contains((individual, role))) {
      result ++= roleSuccessors((individual, role)).map(tuple => {
        val ra = tuple._1
        val clause2 = tuple._2
        var newClause = clause2.without(ra)

        // if the individual is introduced to the clause, we have to create a new clause to enforce the ordering
        if(newClause.literals.contains(ra.individual2))
          newClause = newClause._with(ra.individual2, ConceptLiteral(true, d))
        else
          newClause = newClause.replace(ra.individual2, new ConceptClause(Set(ConceptLiteral(true, d)), ordering))

        val resolvent = clause.without(individual, literal)
          .combineWith(newClause)

        inferenceLogger.sendInference(
          new RoleAssertionABoxDerivation(Some(clause2), clause, ra, literal, resolvent)
        )

        resolvent
      })
    }

    // Now the inferences with other role restrictions
    // WARNING: we assume that we never create unsatisfiable definer sets with more than one existentially quantified variable
    val updatedClause = clause.without(individual,literal)
    result ++= unsatisfiableDefinerMap.getOrElse(d, Set()).flatMap { dis =>
        var premiseDefiners = dis + (d)
        val lastpremise = new ConceptClause(premiseDefiners.map(d => ConceptLiteral(false, d)))
        val partnerLiterals = dis.map(di => ConceptLiteral(true,
          if (existentialDefiners(di))
            ExistentialRoleRestriction(role, di)
          else
            UniversalRoleRestriction(role, di))).toList

     //   println("Partner literals: "+partnerLiterals)

        if (dis.exists(existentialDefiners)) {
          // inferences are logged by the following method
          combineStepWise(updatedClause, individual, partnerLiterals, List(clause), List(literal), List(lastpremise), List())
        } else {
          // TODO now we need to do the same for all existentially quantified variables
          Set[ExtendedABoxClause]()
        }
      }

    result
  }

  private def existentialRoleInferences(clause: ExtendedABoxClause, individual: Individual, r: Role, d0: BaseConcept)
  : Set[ExtendedABoxClause] = {
    val literal = ConceptLiteral(true, ExistentialRoleRestriction(r, d0))
    val updatedClause = clause.without(individual, literal)
    (unsatisfiableDefinerSets ++ unsatisfiableDefinerMap.getOrElse(d0, Set())).flatMap { dis =>
      var premiseDefiners = dis
      if(!unsatisfiableDefinerSets(dis))
        premiseDefiners+=(d0)
      val lastpremise = new ConceptClause(premiseDefiners.map(d => ConceptLiteral(false, d)))
      val partnerLiterals = dis.map(di => ConceptLiteral(true, UniversalRoleRestriction(r, di))).toList

      // inferences are logged by the following method
      combineStepWise(updatedClause, individual, partnerLiterals, List(clause), List(literal), List(lastpremise), List())
    }.toSet
  }

  private def roleAssertionInferences(ra: RoleAssertion, next: ExtendedABoxClause): Set[ExtendedABoxClause] = {
    rangeRestrictions.getOrElse(ra.role, Set()).map(d => {

      var resolvent = next.without(ra)

      if(resolvent.literals.contains(ra.individual2))
        resolvent = resolvent._with(ra.individual2,
            ConceptLiteral(true, d))
      else
        resolvent = resolvent.replace(
          ra.individual2,
          new ConceptClause(Set(
            ConceptLiteral(true,d)), ordering)
        )

      inferenceLogger.sendInference(
        new RoleAssertionTBoxDerivation(
          next,
          None,
          ra,
          ConceptLiteral(true, UniversalRoleRestriction(ra.role,d)),
          resolvent)
      )

      resolvent
    }).toSet[ExtendedABoxClause]

    // I believe that nothing else is needed here:
    //  - role assertions are only introduced into clauses via the nominal inference, meaning the first element is always the root
    //  - the set-of-support strategy would mean that at least one input is from the focus set, which means
    //    an inference with a role assertion from the ABox (which cannot be in the focus) with just a TBox clause would never
    //    be possible (our pure TBox inferences focus on determining unsatisfiable definer sets)
    //  - assume we derive a clause C1 v r(a,b), with b the root individual. An inference with a TBox clause C2 v Ar.D
    //    would produce C1 or C2(a) v D(b). This clause can only lead to an empty clause if every literal in C2(a) is
    //    eliminated, meaning either 1) C2 can be eliminated via TBox reasoning alone, or 2) using at least one
    //    inference with an ABox clause with a literal L(a), where L could make an inference with C2. But in the latter
    //    case, we would first make that inference with L(a) to pull in C2 into the ABox clause, and then the inference
    //    with the role assertion, which means the inference between the ra assertion and the ABox clause would still
    //    not be needed. This leaves 1) as the interesting part. To deal with this, we just take the special case of
    //    unary TBox axioms (forall r.D) (range restrictions), and
    //    TODO have to make sure that the input already contains all such axioms that are entailed
  }

  private def combineStepWise(clause: ExtendedABoxClause,
                              individual: Individual,
                              literals: List[ConceptLiteral],
                              aboxPremises: List[ExtendedABoxClause],
                              aboxLiterals: List[ConceptLiteral],
                              tboxPremises: List[ConceptClause],
                              tboxLiterals: List[ConceptLiteral])
  : Set[ExtendedABoxClause] = literals match {
    case Nil =>
      inferenceLogger.sendInference(
        new LiteralMixedDerivation(
          aboxPremises,
          tboxPremises.reverse,
          aboxLiterals,
          individual,
          tboxLiterals.reverse,
          clause))

      Set(clause)

    case head :: rest =>
      (literal2TBox.getOrElse(head, Set()).flatMap { clause2 =>
        val newClause = clause.replace(individual,
          clause2.without(head)
            ._with(clause.literals.getOrElse(individual, new ConceptClause(Set(),ordering))))
        combineStepWise(
          newClause,
          individual,
          rest,
          aboxPremises,
          aboxLiterals,
          clause2::tboxPremises,
          head::tboxLiterals)
      } ++
        literal2ABox.getOrElse((individual, head), Set()).flatMap { aboxClause =>
          val newClause = aboxClause.without(individual, head).combineWith(clause)
          combineStepWise(
            newClause,
            individual,
            rest,
            aboxClause::aboxPremises,
            head::aboxLiterals,
            tboxPremises,
            tboxLiterals)
        }).toSet
  }

  private def combineStepWise(clause: ConceptClause,
                              literals: List[ConceptLiteral], premises: List[ConceptClause])
  : Set[(ConceptClause, List[ConceptClause])] = literals match {
    case Nil => Set((clause, premises))
    case head :: rest =>
      literal2TBox.getOrElse(head, Set()).flatMap { clause2 =>
        val newClause = clause2.without(head)._with(clause)
        combineStepWise(newClause, rest, clause2::premises)
      }.toSet
  }

  protected def selectLiteral(clause: ExtendedABoxClause): Option[(Individual, ConceptLiteral)] = {
    if(clause.literals.isEmpty)
      None
    else {
      val (ind, cclause) = clause.literals.head
      if(cclause.literals.isEmpty)
        None
      else
        Some((ind, cclause.literals.head))
    }
  }

  private def selectRA(clause: ExtendedABoxClause): Option[RoleAssertion] = {
    if(clause.roleAssertions.isEmpty)
      return None
    else
      Option(clause.roleAssertions.head)
  }


  protected def newClause(tboxClause: ConceptClause): Unit = {
  //  println("New Clause: " + tboxClause)

    if (!tbox(tboxClause) && validTBox(tboxClause)) {
      tbox += tboxClause
      if(SET_OF_SUPPORT) {
        tboxClause.literals.foreach(l => literal2TBox.addBinding(l, tboxClause))
      } else {
        literal2TBox.addBinding(tboxClause.literals.head, tboxClause) // Pure ordered resolution works again then
      }
      if (tboxClause.literals.forall(negDefinerLiteral)) {
        val definers = conceptsIn(tboxClause.literals)
        unsatisfiableDefinerSets += definers
        definers.foreach(d => unsatisfiableDefinerMap.addBinding(d, definers - d))
      }

      // TODO for this to work, we have to make sure all relevant range restrictions are
      // TODO check: is this todo already relevant for proving ALC concept inclusions?
      // <-- I think so!
      if(tboxClause.literals.size==1)
        tboxClause.literals.head match {
          case ConceptLiteral(true, UniversalRoleRestriction(r, d: BaseConcept)) =>
            rangeRestrictions.addBinding(r,d)
          case other => ; // nothing
        }



    } else {
  //    println("  -> ignored")
   //   if(tbox(tboxClause))
   //     println("     already had this clause")
    }

    if(BACKWARD_SUBSUMPTION){
      tboxClause.literals.foreach { l =>
        val subsumed = literal2TBox.getOrElse(l, Set())
          .filter(c => c!=tboxClause && subsumes(tboxClause, c))
        if(!subsumed.isEmpty){
     //     println("Subsumed clauses: "+subsumed)
          subsumed.foreach(sub => literal2TBox.removeBinding(l,sub))
          tbox = tbox -- subsumed
          toProcessTBox = toProcessTBox -- subsumed
        }
      }
    }
  }

  protected def newClause(aboxClause: ExtendedABoxClause) = {
   // println("New Clause: " + aboxClause)
   // if (!aboxClause.literals.isEmpty)
   //   println("           ordering: " + aboxClause.literals.head._2.ordering)
    if (!aboxClauses(aboxClause)) {
      aboxClauses += aboxClause
      aboxClause.literals.keys.foreach(ind =>
        aboxClause.literals(ind).literals.foreach(l =>
          literal2ABox.addBinding((ind, l), aboxClause)
        ))
      aboxClause.roleAssertions.foreach(ra =>
        roleSuccessors.addBinding((ra.individual1, ra.role), (ra, aboxClause))

      )
    }
  }


  protected def processAdditionalClausesIfNeeded(tboxClause: ConceptClause) : Unit = {
    //val maxLit = tboxClause.literals.head
    //processAdditionalClausesIfNeeded(maxLit)
    tboxClause.literals.foreach(processAdditionalClausesIfNeeded)
  }

  protected def processAdditionalClausesIfNeeded(aboxClause: ExtendedABoxClause): Unit = {
    /*
    selectLiteral(aboxClause) match {
      case Some((_, literal)) => processAdditionalClausesIfNeeded(literal)
      case None => ;
    }*/
    aboxClause.literals.foreach(_._2.literals.foreach(processAdditionalClausesIfNeeded))
  }

  protected def processAdditionalClausesIfNeeded(literal: ConceptLiteral): Unit = literal match {
    case ConceptLiteral(_, ExistentialRoleRestriction(r, concept: BaseConcept)) =>
      definer2Role += ((concept, r))
      //existentialDefiners += concept
      processAdditionalClausesIfNeeded(concept)


    case ConceptLiteral(_, UniversalRoleRestriction(r, concept: BaseConcept)) =>
      definer2Role += ((concept, r))
      processAdditionalClausesIfNeeded(concept)

    case _ => ;
  }

  /**
   * If the given filler concept occurs in a clause, check whether we need to add additional clauses to
   * the current support
   */
  protected def processAdditionalClausesIfNeeded(filler: BaseConcept): Unit = {
    // if we do not use set-of-support, then this lookup will fail to find our definer-clauses, since
    // we only index clauses by their maximal literal. However, without set-of-support strategy
    // there are all in focus anyway
    literal2TBox.get(new ConceptLiteral(false, filler)).foreach(_.foreach(toTBoxFocus))
  }

  protected def toTBoxFocus(clause: ConceptClause) = {
    if(!processedTBox(clause) && !toProcessTBox(clause)){//} && validTBox(clause)) {
      processAdditionalClausesIfNeeded(clause)
      toProcessTBox += clause
    }
  }

  private def conceptsIn(literals: Iterable[ConceptLiteral]) =
    literals.map(_ match {
      case ConceptLiteral(_, c: BaseConcept) => c
      case _ => throw new AssertionError("clause does not contain only negated definers: "+literals)
    }).toSet[BaseConcept]

  private def isDefiner(b: BaseConcept) = {
    b.name.startsWith("_D")
  }

  private def negDefinerLiteral(literal: ConceptLiteral) =
    literal match {
      case ConceptLiteral(false, b: BaseConcept) => isDefiner(b)
      case _ => false
    }

}
