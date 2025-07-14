package uk.ac.man.cs.lethe.internal.dl.abduction

import uk.ac.man.cs.lethe.internal.dl.datatypes.extended.{ConjunctiveAssertion, ConjunctiveDLStatement, DisjunctiveAssertion, DisjunctiveDLStatement, NegatedRoleAssertion}
import uk.ac.man.cs.lethe.internal.dl.datatypes.{Assertion, BaseConcept, BaseRole, BottomConcept, CheapSimplifier, Concept, ConceptAssertion, ConceptComplement, ConceptConjunction, ConceptDisjunction, DLHelpers, DLStatement, ExistentialRoleRestriction, Individual, Ontology, OntologyBeautifier, RoleAssertion, Subsumption, TopConcept, TopRole, UniversalRoleRestriction}
import uk.ac.man.cs.lethe.internal.tools.formatting.SimpleDLFormatter


object Test {
  def main(args: Array[String]): Unit = {
    val ontology = new Ontology()
    ontology.addStatement(
      ConceptAssertion(
        ConceptConjunction(Set(
          ExistentialRoleRestriction(BaseRole("r"),
            ConceptConjunction(Set(
              BaseConcept("A"),
              UniversalRoleRestriction(BaseRole("s"),
                ConceptConjunction(Set(
                  BaseConcept("C"),
                  ConceptDisjunction(Set(
                    ExistentialRoleRestriction(TopRole, BaseConcept("B")),
                    BaseConcept("F")
                  ))
                ))
            )))
        ),
          UniversalRoleRestriction(BaseRole("r"),
            ConceptConjunction(Set(
              BaseConcept("B"),
              ExistentialRoleRestriction(TopRole,
                ConceptDisjunction(Set(
                  BaseConcept("G"),
                  ExistentialRoleRestriction(TopRole, BaseConcept("F"))
                ))
              )
            ))
          ),
          ExistentialRoleRestriction(TopRole,BaseConcept("G"))
        )),
        Individual("a")
      )
    )

    System.out.println(SimpleDLFormatter.format(ontology))

    DeNegator.denegate(ontology)

    System.out.println(OntologyBeautifier.nice(ConceptAssertion(UniversalRoleRestriction(BaseRole("r"),TopConcept), Individual("a"))))
  }
}

/**
 * Last step in the abduction process: take the denormalized forgetting result as input, negate it again.
 */
object DeNegator {
  def denegate(ontology: Ontology): DLStatement = {
    // assumption: tbox is empty, every axiom is either an assertion or a disjunctive assertion
    // all concepts are in CNF
    // universal roles occur only under existential restrictions
    assert(ontology.tbox.isEmpty)

    val conjuncts = ontology.abox.assertions
      .map { x => val r = negateIntoNNF(x); println(SimpleDLFormatter.format(r)); r }
      .map { x => val r = pullOutUniversalRoles(x); println(SimpleDLFormatter.format(r)); r }
      .map { x => val r = splitAndSimplifyAssertions(x); println(SimpleDLFormatter.format(r)); r }
    val asOne = ConjunctiveDLStatement(conjuncts)
    val dnf = toDNF(asOne)
    println(SimpleDLFormatter.format(dnf))
    val nonRedundant = redundancyRemove(dnf)
    println(SimpleDLFormatter.format(nonRedundant))
    nonRedundant
  }

  def redundancyRemove(st: DLStatement) = st match {
    case DisjunctiveDLStatement(ds) => {
      val nonRedundant = ds.filterNot(disjunct1 =>
        ds.filterNot(_.equals(disjunct1)).exists(contains(disjunct1,_)
      ))
      DisjunctiveDLStatement(nonRedundant)
    }
    case other => other
  }

  def contains(s1: DLStatement, s2: DLStatement) = (s1,s2) match {
    case (a,b) if a.equals(b) => true
    case (ConjunctiveDLStatement(c1), ConjunctiveDLStatement(c2)) => c2.forall(c1)
    case (ConjunctiveDLStatement(c1), other) => c1.contains(other)
    case _ => false
  }

  def toDNF(statement: DLStatement): DLStatement = statement match {
    case r: RoleAssertion => r
    case c: ConceptAssertion => c
    case s: Subsumption => s
    case ConjunctiveDLStatement(conjuncts) =>
      val flat = conjuncts.map(toDNF).flatMap(flatConjuncts).filterNot(tautology)
      if(flat.exists(contradiction))
        Subsumption(TopConcept,BottomConcept)
      else if(flat.exists(_.isInstanceOf[DisjunctiveDLStatement])) {
        val disjunction = flat.find(_.isInstanceOf[DisjunctiveDLStatement])
          .map(_.asInstanceOf[DisjunctiveDLStatement])
          .get
        val others = flat - disjunction
       toDNF(DisjunctiveDLStatement(
         disjunction.statements.map(disjunct =>
           ConjunctiveDLStatement(others + disjunct)
       )))
      } else {
        ConjunctiveDLStatement(flat)
      }
    case DisjunctiveDLStatement(disjuncts) =>
      val normalized = disjuncts
        .map(toDNF)
        .flatMap(flatDisjuncts)
        .filterNot(contradiction)

      if(disjuncts.exists(tautology))
        Subsumption(TopConcept,TopConcept)

      DisjunctiveDLStatement(normalized)
  }

  def flatConjuncts(statement: DLStatement): Set[DLStatement] = statement match {
    case ConjunctiveDLStatement(cs) => cs.flatMap(flatConjuncts)
    case other => Set(other)
  }

  def flatDisjuncts(statement: DLStatement): Set[DLStatement] = statement match {
    case DisjunctiveDLStatement(cs) => cs.flatMap(flatDisjuncts)
    case other => Set(other)
  }

  def tautology(statement: DLStatement) = statement match {
    case Subsumption(_, TopConcept) => true
    case ConceptAssertion(TopConcept,_) => true
    case _ => false
  }

  def contradiction(statement: DLStatement) = statement match {
    case Subsumption(TopConcept, BottomConcept) => true
    case ConceptAssertion(BottomConcept,_) => true
    case _ => false
  }

  def splitAndSimplifyAssertions(assertion: Assertion): DLStatement = assertion match {
    case r: RoleAssertion => r
    case ConjunctiveAssertion(conjuncts) => ConjunctiveDLStatement(conjuncts.map(splitAndSimplifyAssertions))
    case ConceptAssertion(ConceptConjunction(cs), individual) =>
      ConjunctiveDLStatement(cs.map(ConceptAssertion(_, individual)).map(splitAndSimplifyAssertions))
    case ConceptAssertion(ConceptDisjunction(ds), individual) =>
      DisjunctiveDLStatement(ds.map(ConceptAssertion(_, individual)).map(splitAndSimplifyAssertions))
    case ConceptAssertion(UniversalRoleRestriction(TopRole, c), individual) =>
       OntologyBeautifier.nice(Subsumption(TopConcept, c))
    case otherAssertion: ConceptAssertion => OntologyBeautifier.nice(otherAssertion)
    case other => assert(false); other
  }

  def pullOutUniversalRoles(assertion: Assertion): Assertion = assertion match {
    case r: RoleAssertion => r
    case ConjunctiveAssertion(conjuncts) => ConjunctiveAssertion(conjuncts.map(pullOutUniversalRoles))
    case ConceptAssertion(concept, individual) => ConceptAssertion(pullOutUniversalRoles(concept), individual)
    case other => assert(false); other
  }

  var id = 0

  def pullOutUniversalRoles(concept: Concept): Concept = {
    val myId = id
    id += 1
    println(" ".repeat(id) + " In: " + SimpleDLFormatter.format(concept))
    val result = concept match {
      case a: BaseConcept => a

      case ConceptComplement(a: BaseConcept) => ConceptComplement(a)

      case ConceptConjunction(cs) => DLHelpers.conjunction(cs.map(pullOutUniversalRoles))

      case ConceptDisjunction(cs) => DLHelpers.disjunction(cs.map(pullOutUniversalRoles))

      case ExistentialRoleRestriction(r, ConceptDisjunction(ds)) =>
        ConceptDisjunction(ds.map(ExistentialRoleRestriction(r, _)).map(pullOutUniversalRoles))

      case UniversalRoleRestriction(r, filler) =>
        val broken = breakUniversalFiller(pullOutUniversalRoles(filler))
        val fillerConjuncts = broken match {
          case ConceptConjunction(cs) => cs
          case other => Set(other)
        }
        val conjuncts = fillerConjuncts.map{fillerConjunct =>
          val disjuncts = fillerConjunct match {
            case ConceptDisjunction(cs) => cs;
            case other => Set(other)
          }
          val (univ, other) = disjuncts.partition { case UniversalRoleRestriction(TopRole, _) => true; case _ => false }
          if (univ.isEmpty)
            UniversalRoleRestriction(r, DLHelpers.disjunction(disjuncts))
          else
            DLHelpers.disjunction(
              univ.map(underUniversal).map(UniversalRoleRestriction(TopRole, _))
                ++ Set(UniversalRoleRestriction(r, DLHelpers.disjunction(other)))
            )
        }
        DLHelpers.conjunction(conjuncts)

      case ExistentialRoleRestriction(r, filler) =>
        val broken = breakExistentialFiller(pullOutUniversalRoles(filler))
        val fillerDisjuncts = broken match {
          case ConceptDisjunction(cs) => cs
          case other => Set(other)
        }
        val disjuncts = fillerDisjuncts.map{fillerDisjunct =>
          val conjuncts = fillerDisjunct match {
            case ConceptConjunction(cs) => cs;
            case other => Set(other)
          }
          val (univ, other) = conjuncts.partition { case UniversalRoleRestriction(TopRole, _) => true; case _ => false }
          if (univ.isEmpty)
            ExistentialRoleRestriction(r, DLHelpers.conjunction(conjuncts))
          else
            DLHelpers.conjunction(
              univ.map(underUniversal).map(UniversalRoleRestriction(TopRole, _))
                ++ Set(UniversalRoleRestriction(r, DLHelpers.conjunction(other)))
            )
        }
        DLHelpers.disjunction(disjuncts)

      /*
    case UniversalRoleRestriction(r, ConceptConjunction(cs)) =>
      ConceptConjunction(cs.map(UniversalRoleRestriction(r, _)).map(pullOutUniversalRoles))

    /*case ExistentialRoleRestriction(r, ConceptConjunction(cs)) if cs.exists(_.isInstanceOf[ConceptDisjunction]) =>
      val disjunction =
        cs.find(_.isInstanceOf[ConceptDisjunction])
          .map(_.asInstanceOf[ConceptDisjunction])
          .get
      DLHelpers.disjunction(
        disjunction.disjuncts
          .map(d => ExistentialRoleRestriction(r, ConceptConjunction(Set(d)++cs)))
      .map(pullOutUniversalRoles))

    case UniversalRoleRestriction(r, ConceptDisjunction(ds)) if ds.exists(_.isInstanceOf[ConceptConjunction]) =>
      val conjunction =
        ds.find(_.isInstanceOf[ConceptConjunction])
          .map(_.asInstanceOf[ConceptConjunction])
          .get
          println(" ".repeat(myId)+" conjunction: "+SimpleDLFormatter.format(conjunction))
      DLHelpers.conjunction(
        conjunction.conjuncts
          .map(c => UniversalRoleRestriction(r, ConceptDisjunction(Set(c)++ds)))
          .map(pullOutUniversalRoles))
    */
    case ExistentialRoleRestriction(r, c) =>
      assert(!r.equals(TopRole))
      val inner = pullOutUniversalRoles(c)
      val conjuncts = inner match {
        case ConceptConjunction(cs) => cs;
        case other => Set(other)
      }
      val (univ, other) = conjuncts.partition { case UniversalRoleRestriction(TopRole, _) => true; case _ => false }
      if (univ.isEmpty)
        ExistentialRoleRestriction(r, DLHelpers.conjunction(conjuncts))
      else
        DLHelpers.conjunction(Set(
          ExistentialRoleRestriction(r, DLHelpers.conjunction(other)),
          UniversalRoleRestriction(TopRole, DLHelpers.conjunction(univ.map(underUniversal)))))

    case UniversalRoleRestriction(r, c) =>
      val inner = pullOutUniversalRoles(c)
      // TODO here we have to do a transformation into CNF!
      val disjuncts = inner match {
        case ConceptDisjunction(cs) => cs;
        case other => Set(other)
      }
      val (univ, other) = disjuncts.partition { case UniversalRoleRestriction(TopRole, _) => true; case _ => false }
      if (univ.isEmpty)
        UniversalRoleRestriction(r, DLHelpers.disjunction(disjuncts))
      else
        DLHelpers.disjunction(
          univ.map(underUniversal).map(UniversalRoleRestriction(TopRole, _))
            ++ Set(UniversalRoleRestriction(r, DLHelpers.disjunction(other)))
        )

       */
    }
    println(" ".repeat(myId) + " Out: " + SimpleDLFormatter.format(result))
    result
  }


  /**
   * concepts under a universal role restriction need to be normalized into a conjunction of disjunctions of atoms
   * for the pulling of the universal role to work */
  def breakUniversalFiller(filler: Concept): Concept = filler match {
    case ds: ConceptDisjunction =>
      val flattened = flatten(ds)
      if (flattened.disjuncts.exists(_.isInstanceOf[ConceptConjunction])) {
        val conjunction = flattened.disjuncts.find(_.isInstanceOf[ConceptConjunction] )
          .map (_.asInstanceOf[ConceptConjunction] )
          .get
        val rest = flattened.disjuncts - conjunction
        breakUniversalFiller(ConceptConjunction (conjunction.conjuncts.map (c =>
          ConceptDisjunction (rest + c) ) )
        )
      } else
        flattened
    case cs: ConceptConjunction =>
      val flattened = flatten(cs)
      val brokenConjuncts = flattened.conjuncts.map(breakUniversalFiller)
      flatten(ConceptConjunction(brokenConjuncts))
    case other => other
  }

  /**
   * concepts under an existential role restriction need to be normalized into a disjunction of conjunctions of atoms
   * for the pulling of the universal role to work */
  def breakExistentialFiller(filler: Concept): Concept = filler match {
    case ds: ConceptConjunction =>
      val flattened = flatten(ds)
      if (flattened.conjuncts.exists(_.isInstanceOf[ConceptDisjunction])) {
        val disjunction = flattened.conjuncts.find(_.isInstanceOf[ConceptDisjunction] )
          .map (_.asInstanceOf[ConceptDisjunction] )
          .get
        val rest = flattened.conjuncts - disjunction
        breakExistentialFiller(ConceptDisjunction (disjunction.disjuncts.map (c =>
          ConceptConjunction (rest + c) ) )
        )
      } else
        flattened
    case cs: ConceptDisjunction =>
      val flattened = flatten(cs)
      val brokenConjuncts = flattened.disjuncts.map(breakExistentialFiller)
      flatten(ConceptDisjunction(brokenConjuncts))
    case other => other
  }

  def flatten(concept: ConceptConjunction): ConceptConjunction = {
    if (concept.conjuncts.exists(_.isInstanceOf[ConceptConjunction]))
      flatten(
        ConceptConjunction(
          concept.conjuncts.flatMap(_ match {
            case ConceptConjunction(cs) => cs
            case other => Set(other)
          })))
    else
      concept
  }

  def flatten(concept: ConceptDisjunction): ConceptDisjunction = {
    if (concept.disjuncts.exists(_.isInstanceOf[ConceptDisjunction]))
      flatten(
        ConceptDisjunction(
          concept.disjuncts.flatMap(_ match {
            case ConceptDisjunction(cs) => cs
            case other => Set(other)
          })))
    else
      concept
  }


  def underUniversal(concept: Concept): Concept = concept match {
    case UniversalRoleRestriction(TopRole, filler) =>
      filler match {
        case urr: UniversalRoleRestriction if urr.role.equals(TopRole) => underUniversal(urr)
        case other => other
    }
    case other => assert(false); other
  }

  /**
   * case:
   *
   * existential restriction (r,c)
   *  -> if c is a disjunction, split the disjunction, process each disjunct
   *  -> if c is a conjunction, pull out
   *
   * */

  def negateIntoNNF(assertion: Assertion): Assertion = assertion match {
    case NegatedRoleAssertion(role, individual1, individual2) => RoleAssertion(role, individual1, individual2)
    case ConceptAssertion(concept, individual) => ConceptAssertion(negateIntoNNF(concept), individual)
    case DisjunctiveAssertion(disjuncts) => ConjunctiveAssertion(disjuncts.map(negateIntoNNF))
  }

  def negateIntoNNF(concept: Concept): Concept = concept match {
    case a: BaseConcept => ConceptComplement(a);
    case ConceptComplement(a: BaseConcept) => a;
    case ExistentialRoleRestriction(r,c) => UniversalRoleRestriction(r,negateIntoNNF(c))
    case UniversalRoleRestriction(r,c) => ExistentialRoleRestriction(r,negateIntoNNF(c))
    case ConceptConjunction(conjuncts) => ConceptDisjunction(conjuncts.map(negateIntoNNF))
    case ConceptDisjunction(disjuncts) => ConceptConjunction(disjuncts.map(negateIntoNNF))
    case _ => assert(false); concept;
  }
}
