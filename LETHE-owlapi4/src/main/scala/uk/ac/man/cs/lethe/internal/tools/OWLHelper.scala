package uk.ac.man.cs.lethe.internal.tools

import org.semanticweb.owlapi.model.{OWLAxiom, OWLEntity, OWLLogicalAxiom, OWLOntology, OWLOntologyManager}
import scala.collection.JavaConverters._

// helper object to assure owl4 <-> owl5 compatibility 
// (avoiding methods with different signatures in owl4 and owl5)
object OWLHelper {

    def addAxioms(ontology: OWLOntology, axioms: java.util.Set[_ <: OWLAxiom], manager: OWLOntologyManager) = {
        axioms.asScala.foreach(axiom => manager.addAxiom(ontology, axiom))
        
    }

    def removeAxioms(ontology: OWLOntology, axioms: java.util.Set[_ <: OWLAxiom], manager: OWLOntologyManager) = {
        axioms.asScala.foreach(axiom => manager.removeAxiom(ontology, axiom))
    }
}
