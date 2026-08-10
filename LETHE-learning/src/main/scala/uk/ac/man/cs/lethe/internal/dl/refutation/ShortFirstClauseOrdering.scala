package uk.ac.man.cs.lethe.internal.dl.refutation

import uk.ac.man.cs.lethe.internal.dl.forgetting.direct.{ConceptClause, ConceptClauseOrdering, ConceptLiteral}

class ShortFirstClauseOrdering(literalOrdering: Ordering[ConceptLiteral])
  extends ConceptClauseOrdering(literalOrdering)
{
  override def compare(clause1: ConceptClause, clause2: ConceptClause): Int = {
    if(clause1.size!=clause2.size)
      clause1.size-clause2.size
    else
      super.compare(clause1, clause2)
  }
}
