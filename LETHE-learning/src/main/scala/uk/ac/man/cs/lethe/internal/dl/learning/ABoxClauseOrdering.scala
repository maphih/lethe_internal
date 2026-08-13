package uk.ac.man.cs.lethe.internal.dl.learning

import uk.ac.man.cs.lethe.internal.dl.datatypes.extended.ExtendedABoxClause

class ABoxClauseOrdering extends Ordering[ExtendedABoxClause] {
  override def compare(x: ExtendedABoxClause, y: ExtendedABoxClause): Int = {
    if(x.size!=y.size)
      x.size - y.size
    else {
      // TODO this can be done better!
      x.toString.compareTo(y.toString)
    }
  }
}
