package lisa.automation

import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.utils.memoization.memoized

class ExtendedWhitman(axioms: Set[(AnnotatedFormula, AnnotatedFormula)]) {
  val memoizedProve: ((AnnotatedFormula, AnnotatedFormula)) => Boolean = memoized[(AnnotatedFormula, AnnotatedFormula), Boolean] { case (gamma, delta) =>
    val axiomsFormulas = axioms flatMap { case (a, b) => Set(a.formula, b.formula) }

    // ==== Common cases ====
    val hyp = gamma._2 != NoneAnnotation && delta._2 != NoneAnnotation && gamma._1 == delta._1
    val ax = axioms.contains((gamma, delta))
    val weaken = gamma._2 != NoneAnnotation && delta._2 != NoneAnnotation &&
      (memoizedProve(gamma, AnnotatedFormula(delta._1, NoneAnnotation)) || memoizedProve(AnnotatedFormula(gamma._1, NoneAnnotation), delta))

    // ==== Gamma cases ====
    val leftNot = gamma match
      case AnnotatedFormula(¬(phi), annot) => memoizedProve(AnnotatedFormula(phi, annot), delta)
      case _ => false
    val leftAnd = gamma match
      case AnnotatedFormula(phi ∧ psi, annot) => memoizedProve(AnnotatedFormula(phi, annot), delta) || memoizedProve(AnnotatedFormula(psi, annot), delta)
      case _ => false
    val leftOr = gamma match
      case AnnotatedFormula(phi ∨ psi, annot) => memoizedProve(AnnotatedFormula(phi, annot), delta) && memoizedProve(AnnotatedFormula(psi, annot), delta)
      case _ => false

    // ==== Delta cases =====
    val rightNot = delta match
      case AnnotatedFormula(¬(phi), annot) => memoizedProve(gamma, AnnotatedFormula(phi, annot))
      case _ => false
    val rightAnd = delta match
      case AnnotatedFormula(phi ∧ psi, annot) => memoizedProve(gamma, AnnotatedFormula(phi, annot)) || memoizedProve(gamma, AnnotatedFormula(psi, annot))
      case _ => false
    val rightOr = delta match
      case AnnotatedFormula(phi ∨ psi, annot) => memoizedProve(gamma, AnnotatedFormula(phi, annot)) && memoizedProve(gamma, AnnotatedFormula(psi, annot))
      case _ => false
    val cut = axiomsFormulas.exists(x => {
      val p1 = memoizedProve(gamma, AnnotatedFormula(x, RightAnnotation))
      val p2 = memoizedProve(AnnotatedFormula(x, LeftAnnotation), delta)
      val p3 = memoizedProve(delta, AnnotatedFormula(x, RightAnnotation))
      val p4 = memoizedProve(AnnotatedFormula(x, LeftAnnotation), gamma)

      (p1 && p2) || (p3 && p4)
    })

    val success = hyp || ax || weaken ||
      leftNot || leftAnd || leftOr ||
      rightNot || rightAnd || rightOr ||
      cut

    success
  }

  def prove(gamma: AnnotatedFormula, delta: AnnotatedFormula): Boolean = {
    memoizedProve((gamma, delta))
  }
}
