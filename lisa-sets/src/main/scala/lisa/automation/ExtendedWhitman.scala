package lisa.automation

import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.utils.memoization.memoized

class ExtendedWhitman(axioms: Set[(AnnotatedFormula, AnnotatedFormula)]) {
  val axiomsFormulas = axioms flatMap { case (a, b) => Set(a.formula, b.formula) }
  var proven: Set[(AnnotatedFormula, AnnotatedFormula)] = Set()
  var visited: Set[(AnnotatedFormula, AnnotatedFormula)] = Set()

  def prove(gamma: AnnotatedFormula, delta: AnnotatedFormula): Boolean = {
    if proven.contains((gamma, delta)) then return true
    else if visited.contains((gamma, delta)) then return false
    else
      visited += ((gamma, delta))
      // ==== Common cases ====
      val hyp = gamma._2 != NoneAnnotation && delta._2 != NoneAnnotation &&
        gamma._1 == delta._1 && gamma._2 != delta._2
      val ax = axioms.contains((gamma, delta))
      val weaken = gamma._2 != NoneAnnotation && delta._2 != NoneAnnotation &&
        (prove(gamma, AnnotatedFormula(delta._1, NoneAnnotation)) || prove(AnnotatedFormula(gamma._1, NoneAnnotation), delta))

      // ==== Gamma cases ====
      val leftNot = gamma match
        case AnnotatedFormula(¬(phi), annot) => prove(AnnotatedFormula(phi, annot), delta)
        case _ => false
      val leftAnd = gamma match
        case AnnotatedFormula(phi ∧ psi, annot) => prove(AnnotatedFormula(phi, annot), delta) || prove(AnnotatedFormula(psi, annot), delta)
        case _ => false
      val leftOr = gamma match
        case AnnotatedFormula(phi ∨ psi, annot) => prove(AnnotatedFormula(phi, annot), delta) && prove(AnnotatedFormula(psi, annot), delta)
        case _ => false

      // ==== Delta cases =====
      val rightNot = delta match
        case AnnotatedFormula(¬(phi), annot) => prove(gamma, AnnotatedFormula(phi, annot))
        case _ => false
      val rightAnd = delta match
        case AnnotatedFormula(phi ∧ psi, annot) => prove(gamma, AnnotatedFormula(phi, annot)) || prove(gamma, AnnotatedFormula(psi, annot))
        case _ => false
      val rightOr = delta match
        case AnnotatedFormula(phi ∨ psi, annot) => prove(gamma, AnnotatedFormula(phi, annot)) && prove(gamma, AnnotatedFormula(psi, annot))
        case _ => false
      val cut = axiomsFormulas.exists(x => {
        val p1 = prove(gamma, AnnotatedFormula(x, RightAnnotation))
        val p2 = prove(AnnotatedFormula(x, LeftAnnotation), delta)
        val p3 = prove(delta, AnnotatedFormula(x, RightAnnotation))
        val p4 = prove(AnnotatedFormula(x, LeftAnnotation), gamma)

        (p1 && p2) || (p3 && p4)
      })

      val success = hyp || ax || weaken ||
        leftNot || leftAnd || leftOr ||
        rightNot || rightAnd || rightOr ||
        cut

      if success then proven += ((gamma, delta))
      success
  }

  def isAtomic(formula: Formula): Boolean = formula match {
    case phi ∧ psi => false
    case phi ∨ psi => false
    case ¬(phi) => false
    case _ => true
  }
}
