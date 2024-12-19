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
    val bottom = AnnotatedFormula(⊥, NoneAnnotation)
    if proven.contains((gamma, delta)) then return true
    else if visited.contains((gamma, delta)) then return false
    else
      visited += ((gamma, delta))
      // ==== Common cases ====
      val hyp = gamma._2 != NoneAnnotation && delta._2 != NoneAnnotation &&
        gamma._1 == delta._1 && gamma._2 != delta._2
      val ax = axioms.contains((gamma, delta)) || axioms.contains((delta, gamma))
      val weaken = gamma._2 != NoneAnnotation && delta._2 != NoneAnnotation &&
        (prove(gamma, bottom) || prove(bottom, delta))

      // ==== Gamma cases ====
      val leftNot = gamma match
        case AnnotatedFormula(¬(phi), LeftAnnotation) => prove(AnnotatedFormula(phi, RightAnnotation), delta)
        case _ => false
      val leftAnd = gamma match
        case AnnotatedFormula(phi ∧ psi, LeftAnnotation) =>
          prove(AnnotatedFormula(phi, LeftAnnotation), delta) || prove(AnnotatedFormula(psi, LeftAnnotation), delta)
        case _ => false
      val leftOr = gamma match
        case AnnotatedFormula(phi ∨ psi, LeftAnnotation) =>
          prove(AnnotatedFormula(phi, LeftAnnotation), delta) && prove(AnnotatedFormula(psi, LeftAnnotation), delta)
        case _ => false

      val rightNot = gamma match
        case AnnotatedFormula(¬(phi), RightAnnotation) => prove(AnnotatedFormula(phi, LeftAnnotation), delta)
        case _ => false
      val rightAnd = gamma match
        case AnnotatedFormula(phi ∧ psi, RightAnnotation) =>
          prove(AnnotatedFormula(phi, RightAnnotation), delta) && prove(AnnotatedFormula(psi, RightAnnotation), delta)
        case _ => false
      val rightOr = gamma match
        case AnnotatedFormula(phi ∨ psi, RightAnnotation) =>
          prove(AnnotatedFormula(phi, RightAnnotation), delta) || prove(AnnotatedFormula(psi, RightAnnotation), delta)
        case _ => false

      // ==== Delta cases ====
      val leftNotb = delta match
        case AnnotatedFormula(¬(phi), LeftAnnotation) => prove(gamma, AnnotatedFormula(phi, RightAnnotation))
        case _ => false
      val leftAndb = delta match
        case AnnotatedFormula(phi ∧ psi, LeftAnnotation) =>
          prove(gamma, AnnotatedFormula(phi, LeftAnnotation)) || prove(gamma, AnnotatedFormula(psi, LeftAnnotation))
        case _ => false
      val leftOrb = delta match
        case AnnotatedFormula(phi ∨ psi, LeftAnnotation) =>
          prove(gamma, AnnotatedFormula(phi, LeftAnnotation)) && prove(gamma, AnnotatedFormula(psi, LeftAnnotation))
        case _ => false

      val rightNotb = delta match
        case AnnotatedFormula(¬(phi), RightAnnotation) => prove(gamma, AnnotatedFormula(phi, LeftAnnotation))
        case _ => false
      val rightAndb = delta match
        case AnnotatedFormula(phi ∧ psi, RightAnnotation) =>
          prove(gamma, AnnotatedFormula(phi, RightAnnotation)) && prove(gamma, AnnotatedFormula(psi, RightAnnotation))
        case _ => false
      val rightOrb = delta match
        case AnnotatedFormula(phi ∨ psi, RightAnnotation) =>
          prove(gamma, AnnotatedFormula(phi, RightAnnotation)) || prove(gamma, AnnotatedFormula(psi, RightAnnotation))
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
        cut || leftNotb || leftAndb || leftOrb ||
        rightNotb || rightAndb || rightOrb

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
