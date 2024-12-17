package lisa.maths.settheory.orderings

import lisa.automation.settheory.SetTheoryTactics.WhitmanTactic
import lisa.fol.FOL.*

object Whitman extends lisa.Main {
  val x = variable
  val u = variable
  val test: Formula = And(x, u)
  // val axioms = Set(AnnotatedFormula(⊥, NoneAnnotation), AnnotatedFormula(x ∧ (¬(x) ∨ u), RightAnnotation))
}
