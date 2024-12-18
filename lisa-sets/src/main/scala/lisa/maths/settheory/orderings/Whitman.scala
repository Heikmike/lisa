package lisa.maths.settheory.orderings

import lisa.automation.ExtendedWhitman
import lisa.fol.FOL.*

object Whitman extends lisa.Main {
  val x = VariableFormula("x")
  val u = VariableFormula("u")
  val left = x ∧ (¬(x) ∨ u)
  val right = ¬(x) ∨ u
  val bottom = AnnotatedFormula(⊥, NoneAnnotation)

  val axiom = (bottom, AnnotatedFormula(left, RightAnnotation))
  val axiomSet: Set[(AnnotatedFormula, AnnotatedFormula)] = Set(axiom)
  val gamma = bottom
  val delta = AnnotatedFormula(u, RightAnnotation)

  // val x = VariableFormula("x")
  // val y = VariableFormula("y")
  // val z = VariableFormula("z")

  // val axiom1 = (AnnotatedFormula(x, LeftAnnotation), AnnotatedFormula(y, RightAnnotation))
  // val axiom2 = (AnnotatedFormula(y, LeftAnnotation), AnnotatedFormula(z, RightAnnotation))
  // val axiomSet: Set[(AnnotatedFormula, AnnotatedFormula)] = Set(axiom1, axiom2)

  // val gamma = AnnotatedFormula(x, LeftAnnotation)
  // val delta = AnnotatedFormula(z, RightAnnotation)

  val extendedWhitman = ExtendedWhitman(axiomSet)
  if extendedWhitman.prove(gamma, delta) then
    print("Success")
  else
    print("Failed")
}
