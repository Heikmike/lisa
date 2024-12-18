package lisa.maths.settheory.orderings

import lisa.automation.ExtendedWhitman
import lisa.fol.FOL.*

object Whitman extends lisa.Main {
  // ==== Example 3.1 from paper ====
  // val x = VariableFormula("x")
  // val u = VariableFormula("u")
  // val left = x ∧ (¬(x) ∨ u)
  // val right = ¬(x) ∨ u
  // val bottom = AnnotatedFormula(⊥, NoneAnnotation)

  // val axiom = (bottom, AnnotatedFormula(left, RightAnnotation))
  // val axiomSet: Set[(AnnotatedFormula, AnnotatedFormula)] = Set(axiom)
  // val gamma = bottom
  // val delta = AnnotatedFormula(right, RightAnnotation)

  // ==== De Morgan's Law ====
  // val phi = VariableFormula("phi")
  // val psi = VariableFormula("psi")
  // val axiomSet: Set[(AnnotatedFormula, AnnotatedFormula)] = Set()
  // val gamma = AnnotatedFormula(¬(phi ∧ psi), LeftAnnotation)
  // val delta = AnnotatedFormula(¬(phi) ∨ ¬(psi), RightAnnotation)

  // ==== Transitivity ====
  // val x = VariableFormula("x")
  // val y = VariableFormula("y")
  // val z = VariableFormula("z")

  // val axiom1 = (AnnotatedFormula(x, LeftAnnotation), AnnotatedFormula(y, RightAnnotation))
  // val axiom2 = (AnnotatedFormula(y, LeftAnnotation), AnnotatedFormula(z, RightAnnotation))
  // val axiomSet: Set[(AnnotatedFormula, AnnotatedFormula)] = Set(axiom1, axiom2)

  // val gamma = AnnotatedFormula(x, LeftAnnotation)
  // val delta = AnnotatedFormula(z, RightAnnotation)
  

  // ==== Example 3.2 ====
  // val phi = VariableFormula("phi")
  // val psi = VariableFormula("psi")
  // val theta = VariableFormula("theta")
  // val etha = VariableFormula("etha")

  // val f1 = psi ∧ theta
  // val axiom1 = (AnnotatedFormula(phi, LeftAnnotation), AnnotatedFormula(f1, RightAnnotation))
  // val axiom2 = (AnnotatedFormula(theta, LeftAnnotation), AnnotatedFormula(etha, RightAnnotation))
  // val axiom3 = (AnnotatedFormula(psi, LeftAnnotation), AnnotatedFormula(¬(etha), RightAnnotation))
  // val axiomSet = Set(axiom1, axiom2, axiom3)
  // val gamma = AnnotatedFormula(phi, LeftAnnotation)
  // val delta = AnnotatedFormula(¬(phi), RightAnnotation)

  // ==== Example Allessio ====

  val phi = VariableFormula("phi")
  val psi = VariableFormula("psi")
  val eta = VariableFormula("eta")
  val axiom1 = (AnnotatedFormula(phi, LeftAnnotation), AnnotatedFormula(¬(eta), RightAnnotation))
  val axiom2 = (AnnotatedFormula(psi, LeftAnnotation), AnnotatedFormula(¬(eta), RightAnnotation))
  val axiomSet = Set(axiom1, axiom2)
  val gamma = AnnotatedFormula((phi ∨ psi) ∧ eta, LeftAnnotation)
  val delta = AnnotatedFormula((phi ∨ psi) ∧ eta, LeftAnnotation)

  val extendedWhitman = ExtendedWhitman(axiomSet)
  if extendedWhitman.prove(gamma, delta) then
    print("Success")
  else
    print("Failed")
}
