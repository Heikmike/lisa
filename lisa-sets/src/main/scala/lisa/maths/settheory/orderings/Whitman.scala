package lisa.maths.settheory.orderings

import lisa.automation.ExtendedWhitman
import lisa.fol.FOL.*

object Whitman extends lisa.Main {
  val x = VariableFormula("x")
  val u = VariableFormula("u")
  val left = x ∧ (¬(x) ∨ u)

  val axiom = AnnotatedFormula(left, RightAnnotation)
  val axiomSet = Set((AnnotatedFormula(⊥, NoneAnnotation), axiom))
  val gamma = AnnotatedFormula(left, LeftAnnotation)
  val delta = AnnotatedFormula(u, RightAnnotation)

  val extendedWhitman = ExtendedWhitman(axiomSet)
  extendedWhitman.prove(gamma, delta) match
    case Left(proof) => println("success")
    case Right(error) => println(error)
}
