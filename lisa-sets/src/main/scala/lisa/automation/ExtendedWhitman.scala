import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.utils.K.{_, given}
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof

sealed trait Annotation
case object LeftAnnotation extends Annotation
case object RightAnnotation extends Annotation

case class AnnotatedFormula(formula: Formula, annotation: Annotation)


class ExtendedWhitman(axioms: Set[(AnnotatedFormula, AnnotatedFormula)]) {
  def prove(gamma: AnnotatedFormula, delta: AnnotatedFormula): Either[SCProof, String] = {
    val axiomsFormulas = axioms flatMap { case (a, b) => Set(a.formula, b.formula) }
    var proven: Set[(AnnotatedFormula, AnnotatedFormula)] = Set()
    var visited: Set[(AnnotatedFormula, AnnotatedFormula)] = Set()
    var steps: IndexedSeq[SCProofStep] = IndexedSeq()

    if proven contains (gamma, delta) then return Left(SCProof(steps))
    if visited contains (gamma, delta) then return Right("Cyclic proof")

    visited = visited union Set(goal)
    val left = goal.left
    val right = goal.right
    val gamma = left.head
    val delta = right.head

    if axioms contains goal then return Left(SCProof(IndexedSeq())) // Ax
    if gamma == delta then // Hyp
      val hyp = Hypothesis(goal, gamma)
      steps = steps :+ hyp
      return Left(SCProof(steps))

    val success = (gamma, delta) match // success means that success has type Left(proof)
      case(ConnectorFormula(Neg, phi), delta) => // LeftNot
        val seq = Sequent(phi.toSet, Set(delta))
        prove(seq)
      case(ConnectorFormula(And, Seq(phi, psi)), delta) => // LeftAnd
        val seq1 = Sequent(Set(phi), right)
        val seq2 = Sequent(Set(psi), right)
        val p1 = prove(seq1)
        val p2 = prove(seq2)

        // TODO: Add the proof steps to the steps list
        if p1.isLeft then p1 else p2
      case(ConnectorFormula(Or, Seq(phi, psi)), delta) => // LeftOr
        val seq1 = Sequent(Set(phi), right)
        val seq2 = Sequent(Set(psi), right)
        val p1 = prove(seq1)
        val p2 = prove(seq2)

        if p1.isLeft && p2.isLeft then p1 else Right("Error")
      case(gamma, ConnectorFormula(Neg, phi)) => // RightNot
        val seq = Sequent(left, phi.toSet)

    success match
      case Left(proof) =>
        proven = proven union Set(goal)
        Left(proof)
      case Right(error) => Right(error)
// =======
//     val success = (gamma, delta) match {
//       case (phi, phi) => Left(SCProof(IndexedSeq(SC.Hypothesis(goal, phi)))) 
//       case (_, _) if axioms contains goal => SCProof(IndexedSeq())
//       case (gamma, delta) => 

//       case gamma != None, delta != None => (prove(gamma, none) || prove(none, delta)) 
//       
//       case (neg(psi)_left, delta) => prove(psi_right, delta) 
//       case (And(phi,psi)_left, delta) => (prove(phi_left, delta) || prove(psi_left, delta)) 
//       case (Or(phi,psi)_left, delta) => (prove(phi_left, delta) && prove(psi_left, delta)) 
//       
//       case (neg(psi)_right, delta) => (prove(psi_left, delta))
//       case (And(phi,psi)_right, delta) => (prove(phi_right, delta) && prove(psi_right, delta)) 
//       case (Or(phi,psi)_right, delta) => (prove(phi_right, delta) || prove(psi_right,delta)) 

//       case (gamma, neg(psi)_left) => prove(gamma, psi_left) 
//       case (gamma, And(phi,psi)_left) => (prove(gamma, phi_left) || prove(gamma, psi_left)) 
//       case (gamma, Or(phi,psi)_left) => (prove(gamma, phi_left) && prove(gamma,psi_left)) 
//       
//       case (gamma, neg(psi)_right) => (prove(gamma,psi_left))
//       case (gamma, And(phi,psi)_right) => (prove(gamma, phi_right) && prove(gamma, psi_right)) 
//       case (gamma, Or(phi,psi)_right) => (prove(gamma, phi_right) || prove(gamma, psi_right)) 

//       case AxFormula(x in AxFormula => (prove(gamma, x_right) && prove(x_left, delta)) || (prove(delta, x_right) && prove(x_left, gamma)) 

//       // my idea for handle left and right gives to prove a array (Formula: F, side: 0 - left, 1 - right) 
//       // when you analyze the formula you analyze side and F and the rebuild a new array like
//       // ((And(psi, phi), 0), delta) => (prove((psi, 0), delta)) || prove((phi,0), delta)) 
//       // I think you don't have to build new strange property for Formula and subformula because the side is at  total formula level 
//     }
// >>>>>>> origin/feature/whitman-variant
  }
}
