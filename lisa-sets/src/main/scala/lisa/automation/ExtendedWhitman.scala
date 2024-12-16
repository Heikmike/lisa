import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.utils.K.{_, given}
import lisa.kernel.proof.SCProof

class ExtendedWhitman(axiomsSeq: Seq[Sequent]) {
  private def isNegation(formula: Formula): Boolean = {
    return true
  }

  private def isDisjunction(formula: Formula): Boolean = {
    return true
  }

  private def isConjunction(formula: Formula): Boolean = {
    return true
  }

  def prove(goal: Sequent): Either[SCProof, String] = {
    val axioms = axiomsSeq.toSet
    val axiomsFormulas = axioms map (_.left.head) union (axioms map (_.right.head))
    val proven: Set[Sequent] = Set()
    val visited = Set.empty[Sequent]

    if proven contains goal then return Left(SCProof(proven toIndexedSeq))
    if visited contains goal then return Right("Cyclic proof")

    visited += goal
    val gamma = goal.left.head
    val delta = goal.right.head

    val success = (gamma, delta) match {
      case (phi, phi) => Left(SCProof(IndexedSeq(SC.Hypothesis(goal, phi)))) 
      case (_, _) if axioms contains goal => SCProof(IndexedSeq())
      case (gamma, delta) => 

      case gamma != None, delta != None => (prove(gamma, none) || prove(none, delta)) 
      
      case (neg(psi)_left, delta) => prove(psi_right, delta) 
      case (And(phi,psi)_left, delta) => (prove(phi_left, delta) || prove(psi_left, delta)) 
      case (Or(phi,psi)_left, delta) => (prove(phi_left, delta) && prove(psi_left, delta)) 
      
      case (neg(psi)_right, delta) => (prove(psi_left, delta))
      case (And(phi,psi)_right, delta) => (prove(phi_right, delta) && prove(psi_right, delta)) 
      case (Or(phi,psi)_right, delta) => (prove(phi_right, delta) || prove(psi_right,delta)) 

      case (gamma, neg(psi)_left) => prove(gamma, psi_left) 
      case (gamma, And(phi,psi)_left) => (prove(gamma, phi_left) || prove(gamma, psi_left)) 
      case (gamma, Or(phi,psi)_left) => (prove(gamma, phi_left) && prove(gamma,psi_left)) 
      
      case (gamma, neg(psi)_right) => (prove(gamma,psi_left))
      case (gamma, And(phi,psi)_right) => (prove(gamma, phi_right) && prove(gamma, psi_right)) 
      case (gamma, Or(phi,psi)_right) => (prove(gamma, phi_right) || prove(gamma, psi_right)) 

      case AxFormula(x in AxFormula => (prove(gamma, x_right) && prove(x_left, delta)) || (prove(delta, x_right) && prove(x_left, gamma)) 

      // my idea for handle left and right gives to prove a array (Formula: F, side: 0 - left, 1 - right) 
      // when you analyze the formula you analyze side and F and the rebuild a new array like
      // ((And(psi, phi), 0), delta) => (prove((psi, 0), delta)) || prove((phi,0), delta)) 
      // I think you don't have to build new strange property for Formula and subformula because the side is at  total formula level 
    }
  }
}
