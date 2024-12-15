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
      case (gamma, delta) => {
        if isNegation(gamma) then
          prove(Sequent())
      }
    }
  }
}
