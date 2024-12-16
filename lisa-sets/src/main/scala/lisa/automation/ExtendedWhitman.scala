import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.utils.K.{_, given}
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof

class ExtendedWhitman(axiomsSeq: Seq[Sequent]) {
  def prove(goal: Sequent): Either[SCProof, String] = {
    val axioms = axiomsSeq.toSet
    val axiomsFormulas = axioms map (_.left.head) union (axioms map (_.right.head))
    var proven: Set[Sequent] = Set()
    var visited: Set[Sequent] = Set()
    var steps: IndexedSeq[SCProofStep] = IndexedSeq()

    if proven contains goal then return Left(SCProof(steps))
    if visited contains goal then return Right("Cyclic proof")

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
  }
}
