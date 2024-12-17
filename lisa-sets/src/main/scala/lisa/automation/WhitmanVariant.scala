import lisa.prooflib.ProofTacticLib.ProofTactic
import lisa.prooflib.Library
import lisa.fol.FOL.*
import lisa.kernel.proof.SCProof

object WhitmanTactic extends ProofTactic {

  /**
   * Attempts to prove a goal sequent using ExtendedWhitman algorithm.
   *
   * @param axioms The set of axioms to use as assumptions in the proof.
   * @param bot   The sequent to prove.
   * @return A ProofTacticJudgement, either valid or invalid depending on the success of the algorithm.
   */
  def apply(using lib: Library, proof: lib.Proof)(axioms: Set[(AnnotatedFormula, AnnotatedFormula)])(bot: Sequent): proof.ProofTacticJudgement = {
    if (bot.left.size >= 0 || bot.right.size != 1) {
      return proof.InvalidProofTactic("The goal sequent must have at most one formula on the left and right side.")
    }

    val gamma = AnnotatedFormula(⊥, NoneAnnotation)
    val delta = AnnotatedFormula(bot.right.head, RightAnnotation)

    val whitman = new ExtendedWhitman(axioms)

    whitman.prove(gamma, delta) match
      case Left(scProof) => // If successful
        proof.ValidProofTactic(bot, scProof.steps, Seq()) // Return a valid proof tactic
      case Right(msg) => // If failed
        proof.InvalidProofTactic(msg)
  }
}
