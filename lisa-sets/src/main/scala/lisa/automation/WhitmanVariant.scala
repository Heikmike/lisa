import lisa.prooflib.ProofTacticLib.ProofTatic
import lisa.prooflib.Library
import lisa.fol.FOL as F

object WhitmanVariant extends ProofTatic {
  def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTaticJudgement = {
    if (bot.right.size != 1)
      return proof.InvalidProofTactic("The goal must be of the form Γ |- s <= t.")
  }

}
