import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.utils.K.{_, given}
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof

// INFO: Consider moving those objects and classes lisa.kernel.fol.FormulaDefinitions
sealed trait Annotation
case object LeftAnnotation extends Annotation
case object RightAnnotation extends Annotation
case object NoneAnnotation extends Annotation

case class AnnotatedFormula(formula: Formula, annotation: Annotation)

class ExtendedWhitman(axioms: Set[(AnnotatedFormula, AnnotatedFormula)]) {
  def prove(gamma: AnnotatedFormula, delta: AnnotatedFormula): Either[SCProof, String] = {
    val axiomsFormulas = axioms flatMap { case (a, b) => Set(a.formula, b.formula) }
    val goal = Sequent(Set(gamma.formula), Set(delta.formula))
    var proven: Set[(AnnotatedFormula, AnnotatedFormula)] = Set()
    var visited: Set[(AnnotatedFormula, AnnotatedFormula)] = Set()
    var steps: IndexedSeq[SCProofStep] = IndexedSeq()

    if proven.contains((gamma, delta)) then return Left(SCProof(steps))
    if visited.contains((gamma, delta)) then return Right("Cyclic proof")

    visited = visited ++ Set((gamma, delta))

    val success = (gamma, delta) match // success means that success has type Left(proof)
      case (AnnotatedFormula(phi, phiAnnot), AnnotatedFormula(psi, psiAnnot))
      if (phi == psi && phiAnnot != psiAnnot && phiAnnot != NoneAnnotation && psiAnnot != NoneAnnotation) => // Hyp
          val hyp = Hypothesis(goal, phi)
          steps = steps :+ hyp
          Left(SCProof(steps))

      // ==== Gamma cases ====
      case (AnnotatedFormula(ConnectorFormula(Neg, phi), annot), delta) => // LeftNot
        val reversedAnnot = annot match
          case LeftAnnotation => RightAnnotation
          case RightAnnotation => LeftAnnotation
          case NoneAnnotation => NoneAnnotation

        prove(AnnotatedFormula(phi.head, reversedAnnot), delta)

      case (AnnotatedFormula(ConnectorFormula(And, Seq(phi, psi)), annot), delta) => // LeftAnd
        val p1 = prove(AnnotatedFormula(phi, annot), delta)
        val p2 = prove(AnnotatedFormula(psi, annot), delta)
        // TODO: Add the proof steps
        if p1.isLeft then p1 else p2

      case (AnnotatedFormula(ConnectorFormula(Or, Seq(phi, psi)), annot), delta) => // LeftOr
        val p1 = prove(AnnotatedFormula(phi, annot), delta)
        val p2 = prove(AnnotatedFormula(psi, annot), delta)
        // TODO: Add the proof steps
        if p1.isLeft && p2.isLeft then Left(SCProof(steps)) else Right("Error")


      // ==== Delta cases ====
      case (delta, AnnotatedFormula(ConnectorFormula(Neg, phi), annot)) => // RightNot
        val reversedAnnot = annot match
          case LeftAnnotation => RightAnnotation
          case RightAnnotation => LeftAnnotation
          case NoneAnnotation => NoneAnnotation

        prove(delta, AnnotatedFormula(phi.head, reversedAnnot))

      case (gamma, AnnotatedFormula(ConnectorFormula(And, Seq(phi, psi)), annot)) => // RightAnd
        val p1 = prove(gamma, AnnotatedFormula(phi, annot))
        val p2 = prove(gamma, AnnotatedFormula(psi, annot))
        // TODO: Add the proof steps
        if p1.isLeft then p1 else p2

      case (gamma, AnnotatedFormula(ConnectorFormula(Or, Seq(phi, psi)), annot)) => // RightOr
        val p1 = prove(gamma, AnnotatedFormula(phi, annot))
        val p2 = prove(gamma, AnnotatedFormula(psi, annot))
        // TODO: Add the proof steps
        if p1.isLeft && p2.isLeft then Left(SCProof(steps)) else Right("Error")

      case _ =>
        if axioms.contains((gamma, delta)) then Left(SCProof(steps)) // Ax
        if (gamma._2 != NoneAnnotation && delta._2 != NoneAnnotation) then // Weaken
          // NOTE: The formula doesn't really matter, what's important is the None annotation
          // There might be a smarter way to represent None
          val p1 = prove(gamma, AnnotatedFormula(gamma._1, NoneAnnotation))
          val p2 = prove(AnnotatedFormula(delta._1, NoneAnnotation), delta)
          // TODO: Add the proof steps
          if p1.isLeft then return p1 else return p2

          val cut = axiomsFormulas.find(x => {
            val p1 = prove(gamma, AnnotatedFormula(x, RightAnnotation))
            val p2 = prove(AnnotatedFormula(x, LeftAnnotation), delta)
            val p3 = prove(delta, AnnotatedFormula(x, RightAnnotation))
            val p4 = prove(AnnotatedFormula(x, LeftAnnotation), gamma)
            (p1.isLeft && p2.isLeft) || (p3.isLeft && p4.isLeft)
          })
          cut match
            case Some(x) => Left(SCProof(steps))
            case None => Right("Error")


    success match
      case Left(proof) =>
        proven = proven ++ Set((gamma, delta))
        Left(proof)
      case Right(error) => Right(error)
  }
}
