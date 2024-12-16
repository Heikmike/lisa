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
      case _ if axioms.contains((gamma, delta)) => Left(SCProof(steps)) // Ax

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

    success match
      case Left(proof) =>
        proven = proven ++ Set((gamma, delta))
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
