import Hironaka.Algebra.RelativeUnramifiedClosedFiber
import Hironaka.Algebra.NodeGeometricCompletionOriginalFiberSection
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # The literal ORIGINAL quotient closed fibre detects local unramifiedness -/

noncomputable section
open IsLocalRing
open scoped TensorProduct
namespace Hironaka.Algebra.RelativeUnramified
open NodeGeometricCompletionOriginalFiberSection
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R T : Type u) [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T]
  [Algebra R T] [IsLocalHom (algebraMap R T)]

/-- Native quotient/tensor comparison with the ENTIRE original canonical residue action. -/
def closedFiberResidueTensorEquiv :
    letI : Algebra (ResidueField R) (FiberRing R T) := baseResidueAlgebra R T
    FiberRing R T ≃ₐ[ResidueField R] (ResidueField R ⊗[R] T) := by
  letI : Algebra (ResidueField R) (FiberRing R T) := baseResidueAlgebra R T
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (maximalIdeal R)
  refine { e.toRingEquiv with commutes' := ?_ }
  intro a
  obtain ⟨r, rfl⟩ := residue_surjective a
  exact e.commutes (residue R r)

/-- Actual unramifiedness of the ORIGINAL quotient closed fibre suffices. -/
theorem formallyUnramified_of_closedFiber [Algebra.EssFiniteType R T]
    (h : letI : Algebra (ResidueField R) (FiberRing R T) := baseResidueAlgebra R T
      Algebra.FormallyUnramified (ResidueField R) (FiberRing R T)) :
    Algebra.FormallyUnramified R T := by
  let : Algebra (ResidueField R) (FiberRing R T) := baseResidueAlgebra R T
  let : Algebra.FormallyUnramified (ResidueField R) (FiberRing R T) := h
  let : Algebra.FormallyUnramified (ResidueField R) (ResidueField R ⊗[R] T) :=
    Algebra.FormallyUnramified.of_equiv (closedFiberResidueTensorEquiv R T)
  exact formallyUnramified_of_residueTensor R T

end Hironaka.Algebra.RelativeUnramified
