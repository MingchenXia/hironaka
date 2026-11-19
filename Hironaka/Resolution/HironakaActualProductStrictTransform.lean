import Hironaka.Resolution.HironakaActualProductBlowup
import Hironaka.Blowup.ExceptionalFibres

/-! Strict transforms of arbitrary old members and the horizontal divisor
under the literal product map. The native product theorem supplies the map's
provenance; its blowup conclusion is not used in either set identity.
Blueprint FIRST: `hironaka-actual-product-strict-transform.tex`. -/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualProductStrictTransform
noncomputable section
open Hironaka.BlowupSequences BlowupTowers
  BlowupStrictSubmanifold HironakaActualProjectionTestRecord HironakaActualProductBlowup
variable {n : ℕ} {X D : CMfd.{u} n} {C : Set X} {π : D → X}

/-- Every old set commutes with strict transform under the literal product,
without a closedness, admissibility or blowup premise. -/
theorem product_strictTransform (A : Set X) :
    geoStrictTransform (productMap π) ((Prod.fst : projectionAmbient X → X) ⁻¹' C)
        ((Prod.fst : projectionAmbient X → X) ⁻¹' A) =
      (Prod.fst : projectionAmbient D → D) ⁻¹' geoStrictTransform π C A := by
  have hSet : (productMap π) ⁻¹'
      (((Prod.fst : projectionAmbient X → X) ⁻¹' A) \
        ((Prod.fst : projectionAmbient X → X) ⁻¹' C)) =
      (π ⁻¹' (A \ C)) ×ˢ (Set.univ : Set (ComplexModel 1)) := by
    ext p
    simp only [mem_preimage, mem_sdiff, productMap, mem_prod, mem_univ, and_true]
  rw [geoStrictTransform, hSet, closure_prod_eq, closure_univ]
  ext p
  simp only [mem_prod, mem_univ, and_true, mem_preimage, geoStrictTransform]

/-- The SAME native source blowup gives the necessary density, including
empty manifolds and every centre allowed by the native hypothesis. -/
theorem horizontal_strictTransform (hπ : IsBlowupAlong n C π) :
    geoStrictTransform (productMap π) ((Prod.fst : projectionAmbient X → X) ⁻¹' C)
        (horizontal X) = horizontal D := by
  have hSet : (productMap π) ⁻¹'
      (horizontal X \ ((Prod.fst : projectionAmbient X → X) ⁻¹' C)) =
      (π ⁻¹' C)ᶜ ×ˢ ({0} : Set (ComplexModel 1)) := by
    ext p
    simp only [mem_preimage, mem_sdiff, productMap, horizontal, mem_ofPred_eq,
      mem_prod, mem_compl_iff, mem_singleton_iff]
    exact and_comm
  have hDense : closure (π ⁻¹' C)ᶜ = Set.univ := by
    rw [closure_compl, ExceptionalFibres.interior_preimage_eq_empty hπ, compl_empty]
  rw [geoStrictTransform, hSet, closure_prod_eq, hDense, isClosed_singleton.closure_eq]
  ext p
  simp only [mem_prod, mem_univ, true_and, mem_singleton_iff, horizontal, mem_ofPred_eq]

end
end Hironaka.HironakaActualProductStrictTransform
