import Hironaka.Geometry.QuotGrassmannPivotGlobalPullbackSections
import Hironaka.Algebra.PluckerQuotTransitionFixedIndices
import Mathlib.AlgebraicGeometry.Cover.Open

/-! The same original fixed-complement pivot morphisms cover the original projective model. -/

noncomputable section

open scoped Classical
open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot Algebra.PluckerQuotTransition

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

/-- Every actual injective original coordinate selector extends to the same original ambient
permutation while keeping its selected original columns literally unchanged. -/
theorem originalCoordinate_exists_fixedPivot
    (j : Fin (pluckerDimension ι ν + 1))
    (hj : Function.Injective (coordinateSelector ι ν j)) :
    ∃ p : (ι ⊕ ν) ≃ (ι ⊕ ν),
      (∀ i, p (Sum.inl i) = coordinateSelector ι ν j i) ∧
        pivotIndex (coordinateSelector ι ν) p = j := by
  let a : ι ↪ (ι ⊕ ν) := ⟨coordinateSelector ι ν j, hj⟩
  let c := originalFixedPivotComplementEquiv a (Nat.card_eq_fintype_card (α := ι))
  let p := (Equiv.sumCongr (Equiv.refl ι) c).trans (originalPivotComplementEquiv a)
  have hp (i : ι) : p (Sum.inl i) = coordinateSelector ι ν j i := rfl
  refine ⟨p, hp, ?_⟩
  apply (coordinateSelector ι ν).injective
  simp only [pivotIndex, Equiv.apply_symm_apply]
  funext i
  exact hp i

variable (R : Type u) [CommRing R]

/-- Every point of the SAME original model lies in an actual original pivot morphism with
the SAME fixed original polynomial chart source. -/
theorem originalFixedPivotModelMorphism_cover (x : projectiveModel R ι ν) :
    ∃ p : (ι ⊕ ν) ≃ (ι ⊕ ν), x ∈ Set.range (originalPivotModelMorphism R p) := by
  have hx : x ∈ ⨆ j : {j : Fin (pluckerDimension ι ν + 1) //
      Function.Injective (coordinateSelector ι ν j)}, coordinateOpen R ι ν j.val := by
    rw [iSup_pivotOpen_eq_top R ι ν]
    trivial
  obtain ⟨j, hxj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨p, _, hp⟩ := originalCoordinate_exists_fixedPivot j.val j.property
  have hx' : x ∈ coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) p) := by
    simpa only [hp] using hxj
  let y : (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) p)).toScheme := ⟨x, hx'⟩
  refine ⟨p, (pivotMatrixSchemeIso R p).hom y, ?_⟩
  change ((pivotMatrixSchemeIso R p).hom ≫ (pivotMatrixSchemeIso R p).inv ≫
    (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) p)).ι) y = x
  rw [Iso.hom_inv_id_assoc]
  rfl

end Hironaka.Geometry.QuotGrassmann
