import DeJongAlterations.Geometry.ProjectiveCompactification
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The actual enlarged boundary in source 4.7

The vanishing ideal of the complement of the source's boundary-free open
constructs the closed set j(Z) ∪ (Xbar \ j(X)) internally. Its support
pulls back to precisely the original closed support.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.ProjectiveCompactification

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} {R : Type u} [CommRing R] {n : ℕ}
variable (e : X ⟶ projectiveSpace R n) [IsImmersion e] [QuasiCompact e]

/-- The actual reduced boundary of the constructed projective compactification. -/
def extendedBoundary (D : X.IdealSheafData) : (closure e).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ((inclusion e ''ᵁ D.support.compl).compl)

/-- The actual compactification boundary has exactly the closed support specified in de Jong 4.7. -/
theorem extendedBoundary_support (D : X.IdealSheafData) :
    ((extendedBoundary e D).support : Set (closure e)) =
      inclusion e '' (D.support : Set X) ∪ (Set.range (inclusion e))ᶜ := by
  rw [extendedBoundary, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  change (inclusion e '' (D.support : Set X)ᶜ)ᶜ =
    inclusion e '' (D.support : Set X) ∪ (Set.range (inclusion e))ᶜ
  ext x
  constructor
  · intro hx
    by_cases hr : x ∈ Set.range (inclusion e)
    · obtain ⟨y, rfl⟩ := hr
      left
      refine ⟨y, ?_, rfl⟩
      by_contra hy
      exact hx ⟨y, hy, rfl⟩
    · exact Or.inr hr
  · rintro (⟨y, hy, rfl⟩ | hx) ⟨z, hz, hzx⟩
    · have hzy : z = y := (inclusion e).isEmbedding.injective hzx
      exact hz (hzy ▸ hy)
    · exact hx ⟨z, hzx⟩

/-- The whole actual boundary support pulls back to the original closed support. -/
theorem inclusion_preimage_extendedBoundary_support (D : X.IdealSheafData) :
    inclusion e ⁻¹' ((extendedBoundary e D).support : Set (closure e)) =
      (D.support : Set X) := by
  rw [extendedBoundary_support]
  ext x
  constructor
  · rintro (⟨y, hy, hyx⟩ | hx)
    · exact (inclusion e).isEmbedding.injective hyx ▸ hy
    · exact False.elim (hx ⟨x, rfl⟩)
  · intro hx
    exact Or.inl ⟨x, hx, rfl⟩

/-- Native ideal-sheaf pullback gives exactly the original closed support. -/
theorem extendedBoundary_comap_support (D : X.IdealSheafData) :
    ((extendedBoundary e D).comap (inclusion e)).support = D.support := by
  rw [Scheme.IdealSheafData.support_comap]
  apply SetLike.coe_injective
  exact inclusion_preimage_extendedBoundary_support e D

/-- A proper original closed support gives a proper boundary on the actual projective compactification. -/
theorem extendedBoundary_support_ne_top (D : X.IdealSheafData) (hD : D.support ≠ ⊤) :
    (extendedBoundary e D).support ≠ ⊤ := by
  intro h
  apply hD
  apply SetLike.coe_injective
  rw [← inclusion_preimage_extendedBoundary_support e D, h]
  exact Set.preimage_univ

variable {k : Type u} [Field k]

/-- Source 4.7's actual projective compactification together with its internally constructed closed boundary. -/
theorem exists_projective_compactification_with_boundary
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p]
    {n : ℕ} (e : X ⟶ projectiveSpace k n) [IsImmersion e]
    (he : e ≫ projectiveSpaceStructure k n = p) (D : X.IdealSheafData) :
    ∃ (Xbar : Scheme.{u}) (pbar : Xbar ⟶ Spec (CommRingCat.of k))
      (j : X ⟶ Xbar) (Dbar : Xbar.IdealSheafData),
      IsVariety pbar ∧ IsProjectiveOver pbar ∧ IsOpenImmersion j ∧ IsDominant j ∧
        j ≫ pbar = p ∧
        (Dbar.support : Set Xbar) = j '' (D.support : Set X) ∪ (Set.range j)ᶜ ∧
        (Dbar.comap j).support = D.support ∧
        (D.support ≠ ⊤ → Dbar.support ≠ ⊤) := by
  let := immersion_isQuasiCompact p e
  exact ⟨closure e, closureStructure e, inclusion e, extendedBoundary e D,
    structure_isVariety p e, structure_isProjective e, inferInstance, inferInstance,
    (inclusion_structure e).trans he, extendedBoundary_support e D,
    extendedBoundary_comap_support e D, extendedBoundary_support_ne_top e D⟩

end DeJongAlterations.Geometry.ProjectiveCompactification
