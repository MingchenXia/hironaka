import DeJongAlterations.Geometry.GenericallyEtaleComposition
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Actual dense etale opens of reduced irreducible components

An actual Noetherian component contains an actual nonempty target open.
On that open its actual closed immersion is surjective and is an
isomorphism when the target is reduced. Dense source-open transport uses
the actual image-open isomorphism, not an assumed etale-open certificate.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.AlterationDominatingBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Z W V : Scheme.{u}}

/-- An actual component closed immersion into a reduced Noetherian scheme
has an internally produced dense etale source open. -/
theorem genericallyEtale_component
    (j : Z ⟶ W) [IsIntegral Z] [IsClosedImmersion j]
    [IsReduced W] [AlgebraicGeometry.IsNoetherian W]
    (hj : Set.range j ∈ irreducibleComponents W) :
    IsGenericallyEtale j := by
  obtain ⟨o, ho, hne, hsub⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent (Set.range j) hj
  let U : W.Opens := ⟨o, ho⟩
  let : Surjective (j ∣_ U) := ⟨by
    intro y
    obtain ⟨x, hx⟩ := hsub y.property
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change j x ∈ U
      rw [hx]
      exact y.property
    · apply Subtype.ext
      simpa only [morphismRestrict_base_coe] using hx⟩
  let : IsIso (j ∣_ U) := isIso_of_isClosedImmersion_of_surjective (j ∣_ U)
  have hne' : ((j ⁻¹ᵁ U : Z.Opens) : Set Z).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨x, hx⟩ := hsub hy
    exact ⟨x, by change j x ∈ U; rw [hx]; exact hy⟩
  refine ⟨j ⁻¹ᵁ U, (j ⁻¹ᵁ U).isOpen.dense hne', ?_⟩
  rw [← morphismRestrict_ι]
  infer_instance

/-- Generic etaleness proved on an actual dense source open immersion
transports through its actual image-open isomorphism. -/
theorem genericallyEtale_of_source_open
    (i : Z ⟶ W) (p : W ⟶ V) [IsOpenImmersion i] [IsDominant i]
    (h : IsGenericallyEtale (i ≫ p)) : IsGenericallyEtale p := by
  obtain ⟨U, hU, hEt⟩ := h
  let := hEt
  refine ⟨i ''ᵁ U, ?_, ?_⟩
  · change Dense (i '' (U : Set Z))
    exact i.denseRange.dense_image i.continuous hU
  · rw [← i.isoImage_inv_ι U, Category.assoc, Category.assoc]
    infer_instance

end DeJongAlterations.Geometry.AlterationDominatingBaseChange
