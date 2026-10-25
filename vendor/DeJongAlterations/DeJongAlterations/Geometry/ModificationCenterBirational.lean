import DeJongAlterations.Modification
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The full target restriction of a separated birational partial isomorphism

The actual compatible partial inverse lifts through the native restriction
pullback. Its other inverse identity follows from native separated-morphism
extensionality on a dominant open of the reduced source.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.ModificationCenter

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/-- A separated morphism from a reduced scheme is an isomorphism over the entire
native target open of a compatible dense-open partial isomorphism. -/
theorem isIso_restrict_partialIso_target (f : X ⟶ Y) [IsReduced X] [IsSeparated f]
    (e : X.PartialIso Y) (he : e.IsOver f (𝟙 Y)) : IsIso (f ∣_ e.target) := by
  have heq : e.iso.hom ≫ e.target.ι = e.source.ι ≫ f := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using he
  have hle : e.source ≤ f ⁻¹ᵁ e.target := by
    intro x hx
    have H := congrArg (fun k : e.source.toScheme ⟶ Y => k ⟨x, hx⟩) heq
    have hm := (e.iso.hom ⟨x, hx⟩).2
    change f x ∈ e.target
    simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using H ▸ hm
  let j := X.homOfLE hle
  have hj : j ≫ f ∣_ e.target = e.iso.hom := by
    apply (cancel_mono e.target.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι, ← heq]
  have hi : e.target.ι = e.iso.inv ≫ e.source.ι ≫ f := by
    rw [← heq, Iso.inv_hom_id_assoc]
  let a : e.target.toScheme ⟶ (f ⁻¹ᵁ e.target).toScheme :=
    (isPullback_morphismRestrict f e.target).lift (𝟙 _) (e.iso.inv ≫ e.source.ι) (by
      simpa only [Category.id_comp, Category.assoc] using hi)
  have ha : a ≫ f ∣_ e.target = 𝟙 _ :=
    (isPullback_morphismRestrict f e.target).lift_fst _ _ _
  have hai : a ≫ (f ⁻¹ᵁ e.target).ι = e.iso.inv ≫ e.source.ι :=
    (isPullback_morphismRestrict f e.target).lift_snd _ _ _
  have hja : e.iso.hom ≫ a = j := by
    apply (cancel_mono (f ⁻¹ᵁ e.target).ι).mp
    rw [Category.assoc, hai, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]
  have : IsDominant j := AlgebraicGeometry.Opens.isDominant_homOfLE e.dense_source hle
  have hother : (f ∣_ e.target) ≫ a = 𝟙 _ := by
    apply ext_of_isDominant_of_isSeparated (f ∣_ e.target) ?_ j ?_
    · rw [Category.assoc, ha, Category.comp_id, Category.id_comp]
    · rw [← Category.assoc, hj, hja, Category.comp_id]
  exact ⟨⟨a, hother, ha⟩⟩

/-- An actual modification internally supplies a dense target open with an isomorphism
on its full native inverse image. -/
theorem exists_dense_isomorphism_open (f : X ⟶ Y) [hf : IsModification f] :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ IsIso (f ∣_ U) := by
  let := hf.sourceIntegral
  obtain ⟨e, he⟩ := hf.birational
  exact ⟨e.target, e.dense_target, isIso_restrict_partialIso_target f e he⟩

end DeJongAlterations.Geometry.ModificationCenter
