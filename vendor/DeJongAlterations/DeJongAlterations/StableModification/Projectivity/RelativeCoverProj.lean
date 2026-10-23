/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3C)
-/
import DeJongAlterations.StableModification.CurvesField.AmpleFiber

/-!
# Locally relatively projective morphisms over affine opens

Blueprint `sm-projectivity-relative.tex`, preliminaries of `lem:sm-ltg-two-affines`. If
`β : X ⟶ Y` is projective relative to `W' ⟶ Y ⟶ Spec R` over an open `W' ⊆ Y` (one member of the
cover of OM3A's `LocallyRelativelyProjective`), then over every affine open `W ⊆ W'` the preimage
`β⁻¹ W` is a closed subscheme of `ℙⁿ_{Γ(Y, W)}` over `Spec Γ(Y, W)`
(`isProjectiveOver_morphismRestrict_of_le`): `β⁻¹ W` is the base change of `β ∣_ W'` along
`Spec Γ(Y, W) ≅ W ⊆ W'`. This is Codex's `Cohomology.isProjectiveOver_morphismRestrict_toSpecΓ`
with a closed immersion given only over `W'`, proved as OM3B's
`CurvesField.isProjectiveOver_fiber_of_locallyRelativelyProjective`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

open DeJong

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- `β⁻¹ W` is the base change of `β` along `Spec Γ(Y, W) ≅ W ⊆ Y` (Codex's square `S₂` in the
proof of `Cohomology.isProjectiveOver_morphismRestrict_toSpecΓ`). -/
lemma isPullback_morphismRestrict_toSpecΓ (β : X ⟶ Y) {W : Y.Opens} (hW : IsAffineOpen W) :
    IsPullback (β ⁻¹ᵁ W).ι (β ∣_ W ≫ W.toSpecΓ) β hW.fromSpec :=
  (isPullback_morphismRestrict β W).flip.of_iso (Iso.refl _) (Iso.refl _) hW.isoSpec
    (Iso.refl _) (by simp) (by simp [IsAffineOpen.isoSpec_hom]) (by simp)
    (by simp [IsAffineOpen.isoSpec_hom_fromSpec])

/-- **Projectivity over affine opens** (blueprint `lem:sm-ltg-two-affines`, preliminary): if
`β ∣_ W'` is projective relative to `W' ⟶ Y ⟶ Spec R`, then for every affine open `W ⊆ W'` the
preimage `β⁻¹ W` is projective over `Γ(Y, W)`. -/
theorem isProjectiveOver_morphismRestrict_of_le (pY : Y ⟶ Spec (.of R)) (β : X ⟶ Y)
    {W' : Y.Opens} (hW' : IsRelativelyProjective (W'.ι ≫ pY) (β ∣_ W')) {W : Y.Opens}
    (hW : IsAffineOpen W) (hle : W ≤ W') :
    IsProjectiveOver (k := Γ(Y, W)) (β ∣_ W ≫ W.toSpecΓ) := by
  set t := hW.fromSpec
  have hrange : Set.range t ⊆ Set.range W'.ι := by
    rw [IsAffineOpen.range_fromSpec, Scheme.Opens.range_ι]
    exact hle
  let t' : Spec Γ(Y, W) ⟶ W' := IsOpenImmersion.lift W'.ι t hrange
  have ht' : t' ≫ W'.ι = t := IsOpenImmersion.lift_fac _ _ _
  have hP : IsPullback (pullback.fst (β ∣_ W') t' ≫ (β ⁻¹ᵁ W').ι)
      (pullback.snd (β ∣_ W') t') β (t' ≫ W'.ι) :=
    ((IsPullback.of_hasPullback (β ∣_ W') t').flip.paste_vert
      (isPullback_morphismRestrict β W')).flip
  rw [ht'] at hP
  let e := (isPullback_morphismRestrict_toSpecΓ β hW).isoIsPullback _ _ hP
  have he : e.hom ≫ pullback.snd (β ∣_ W') t' = β ∣_ W ≫ W.toSpecΓ :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  have h₁ := hW'.pullback_snd t'
  have h₂ := isRelativelyProjective_iso_hom_comp h₁ e
  rw [he, ← Category.assoc t' W'.ι pY, ht'] at h₂
  set φ := Spec.preimage (t ≫ pY)
  have hφ : t ≫ pY = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom φ.hom) := by
    rw [Category.id_comp, CommRingCat.ofHom_hom, Spec.map_preimage]
  rw [hφ] at h₂
  exact CurvesField.isProjectiveOver_of_isRelativelyProjective_id
    ((isRelativelyProjective_comp_specMap_iff φ.hom (𝟙 _) _).mp h₂)

end

end DeJongAlterations.StableModification.Projectivity
