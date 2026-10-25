/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.SteinFinite
import DeJongAlterations.StableModification.DeJong.Interface
import DeJongAlterations.Geometry.ProjectiveSpaceBaseChange

/-!
# Stein finiteness for relatively projective morphisms

If `π : B → Y` is projective relative to `pY : Y → Spec V` in the sense of the consumer interface
(`DeJong.IsRelativelyProjective`: a closed immersion `B ↪ Y ×_V ℙⁿ_V` over `Y`, the form of
`TSM-PROJ`), then over every affine open `U ⊆ Y` the preimage `π⁻¹U` is a closed subscheme of
`ℙⁿ_{Γ(Y, U)}` (`isProjectiveOver_morphismRestrict_toSpecΓ`): the square
`ℙⁿ_{Γ(U)} → Y ×_V ℙⁿ_V` over `Spec Γ(U) → Y` is cartesian (Codex's base change of projective
space, `ProjectiveSpaceBaseChange.isPullback_projectiveCoefficientMap`), so the map
`π⁻¹U → ℙⁿ_{Γ(U)}` is the base change of the closed immersion `B ↪ Y ×_V ℙⁿ_V`.

Consequently (`SteinFinite.lean`) for `Y` locally of finite presentation over a valuation ring
`V` and `B` flat over `V`, `π_* 𝒪_B` is a finite `𝒪_Y`-algebra and the relative normalization
`π.normalization = Spec π_* 𝒪_B` is finite over `Y`
(`isFinite_fromNormalization_of_isRelativelyProjective`). This is the finiteness half of
`thm:sm-stein-finite-valuation` (plan `PLAN-SM-GEOM.md`, S8), which replaces Temkin's Lemma 4.4.1
(Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`semi-stable.tex` lines 3089–3104).

Blueprint: `sm-cohomology-stein.tex`, `lem:sm-relproj-affine`, `thm:sm-stein-finite-valuation`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry
open DeJongAlterations.Geometry.ProjectiveSpaceBaseChange
open DeJongAlterations.Geometry.BlowupProjectiveEmbedding

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {V : Type u} [CommRing V] {B Y : Scheme.{u}} (π : B ⟶ Y)
  (pY : Y ⟶ Spec (CommRingCat.of V))

/-- The coefficient map `V → Γ(Y, U)` of a `V`-scheme induces `U → Spec Γ(Y, U) → Spec V`, the
restriction of `pY` to `U`. -/
theorem toSpecΓ_SpecMap_sectionsRingHom (U : Y.Opens) :
    U.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (sectionsRingHom (structureCoeff pY) (le_top : U ≤ ⊤))) =
      U.ι ≫ pY := by
  apply ext_of_isAffine
  ext a
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
    Scheme.Opens.toSpecΓ_appTop, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
  have h := congrArg (fun g => g.hom a) (Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (sectionsRingHom (structureCoeff pY) (le_top : U ≤ ⊤))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  erw [h]
  simp only [sectionsRingHom, structureCoeff, CommRingCat.hom_ofHom, RingHom.comp_apply]
  erw [← CommRingCat.comp_apply (Y.presheaf.map _) (Y.presheaf.map _), ← Functor.map_comp]
  have hiso : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a) = a := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
    rfl
  erw [hiso]
  rfl

/-- **Projectivity over affine opens** (blueprint `lem:sm-relproj-affine`): if `B ↪ Y ×_V ℙⁿ_V`
is a closed immersion over `Y` (with `i ≫ pr₁ = π`), then for every affine open `U ⊆ Y` the
preimage `π⁻¹U` is projective over `Γ(Y, U)`: it is a closed subscheme of `ℙⁿ_{Γ(Y, U)}` over
`π|_U : π⁻¹U → U ≅ Spec Γ(Y, U)`. -/
theorem isProjectiveOver_morphismRestrict_toSpecΓ {n : ℕ}
    (i : B ⟶ pullback pY (projectiveSpaceStructure V n)) [IsClosedImmersion i]
    (hi : i ≫ pullback.fst _ _ = π) {U : Y.Opens} (hU : IsAffineOpen U) :
    IsProjectiveOver (k := Γ(Y, U)) (π ∣_ U ≫ U.toSpecΓ) := by
  let φ : V →+* Γ(Y, U) := sectionsRingHom (structureCoeff pY) (le_top : U ≤ ⊤)
  have hsq : U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) = U.ι ≫ pY :=
    toSpecΓ_SpecMap_sectionsRingHom pY U
  have hfrom : hU.fromSpec ≫ pY = Spec.map (CommRingCat.ofHom φ) := by
    rw [← cancel_epi hU.isoSpec.hom, ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec, ← hsq,
      IsAffineOpen.isoSpec_hom]
  have H := isPullback_projectiveCoefficientMap φ n
  let k : projectiveSpace Γ(Y, U) n ⟶ pullback pY (projectiveSpaceStructure V n) :=
    pullback.lift (projectiveSpaceStructure Γ(Y, U) n ≫ hU.fromSpec) (projectiveCoefficientMap φ n)
      (by rw [Category.assoc, hfrom, H.w])
  -- the square `ℙⁿ_{Γ(U)} → Y ×_V ℙⁿ_V` over `Spec Γ(U) → Y` is cartesian
  have S₁ : IsPullback k (projectiveSpaceStructure Γ(Y, U) n)
      (pullback.fst pY (projectiveSpaceStructure V n)) hU.fromSpec := by
    refine IsPullback.of_right (h₁₂ := pullback.snd pY (projectiveSpaceStructure V n))
      (h₂₂ := pY) (v₁₃ := projectiveSpaceStructure V n) ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback pY (projectiveSpaceStructure V n)).flip
    rw [pullback.lift_snd, hfrom]
    exact H
  -- `π⁻¹U` is the base change of `π` along `Spec Γ(U) ≅ U ⊆ Y`
  have S₂ : IsPullback (π ⁻¹ᵁ U).ι (π ∣_ U ≫ U.toSpecΓ) π hU.fromSpec :=
    (isPullback_morphismRestrict π U).flip.of_iso (Iso.refl _) (Iso.refl _) hU.isoSpec
      (Iso.refl _) (by simp) (by simp [IsAffineOpen.isoSpec_hom]) (by simp)
      (by simp [IsAffineOpen.isoSpec_hom_fromSpec])
  -- the map `π⁻¹U → ℙⁿ_{Γ(U)}`
  let j : (π ⁻¹ᵁ U).toScheme ⟶ projectiveSpace Γ(Y, U) n :=
    H.lift ((π ⁻¹ᵁ U).ι ≫ i ≫ pullback.snd _ _) (π ∣_ U ≫ U.toSpecΓ) (by
      simp only [Category.assoc]
      rw [← pullback.condition, reassoc_of% hi, hsq, reassoc_of% (morphismRestrict_ι π U)])
  have hj : j ≫ projectiveSpaceStructure Γ(Y, U) n = π ∣_ U ≫ U.toSpecΓ := H.lift_snd _ _ _
  have hp : (π ⁻¹ᵁ U).ι ≫ i = j ≫ k := by
    apply pullback.hom_ext
    · rw [Category.assoc, hi, Category.assoc, pullback.lift_fst, ← Category.assoc, hj,
        Category.assoc, ← hU.isoSpec_hom, IsAffineOpen.isoSpec_hom_fromSpec,
        morphismRestrict_ι]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, H.lift_fst]
  have S₃ : IsPullback (π ⁻¹ᵁ U).ι j i k := by
    refine IsPullback.of_bot ?_ hp S₁
    rw [hj, hi]
    exact S₂
  have : IsClosedImmersion j := MorphismProperty.of_isPullback (P := @IsClosedImmersion) S₃
    inferInstance
  exact ⟨n, j, this, hj⟩

section Stein

variable (V) [IsDomain V] [ValuationRing V]

/-- **Stein finiteness for relatively projective morphisms, local form**: let
`pY : Y → Spec V` be locally of finite presentation over a valuation ring `V`, `π : B → Y`
projective relative to `pY` (`B ↪ Y ×_V ℙⁿ_V` over `Y`) with `B` flat over `V`. Then
`Γ(π⁻¹U, 𝒪_B)` is a finite `Γ(U, 𝒪_Y)`-module for every affine open `U ⊆ Y`. -/
theorem finite_sections_preimage_of_isRelativelyProjective [LocallyOfFinitePresentation pY]
    [Flat (π ≫ pY)] (hπ : DeJong.IsRelativelyProjective pY π) {U : Y.Opens}
    (hU : IsAffineOpen U) :
    letI := (π.app U).hom.toAlgebra
    Module.Finite Γ(Y, U) Γ(B, π ⁻¹ᵁ U) := by
  obtain ⟨n, i, hi, hcomp⟩ := hπ
  exact finite_sections_preimage_of_isProjectiveOver V π pY hU
    (isProjectiveOver_morphismRestrict_toSpecΓ π pY i hcomp hU)

/-- **Stein finiteness over a valuation ring** (blueprint `thm:sm-stein-finite-valuation`): let
`pY : Y → Spec V` be locally of finite presentation over a valuation ring `V` and `π : B → Y`
projective relative to `pY` (a closed immersion `B ↪ Y ×_V ℙⁿ_V` over `Y`, the form of
`TSM-PROJ`), with `B` flat over `V`. Then `π_* 𝒪_B` is a finite `𝒪_Y`-algebra: the relative
normalization `π.normalization = Spec π_* 𝒪_B` is finite over `Y`. -/
theorem isFinite_fromNormalization_of_isRelativelyProjective [LocallyOfFinitePresentation pY]
    [Flat (π ≫ pY)] [QuasiCompact π] [QuasiSeparated π] (hπ : DeJong.IsRelativelyProjective pY π) :
    IsFinite π.fromNormalization :=
  isFinite_fromNormalization π fun _ hU =>
    finite_sections_preimage_of_isRelativelyProjective V π pY hπ hU

end Stein

end

end DeJongAlterations.StableModification.Cohomology
