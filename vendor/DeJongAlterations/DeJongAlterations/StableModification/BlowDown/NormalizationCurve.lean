/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.Normalization
import DeJongAlterations.StableModification.ValuationRing.Nagata

/-!
# The normalization `Spec π_* 𝒪_B` is a flat finitely presented curve with reduced closed fibre

This file continues `BlowDown.Normalization` (blueprint `lem:sm-bd-normalization-curve`,
`sm-blow-down.tex`): for a valuation ring `V`, `pY : Y → Spec V` locally of finite presentation
and `π : B → Y` projective relative to `pY` with `B` flat over `V`, the relative normalization
`N = π.normalization` (`= Spec π_* 𝒪_B` by Stein finiteness) is

* flat over `V` (`flat_normalization`): its sections over `ν⁻¹U` (`ν = π.fromNormalization`, `U`
  affine) are those of `B` over `π⁻¹U` (`toNormalization_appLE_bijective`), which have no
  `V`-torsion;
* locally of finite presentation over `V` (`locallyOfFinitePresentation_normalization`): they are
  finite over the finitely presented `Γ(U, 𝒪_Y)` and flat, hence finitely presented by
  Raynaud–Gruson for valuation rings (`ValuationRing.finitePresentation_of_finiteType_of_flat`);
* with reduced closed fibre if `B` has reduced closed fibre
  (`isReduced_closedFibre_normalization`), by lane COH3B's
  `Cohomology.isRadical_map_maximalIdeal_preimage_of_isReduced`.

This is the part of Temkin's Lemma 4.4.1(i) (M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), `semi-stable.tex` T:3089–3104: "`Nr(C)` is an `S`-curve with
geometrically reduced fibres") used in the blowing-down argument, for normalizations dominated by
a flat curve with reduced closed fibre, without the reduced fibre theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

namespace DeJongAlterations.StableModification.BlowDown

universe u

section General

variable {X Z : Scheme.{u}} {A : Type u} [CommRing A]

/-- The coefficients of `g ≫ p` on an open `W′ ≤ g⁻¹W` are those of `p` on `W` followed by
`g^♯ : Γ(Z, W) → Γ(X, W′)`. -/
theorem sectionsRingHom_comp_appLE (g : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of A)) (W : Z.Opens)
    (W' : X.Opens) (h : W' ≤ g ⁻¹ᵁ W) :
    Cohomology.sectionsRingHom (Cohomology.structureCoeff (g ≫ p)) (le_top : W' ≤ ⊤) =
      (g.appLE W W' h).hom.comp (Cohomology.sectionsRingHom (Cohomology.structureCoeff p)
        (le_top : W ≤ ⊤)) := by
  have hm : Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ g.appLE W W' h =
      g.appLE ⊤ W' (h.trans (g.preimage_mono le_top)) := by
    rw [Scheme.Hom.map_appLE]
  ext a
  simp only [Cohomology.sectionsRingHom, Cohomology.structureCoeff, RingHom.comp_apply,
    Scheme.Hom.comp_appTop]
  exact (congrArg (fun φ => φ.hom ((p.appTop).hom
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) hm).symm

end General

section ClosedFibreCover

set_option backward.isDefEq.respectTransparency false

variable {V : Type u} [CommRing V] [IsLocalRing V] {X : Scheme.{u}}

/-- **Reduced closed fibre from radical ideals on a cover**: if every point of `X` lies in an
affine open `W` with `𝔪 Γ(W, 𝒪_X)` radical, the closed fibre `X ×_V k` is reduced (the cover form
of `isReduced_closedFibre_of_isRadical`). -/
theorem isReduced_closedFibre_of_forall_exists_isRadical (p : X ⟶ Spec (CommRingCat.of V))
    (h : ∀ x : X, ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧
      (Ideal.map (Cohomology.sectionsRingHom (Cohomology.structureCoeff p) (le_top : W ≤ ⊤))
        (maximalIdeal V)).IsRadical) :
    IsReduced (pullback p (Spec.map (CommRingCat.ofHom (residue V)))) := by
  refine @isReduced_of_isReduced_stalk _ fun x => ?_
  obtain ⟨W, hW, hxW, hrad⟩ := h (Cohomology.bcFst (residue V) p x)
  have hW' : IsAffineOpen (Cohomology.bcFst (residue V) p ⁻¹ᵁ W) := hW.preimage _
  have hred := isReduced_sections_closedFibre p hW hrad
  let := TopCat.Presheaf.algebra_section_stalk
    (pullback p (Spec.map (CommRingCat.ofHom (residue V)))).presheaf
    (⟨x, hxW⟩ : (Cohomology.bcFst (residue V) p ⁻¹ᵁ W : Opens _))
  have := hW'.isLocalization_stalk ⟨x, hxW⟩
  have key : _root_.IsReduced
      ((pullback p (Spec.map (CommRingCat.ofHom (residue V)))).presheaf.stalk
        ((⟨x, hxW⟩ : (Cohomology.bcFst (residue V) p ⁻¹ᵁ W : Opens _)) : _)) :=
    isReduced_localizationPreserves (hW'.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl _ hred
  exact key

end ClosedFibreCover

section Sections

variable {B Y : Scheme.{u}} (π : B ⟶ Y) [QuasiCompact π] [QuasiSeparated π]

/-- `π⁻¹U ⊆ τ⁻¹(ν⁻¹U)` for `π = τ ≫ ν`, `τ = π.toNormalization`, `ν = π.fromNormalization`. -/
theorem preimage_le_toNormalization_preimage (U : Y.Opens) :
    π ⁻¹ᵁ U ≤ π.toNormalization ⁻¹ᵁ (π.fromNormalization ⁻¹ᵁ U) := by
  simp [← Scheme.Hom.comp_preimage]

set_option backward.isDefEq.respectTransparency false in
/-- **Sections of `Spec π_* 𝒪_B`**: over an affine open `U ⊆ Y` with `Γ(π⁻¹U, 𝒪_B)` integral
over `Γ(U, 𝒪_Y)`, the map `τ^♯ : Γ(N, ν⁻¹U) → Γ(B, π⁻¹U)` is bijective (the integral closure is
everything; `normalizationObjIso`). -/
theorem toNormalization_appLE_bijective {U : Y.Opens} (hU : IsAffineOpen U)
    (hint : letI := (π.app U).hom.toAlgebra; Algebra.IsIntegral Γ(Y, U) Γ(B, π ⁻¹ᵁ U)) :
    Function.Bijective (π.toNormalization.appLE (π.fromNormalization ⁻¹ᵁ U) (π ⁻¹ᵁ U)
      (preimage_le_toNormalization_preimage π U)).hom := by
  let := (π.app U).hom.toAlgebra
  rw [← π.normalizationObjIso_hom_val hU, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Bijective.comp ⟨Subtype.val_injective, fun r => ⟨⟨r, hint.isIntegral r⟩, rfl⟩⟩
    (ConcreteCategory.bijective_of_isIso _)

/-- The structure coefficients of `π ≫ pY` on `π⁻¹U` factor through those of the normalization
`ν ≫ pY` on `ν⁻¹U`. -/
theorem sectionsRingHom_toNormalization {A : Type u} [CommRing A]
    (pY : Y ⟶ Spec (CommRingCat.of A)) (U : Y.Opens) :
    Cohomology.sectionsRingHom (Cohomology.structureCoeff (π ≫ pY)) (le_top : π ⁻¹ᵁ U ≤ ⊤) =
      (π.toNormalization.appLE (π.fromNormalization ⁻¹ᵁ U) (π ⁻¹ᵁ U)
        (preimage_le_toNormalization_preimage π U)).hom.comp
        (Cohomology.sectionsRingHom (Cohomology.structureCoeff (π.fromNormalization ≫ pY))
          (le_top : π.fromNormalization ⁻¹ᵁ U ≤ ⊤)) := by
  have e : π.toNormalization ≫ π.fromNormalization ≫ pY = π ≫ pY := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
  rw [← e]
  exact sectionsRingHom_comp_appLE _ _ _ _ _

end Sections

section Valuation

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
variable {B Y : Scheme.{u}} (π : B ⟶ Y) (pY : Y ⟶ Spec (CommRingCat.of V))
  [QuasiCompact π] [QuasiSeparated π]

omit [QuasiCompact π] [QuasiSeparated π] in
/-- The sections of a flat `V`-scheme have no `V`-torsion, so they form a flat `V`-module. -/
theorem flat_sectionsRingHom [Flat (π ≫ pY)] (W : B.Opens) :
    (Cohomology.sectionsRingHom (Cohomology.structureCoeff (π ≫ pY)) (le_top : W ≤ ⊤)).Flat := by
  let := (Cohomology.sectionsRingHom (Cohomology.structureCoeff (π ≫ pY))
    (le_top : W ≤ ⊤)).toAlgebra
  change Module.Flat V Γ(B, W)
  rw [ValuationRing.flat_iff_forall_smul_eq_zero]
  intro c hc s hs
  rw [Algebra.smul_def] at hs
  refine Cohomology.eq_zero_of_mul_eq_zero_of_flat (π ≫ pY)
    (a := (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) ?_ s hs
  intro h0
  apply hc
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom h0
  rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at this

variable [LocallyOfFinitePresentation pY] [Flat (π ≫ pY)]

/-- Over an affine open `U ⊆ Y`, `τ^♯ : Γ(N, ν⁻¹U) → Γ(B, π⁻¹U)` is bijective when `π` is
projective relative to `pY` (Stein finiteness, lane COH3B). -/
theorem toNormalization_appLE_bijective_of_isRelativelyProjective
    (hπ : DeJong.IsRelativelyProjective pY π) {U : Y.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (π.toNormalization.appLE (π.fromNormalization ⁻¹ᵁ U) (π ⁻¹ᵁ U)
      (preimage_le_toNormalization_preimage π U)).hom := by
  let := (π.app U).hom.toAlgebra
  have := Cohomology.finite_sections_preimage_of_isRelativelyProjective V π pY hπ hU
  exact toNormalization_appLE_bijective π hU inferInstance

/-- On `ν⁻¹U`, the normalization is flat over `V`. -/
theorem flat_sectionsRingHom_normalization (hπ : DeJong.IsRelativelyProjective pY π)
    {U : Y.Opens} (hU : IsAffineOpen U) :
    (Cohomology.sectionsRingHom (Cohomology.structureCoeff (π.fromNormalization ≫ pY))
      (le_top : π.fromNormalization ⁻¹ᵁ U ≤ ⊤)).Flat := by
  have hbij := toNormalization_appLE_bijective_of_isRelativelyProjective π pY hπ hU
  have hB := flat_sectionsRingHom π pY (π ⁻¹ᵁ U)
  rw [sectionsRingHom_toNormalization] at hB
  let ψ := RingEquiv.ofBijective _ hbij
  have h := RingHom.Flat.comp hB (RingHom.Flat.of_bijective (f := ψ.symm.toRingHom)
    ψ.symm.bijective)
  convert h using 1
  ext a
  change _ = ψ.symm (ψ _)
  rw [RingEquiv.symm_apply_apply]

omit [IsDomain V] [ValuationRing V] [LocallyOfFinitePresentation pY] [Flat (π ≫ pY)] in
/-- The ring map `Γ(Spec V, ⊤) → Γ(X, W)` of `p : X → Spec V` is the structure coefficient map
`V → Γ(X, W)` after the identification `Γ(Spec V, ⊤) = V`. -/
theorem appLE_eq_sectionsRingHom {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of V))
    (W : X.Opens) (e : W ≤ p ⁻¹ᵁ ⊤) :
    (p.appLE ⊤ W e).hom = (Cohomology.sectionsRingHom (Cohomology.structureCoeff p)
      (le_top : W ≤ ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom := by
  ext a
  simp only [Cohomology.sectionsRingHom, Cohomology.structureCoeff, RingHom.comp_apply,
    Scheme.Hom.appLE]
  rw [← CommRingCat.comp_apply ((Scheme.ΓSpecIso (CommRingCat.of V)).hom),
    Iso.hom_inv_id, CommRingCat.id_apply]
  rfl

/-- **The normalization `Spec π_* 𝒪_B` is flat over `V`** (blueprint
`lem:sm-bd-normalization-curve`). -/
theorem flat_normalization (hπ : DeJong.IsRelativelyProjective pY π) :
    Flat (π.fromNormalization ≫ pY) := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @Flat)
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).left]
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := π.fromNormalization x) (U := ⊤) trivial
  have e : π.fromNormalization ⁻¹ᵁ U ≤ (π.fromNormalization ≫ pY) ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_top]
    exact le_top
  refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨π.fromNormalization ⁻¹ᵁ U, hU.preimage _⟩, hxU, e, ?_⟩
  show ((π.fromNormalization ≫ pY).appLE ⊤ (π.fromNormalization ⁻¹ᵁ U) e).hom.Flat
  rw [appLE_eq_sectionsRingHom]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).hom))
    (flat_sectionsRingHom_normalization π pY hπ hU)

/-- **The normalization `Spec π_* 𝒪_B` is locally of finite presentation over `V`** (blueprint
`lem:sm-bd-normalization-curve`): on `ν⁻¹U` it is finite over the finitely presented
`Γ(U, 𝒪_Y)` and flat over `V`. -/
theorem locallyOfFinitePresentation_normalization (hπ : DeJong.IsRelativelyProjective pY π) :
    LocallyOfFinitePresentation (π.fromNormalization ≫ pY) := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).left]
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := π.fromNormalization x) (U := ⊤) trivial
  have e : π.fromNormalization ⁻¹ᵁ U ≤ (π.fromNormalization ≫ pY) ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_top]
    exact le_top
  refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨π.fromNormalization ⁻¹ᵁ U, hU.preimage _⟩, hxU, e, ?_⟩
  show ((π.fromNormalization ≫ pY).appLE ⊤ (π.fromNormalization ⁻¹ᵁ U) e).hom.FinitePresentation
  rw [appLE_eq_sectionsRingHom]
  refine RingHom.finitePresentation_stableUnderComposition _ _
    (RingHom.FinitePresentation.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).hom)) ?_
  -- finite type: `V → Γ(U) → Γ(N, ν⁻¹U)` with the second map finite
  have h1 : (Cohomology.sectionsRingHom (Cohomology.structureCoeff pY)
      (le_top : U ≤ ⊤)).FiniteType := by
    have e' : U ≤ pY ⁻¹ᵁ ⊤ := by
      rw [Scheme.Hom.preimage_top]
      exact le_top
    have h := HasRingHomProperty.appLE @LocallyOfFinitePresentation pY inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ e'
    change (pY.appLE ⊤ U e').hom.FinitePresentation at h
    rw [appLE_eq_sectionsRingHom] at h
    have h' := RingHom.FiniteType.of_finitePresentation h
    have := RingHom.FiniteType.comp h' (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv).2)
    convert this using 1
    ext a
    simp only [RingHom.comp_apply]
    rw [← CommRingCat.comp_apply ((Scheme.ΓSpecIso (CommRingCat.of V)).inv),
      Iso.inv_hom_id, CommRingCat.id_apply]
  have h2 : (π.fromNormalization.app U).hom.Finite := by
    let := (π.app U).hom.toAlgebra
    have := Cohomology.finite_sections_preimage_of_isRelativelyProjective V π pY hπ hU
    rw [Scheme.Hom.fromNormalization_app π hU, CommRingCat.hom_comp]
    refine RingHom.Finite.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (π.normalizationObjIso hU).inv).2) ?_
    rw [CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
    exact Module.Finite.equiv ((Subalgebra.equivOfEq _ _
      (Cohomology.integralClosure_eq_top_of_finite)).trans Subalgebra.topEquiv).toLinearEquiv.symm
  have hft : (Cohomology.sectionsRingHom (Cohomology.structureCoeff (π.fromNormalization ≫ pY))
      (le_top : π.fromNormalization ⁻¹ᵁ U ≤ ⊤)).FiniteType := by
    rw [sectionsRingHom_comp]
    exact RingHom.FiniteType.comp h2.to_finiteType h1
  let := (Cohomology.sectionsRingHom (Cohomology.structureCoeff (π.fromNormalization ≫ pY))
      (le_top : π.fromNormalization ⁻¹ᵁ U ≤ ⊤)).toAlgebra
  have : Algebra.FiniteType V Γ(π.normalization, π.fromNormalization ⁻¹ᵁ U) := hft
  have : Module.Flat V Γ(π.normalization, π.fromNormalization ⁻¹ᵁ U) :=
    flat_sectionsRingHom_normalization π pY hπ hU
  exact ValuationRing.finitePresentation_of_finiteType_of_flat

/-- **Radical closed-fibre ideals on the normalization**: `𝔪 Γ(N, ν⁻¹U)` is radical for every
affine open `U ⊆ Y` when `B` has reduced closed fibre (transport of lane COH3B's
`Cohomology.isRadical_map_maximalIdeal_preimage_of_isReduced` along
`τ^♯ : Γ(N, ν⁻¹U) ≅ Γ(B, π⁻¹U)`). -/
theorem isRadical_map_maximalIdeal_normalization
    [IsReduced (pullback (π ≫ pY) (Spec.map (CommRingCat.ofHom (residue V))))]
    (hπ : DeJong.IsRelativelyProjective pY π) {U : Y.Opens} (hU : IsAffineOpen U) :
    (Ideal.map (Cohomology.sectionsRingHom (Cohomology.structureCoeff (π.fromNormalization ≫ pY))
      (le_top : π.fromNormalization ⁻¹ᵁ U ≤ ⊤)) (maximalIdeal V)).IsRadical := by
  have hbij := toNormalization_appLE_bijective_of_isRelativelyProjective π pY hπ hU
  have hrad := Cohomology.isRadical_map_maximalIdeal_preimage_of_isReduced π pY hU.isCompact
  rw [sectionsRingHom_toNormalization, ← Ideal.map_map] at hrad
  let ψ := RingEquiv.ofBijective _ hbij
  have hcomap := hrad.comap ψ.toRingHom
  have key := Ideal.comap_map_of_bijective (f := ψ.toRingHom) ψ.bijective
    (I := Ideal.map (Cohomology.sectionsRingHom
      (Cohomology.structureCoeff (π.fromNormalization ≫ pY))
      (le_top : π.fromNormalization ⁻¹ᵁ U ≤ ⊤)) (maximalIdeal V))
  rw [← key]
  exact hcomap

/-- **The normalization `Spec π_* 𝒪_B` has reduced closed fibre** (blueprint
`lem:sm-bd-normalization-curve`) when `B` has: the affine opens `ν⁻¹U` cover `N` and have radical
closed-fibre ideals (`isRadical_map_maximalIdeal_normalization`). -/
theorem isReduced_closedFibre_normalization
    [IsReduced (pullback (π ≫ pY) (Spec.map (CommRingCat.ofHom (residue V))))]
    (hπ : DeJong.IsRelativelyProjective pY π) :
    IsReduced (pullback (π.fromNormalization ≫ pY) (Spec.map (CommRingCat.ofHom (residue V)))) :=
  isReduced_closedFibre_of_forall_exists_isRadical _ fun x => by
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
      (x := π.fromNormalization x) (U := ⊤) trivial
    exact ⟨_, hU.preimage _, hxU, isRadical_map_maximalIdeal_normalization π pY hπ hU⟩

end Valuation

end DeJongAlterations.StableModification.BlowDown
