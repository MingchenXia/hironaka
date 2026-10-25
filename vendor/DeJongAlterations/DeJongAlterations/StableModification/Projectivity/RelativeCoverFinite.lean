/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3C)
-/
import DeJongAlterations.StableModification.Projectivity.RelativeGenerated
import DeJongAlterations.StableModification.Projectivity.RelativeFinite
import DeJongAlterations.StableModification.Cohomology.SteinProjective
import DeJongAlterations.StableModification.Cohomology.SteinCoherent
import DeJongAlterations.StableModification.Cohomology.FiniteProjective
import DeJongAlterations.StableModification.CurvesField.AmpleSection

/-!
# Finiteness of the cokernels of the two-term complexes (`lem:sm-ltg-two-cech`)

Blueprint `sm-projectivity-relative.tex`, `lem:sm-ltg-two-cech` (PLAN-OM3 §3 step 1). Let
`β : X ⟶ Y`, `W ⊆ Y` affine with `β⁻¹ W` projective over `Γ(Y, W)`, and `U₀ ∪ U₁ = β⁻¹ W` two
affines with affine intersection. Then the cokernel of the difference map
`Γ(U₀, 𝓛^m) × Γ(U₁, 𝓛^m) → Γ(U₀ ∩ U₁, 𝓛^m)` is a finite `Γ(Y, W)`-module:

* `finite_coker_of_pullback`: it is the cokernel of the same map on the open subscheme `β⁻¹ W`
  (pullback of sections along the open immersion, `pullbackLinW`), i.e. `Ȟ¹` of the pair cover
  of `β⁻¹ W` (`RelativeCech.finite_coker_pairDiff`);
* `finite_coker_of_noetherian`: if `Γ(Y, W)` is Noetherian, `Ȟ¹` is finite (Codex's
  `Cohomology.finite_cohomology_of_isProjectiveOver`, Hartshorne III.5.2);
* `finite_coker_of_valuationRing`: if `Y` is locally of finite presentation over a valuation ring
  `V` and `X` is flat over `V`, `Ȟ¹` is finitely presented (Codex's
  `Cohomology.ProjectiveCoordinates.finitePresentation_cechCohomology_fp`; the sections of `𝓛^m`
  on the charts are finite, `finite_twist_sections`, and have no `V`-torsion,
  `Sections.eq_zero_of_smul_eq_zero` with `Cohomology.eq_zero_of_mul_eq_zero_of_flat`).

These assemble to `TwoAffineCover`s in both cases (`twoAffineCover_of_noetherian`,
`twoAffineCover_of_valuationRing`).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Cohomology

variable {X Y : Scheme.{u}} (β : X ⟶ Y) (L : LineBundleData X) (m : ℤ) (W : Y.Opens)

/-- The coefficient map `Γ(Y, W) → Γ(β⁻¹ W, ⊤)` (the structure coefficients of
`β⁻¹ W ⟶ Spec Γ(Y, W)`, Codex's `structureCoeff_morphismRestrict_toSpecΓ`). -/
abbrev coeffW : Γ(Y, W) →+* Γ((β ⁻¹ᵁ W).toScheme, ⊤) :=
  ((β ⁻¹ᵁ W).topIso.inv.hom).comp (β.app W).hom

variable {W}

lemma app_res_topIso {V : X.Opens} (hV : V ≤ β ⁻¹ᵁ W) (r : Γ(X, β ⁻¹ᵁ W)) :
    (β ⁻¹ᵁ W).ι.app V (res hV r) =
      res (le_top : (β ⁻¹ᵁ W).ι ⁻¹ᵁ V ≤ ⊤) ((β ⁻¹ᵁ W).topIso.inv r) := by
  simp only [Scheme.Opens.ι_app, Scheme.Opens.topIso_inv, res]
  change (X.presheaf.map _ ≫ X.presheaf.map _) r = (X.presheaf.map _ ≫ X.presheaf.map _) r
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- Pullback of sections to `β⁻¹ W` as a `Γ(Y, W)`-linear map. -/
def pullbackLinWMap {V : X.Opens} (hV : V ≤ β ⁻¹ᵁ W) :
    sectionsModuleCat (L.twist (unitModule X) m) (β.app W).hom V hV →ₗ[Γ(Y, W)]
      sectionsModuleCat ((L.pullback (β ⁻¹ᵁ W).ι).twist (unitModule (β ⁻¹ᵁ W).toScheme) m)
        (coeffW β W) ((β ⁻¹ᵁ W).ι ⁻¹ᵁ V) le_top where
  toFun s := LineBundleData.Sections.pullback (β ⁻¹ᵁ W).ι (L := L) (m := m) s
  map_add' s t := LineBundleData.Sections.pullback_add L m _ s t
  map_smul' a s := by
    change LineBundleData.Sections.pullback (β ⁻¹ᵁ W).ι
        (res hV (β.app W a) • (show L.Sections m V from s)) =
      res (le_top : (β ⁻¹ᵁ W).ι ⁻¹ᵁ V ≤ ⊤) (coeffW β W a) •
        LineBundleData.Sections.pullback (β ⁻¹ᵁ W).ι (show L.Sections m V from s)
    rw [LineBundleData.Sections.pullback_smul, app_res_topIso]
    rfl

/-- **Pullback of sections to `β⁻¹ W`** as a `Γ(Y, W)`-linear equivalence. -/
def pullbackLinW {V : X.Opens} (hV : V ≤ β ⁻¹ᵁ W) :
    sectionsModuleCat (L.twist (unitModule X) m) (β.app W).hom V hV ≃ₗ[Γ(Y, W)]
      sectionsModuleCat ((L.pullback (β ⁻¹ᵁ W).ι).twist (unitModule (β ⁻¹ᵁ W).toScheme) m)
        (coeffW β W) ((β ⁻¹ᵁ W).ι ⁻¹ᵁ V) le_top :=
  LinearEquiv.ofBijective (pullbackLinWMap β L m hV)
    (L.bijective_pullback_of_isOpenImmersion m (β ⁻¹ᵁ W).ι
      (by rw [Scheme.Opens.opensRange_ι]; exact hV))

lemma pullbackLinW_apply {V : X.Opens} (hV : V ≤ β ⁻¹ᵁ W) (s : L.Sections m V) :
    pullbackLinW β L m hV s = s.pullback (β ⁻¹ᵁ W).ι :=
  rfl

lemma pullbackLinW_map {V V' : X.Opens} (hV : V ≤ β ⁻¹ᵁ W) (hV' : V' ≤ β ⁻¹ᵁ W) (h : V' ≤ V)
    (s : sectionsModuleCat (L.twist (unitModule X) m) (β.app W).hom V hV) :
    pullbackLinW β L m hV' ((L.twist (unitModule X) m).presheaf.map (homOfLE h).op s) =
      ((L.pullback (β ⁻¹ᵁ W).ι).twist (unitModule (β ⁻¹ᵁ W).toScheme) m).presheaf.map
        (homOfLE ((β ⁻¹ᵁ W).ι.preimage_mono h)).op (pullbackLinW β L m hV s) :=
  LineBundleData.Sections.pullback_restrict L m _ h s

/-- **The cokernel on `X` is the cokernel on `β⁻¹ W`** (blueprint `lem:sm-ltg-two-cech`). -/
theorem finite_coker_of_pullback {U₀ U₁ : X.Opens} (hcov : U₀ ⊔ U₁ = β ⁻¹ᵁ W)
    (h : Module.Finite Γ(Y, W)
      (sectionsModuleCat ((L.pullback (β ⁻¹ᵁ W).ι).twist (unitModule (β ⁻¹ᵁ W).toScheme) m)
          (coeffW β W) ((β ⁻¹ᵁ W).ι ⁻¹ᵁ U₀ ⊓ (β ⁻¹ᵁ W).ι ⁻¹ᵁ U₁) le_top ⧸
        LinearMap.range (pairDiff ((β ⁻¹ᵁ W).ι ⁻¹ᵁ U₀) ((β ⁻¹ᵁ W).ι ⁻¹ᵁ U₁)
          ((L.pullback (β ⁻¹ᵁ W).ι).twist (unitModule (β ⁻¹ᵁ W).toScheme) m) (coeffW β W)))) :
    Module.Finite Γ(Y, W)
      (sectionsModuleCat (L.twist (unitModule X) m) (β.app W).hom (U₀ ⊓ U₁)
          (inf_le_left.trans (LineBundleData.le_of_sup_eq₀ β hcov)) ⧸
        LinearMap.range (pairDiffOn (L.twist (unitModule X) m) (β.app W).hom
          (LineBundleData.le_of_sup_eq₀ β hcov) (LineBundleData.le_of_sup_eq₁ β hcov))) := by
  have hU₀ := LineBundleData.le_of_sup_eq₀ β hcov
  have hU₁ := LineBundleData.le_of_sup_eq₁ β hcov
  have hU₀₁ : U₀ ⊓ U₁ ≤ β ⁻¹ᵁ W := inf_le_left.trans hU₀
  let e₀ := (pullbackLinW β L m hU₀).prodCongr (pullbackLinW β L m hU₁)
  let e₁ := pullbackLinW β L m hU₀₁
  let d := pairDiffOn (L.twist (unitModule X) m) (β.app W).hom hU₀ hU₁
  let d' := pairDiff ((β ⁻¹ᵁ W).ι ⁻¹ᵁ U₀) ((β ⁻¹ᵁ W).ι ⁻¹ᵁ U₁)
    ((L.pullback (β ⁻¹ᵁ W).ι).twist (unitModule (β ⁻¹ᵁ W).toScheme) m) (coeffW β W)
  have hcomm : e₁.toLinearMap ∘ₗ d = d' ∘ₗ e₀.toLinearMap := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, d, d', e₀, e₁,
      pairDiffOn_apply, map_sub]
    rw [pullbackLinW_map β L m hU₁ hU₀₁ inf_le_right, pullbackLinW_map β L m hU₀ hU₀₁ inf_le_left]
    rfl
  have hrange : (LinearMap.range d).map e₁.toLinearMap = LinearMap.range d' := by
    rw [← LinearMap.range_comp, hcomm, LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.mpr e₀.surjective
  exact Module.Finite.equiv (Submodule.Quotient.equiv _ _ e₁ hrange).symm

/-! ### The two cases -/

section Cases

variable {β} {U₀ U₁ : X.Opens} (h₀ : IsAffineOpen U₀) (h₁ : IsAffineOpen U₁)
  (h₀₁ : IsAffineOpen (U₀ ⊓ U₁)) (hcov : U₀ ⊔ U₁ = β ⁻¹ᵁ W)

include h₀ h₁ h₀₁ hcov in
/-- The pair cover of `β⁻¹ W` by the preimages of `U₀`, `U₁`. -/
lemma isAffine_pair :
    IsAffineOpen ((β ⁻¹ᵁ W).ι ⁻¹ᵁ U₀) ∧ IsAffineOpen ((β ⁻¹ᵁ W).ι ⁻¹ᵁ U₁) ∧
      IsAffineOpen ((β ⁻¹ᵁ W).ι ⁻¹ᵁ U₀ ⊓ (β ⁻¹ᵁ W).ι ⁻¹ᵁ U₁) ∧
        (β ⁻¹ᵁ W).ι ⁻¹ᵁ U₀ ⊔ (β ⁻¹ᵁ W).ι ⁻¹ᵁ U₁ = ⊤ := by
  have hU₀ := LineBundleData.le_of_sup_eq₀ β hcov
  have hU₁ := LineBundleData.le_of_sup_eq₁ β hcov
  have hr : (β ⁻¹ᵁ W).ι.opensRange = β ⁻¹ᵁ W := Scheme.Opens.opensRange_ι _
  refine ⟨h₀.preimage_of_isOpenImmersion _ (by rw [hr]; exact hU₀),
    h₁.preimage_of_isOpenImmersion _ (by rw [hr]; exact hU₁),
    h₀₁.preimage_of_isOpenImmersion _ (by rw [hr]; exact inf_le_left.trans hU₀), ?_⟩
  rw [← Scheme.Hom.preimage_sup, hcov]
  exact Scheme.Opens.ι_preimage_self _

include h₀ h₁ h₀₁ hcov in
/-- **Finiteness, Noetherian case** (blueprint `lem:sm-ltg-two-cech`). -/
theorem finite_coker_of_noetherian [IsNoetherianRing Γ(Y, W)]
    (hp : IsProjectiveOver (k := Γ(Y, W)) (β ∣_ W ≫ W.toSpecΓ)) (m : ℤ) :
    Module.Finite Γ(Y, W)
      (sectionsModuleCat (L.twist (unitModule X) m) (β.app W).hom (U₀ ⊓ U₁)
          (inf_le_left.trans (LineBundleData.le_of_sup_eq₀ β hcov)) ⧸
        LinearMap.range (pairDiffOn (L.twist (unitModule X) m) (β.app W).hom
          (LineBundleData.le_of_sup_eq₀ β hcov) (LineBundleData.le_of_sup_eq₁ β hcov))) := by
  obtain ⟨a₀, a₁, a₀₁, acov⟩ := isAffine_pair h₀ h₁ h₀₁ hcov
  have : IsProper (β ∣_ W ≫ W.toSpecΓ) := hp.isProper
  have : CompactSpace (β ⁻¹ᵁ W).toScheme :=
    CurvesField.Ample.compactSpace_of_quasiCompact (β ∣_ W ≫ W.toSpecΓ)
  have : IsAffineHom (pullback.diagonal (terminal.from (β ⁻¹ᵁ W).toScheme)) :=
    CurvesField.Ample.isAffineHom_diagonal_of_isSeparated (β ∣_ W ≫ W.toSpecΓ)
  set F := (L.pullback (β ⁻¹ᵁ W).ι).twist (unitModule (β ⁻¹ᵁ W).toScheme) m
  have hfin := finite_cohomology_of_isProjectiveOver hp F
    (fun U hU => (L.pullback (β ⁻¹ᵁ W).ι).finite_twist_sections m hU) 1
  rw [structureCoeff_morphismRestrict_toSpecΓ] at hfin
  have : Module.Finite Γ(Y, W) (cechCohomology F (pairOpens ((β ⁻¹ᵁ W).ι ⁻¹ᵁ U₀)
      ((β ⁻¹ᵁ W).ι ⁻¹ᵁ U₁)) (coeffW β W) 1) :=
    Module.Finite.equiv (cohomologyIsoCech F (coeffW β W)
      (pairCover _ _ a₀ a₁ a₀₁ acov) 1).toLinearEquiv
  exact finite_coker_of_pullback β L m hcov (finite_coker_pairDiff _ _ F (coeffW β W))

include h₀ h₁ h₀₁ hcov in
/-- **Finiteness, valuation case** (blueprint `lem:sm-ltg-two-cech`): over a scheme locally of
finite presentation over a valuation ring `V`, with `X` flat over `V`. -/
theorem finite_coker_of_valuationRing (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
    (pY : Y ⟶ Spec (CommRingCat.of V)) [LocallyOfFinitePresentation pY] [Flat (β ≫ pY)]
    (hW : IsAffineOpen W) (hp : IsProjectiveOver (k := Γ(Y, W)) (β ∣_ W ≫ W.toSpecΓ)) (m : ℤ) :
    Module.Finite Γ(Y, W)
      (sectionsModuleCat (L.twist (unitModule X) m) (β.app W).hom (U₀ ⊓ U₁)
          (inf_le_left.trans (LineBundleData.le_of_sup_eq₀ β hcov)) ⧸
        LinearMap.range (pairDiffOn (L.twist (unitModule X) m) (β.app W).hom
          (LineBundleData.le_of_sup_eq₀ β hcov) (LineBundleData.le_of_sup_eq₁ β hcov))) := by
  obtain ⟨a₀, a₁, a₀₁, acov⟩ := isAffine_pair h₀ h₁ h₀₁ hcov
  have : IsProper (β ∣_ W ≫ W.toSpecΓ) := hp.isProper
  have : CompactSpace (β ⁻¹ᵁ W).toScheme :=
    CurvesField.Ample.compactSpace_of_quasiCompact (β ∣_ W ≫ W.toSpecΓ)
  have : IsAffineHom (pullback.diagonal (terminal.from (β ⁻¹ᵁ W).toScheme)) :=
    CurvesField.Ample.isAffineHom_diagonal_of_isSeparated (β ∣_ W ≫ W.toSpecΓ)
  let alg : Algebra V Γ(Y, W) := sectionsAlgebra V pY W
  have : Algebra.FinitePresentation V Γ(Y, W) := finitePresentation_sectionsAlgebra V pY hW
  obtain ⟨D⟩ := nonempty_projectiveCoordinates_of_isProjectiveOver hp
  set F := (L.pullback (β ⁻¹ᵁ W).ι).twist (unitModule (β ⁻¹ᵁ W).toScheme) m
  have hF : ∀ i, Module.Finite Γ((β ⁻¹ᵁ W).toScheme, D.U i) Γ(F, D.U i) := fun i =>
    (L.pullback (β ⁻¹ᵁ W).ι).finite_twist_sections m (D.isAffineOpen i)
  have key : ∀ v : V, ((β ⁻¹ᵁ W).ι ≫ β ≫ pY).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v) =
      structureCoeff (A := Γ(Y, W)) (β ∣_ W ≫ W.toSpecΓ) (algebraMap V Γ(Y, W) v) := by
    intro v
    rw [structureCoeff_morphismRestrict_toSpecΓ]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
      Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv, RingHom.algebraMap_toAlgebra,
      sectionsRingHom, structureCoeff]
    have hnat := congrArg (fun g => g.hom (pY.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v)))
      (β.naturality (homOfLE (le_top : W ≤ ⊤)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
    erw [hnat, ← CommRingCat.comp_apply (X.presheaf.map _) (X.presheaf.map _),
      ← Functor.map_comp]
    rfl
  have htf : ∀ i, ∀ v : V, v ≠ 0 → ∀ s : Γ(F, D.U i),
      D.const i (algebraMap V Γ(Y, W) v) • s = 0 → s = 0 := by
    intro i v hv s hs
    refine LineBundleData.Sections.eq_zero_of_smul_eq_zero (L.pullback (β ⁻¹ᵁ W).ι) m
      (D.const i (algebraMap V Γ(Y, W) v)) (fun V' hV' f hf => ?_) s hs
    refine eq_zero_of_mul_eq_zero_of_flat ((β ⁻¹ᵁ W).ι ≫ β ≫ pY)
      (a := (Scheme.ΓSpecIso (CommRingCat.of V)).inv v) ?_ f ?_
    · intro h0
      apply hv
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom h0
      simpa using this
    · rw [key]
      refine Eq.trans ?_ hf
      congr 1
      exact (res_res _ _ _ _).symm
  have hfp := D.finitePresentation_cechCohomology_fp V F hF htf 1
  have h1 : Module.Finite Γ(Y, W) (cechCohomology F (pairOpens ((β ⁻¹ᵁ W).ι ⁻¹ᵁ U₀)
      ((β ⁻¹ᵁ W).ι ⁻¹ᵁ U₁)) (structureCoeff (A := Γ(Y, W)) (β ∣_ W ≫ W.toSpecΓ)) 1) :=
    Module.Finite.equiv (cechCohomologyIsoOfAffineCovers F _ D.iSup_eq_top
      (pairCover _ _ a₀ a₁ a₀₁ acov).iSup_eq_top D.isAffineOpen
      (pairCover _ _ a₀ a₁ a₀₁ acov).isAffineOpen 1).toLinearEquiv
  rw [structureCoeff_morphismRestrict_toSpecΓ] at h1
  exact finite_coker_of_pullback β L m hcov (finite_coker_pairDiff _ _ F (coeffW β W))

end Cases

end

end DeJongAlterations.StableModification.Projectivity
