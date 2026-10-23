/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Omega.Invertible
import DeJongAlterations.StableModification.Omega.PoleChartAlgebra
import DeJongAlterations.StableModification.Omega.RosenlichtComponentSmooth

/-!
# Étale node charts at the non-smooth points, with the generator of `ω`

Blueprint `sm-omega-component-degree.tex`, `lem:sm-omega-cd-etale-chart` and
`lem:sm-omega-cd-generator-relation` (the first two steps of the proof of
`lem:sm-omega-bcf-pole-chart`). Let `f : X ⟶ S` be a nodal curve over an integral, normal,
locally Noetherian scheme, smooth over the generic point, and `x ∉ Sm f`.

* `exists_etaleNodeChart_of_not_mem_smoothLocus`: for affine opens `x ∈ W ⊆ f⁻¹ V` there are an
  étale `φ : Γ(X, W) → T₀`, an étale node chart of `Spec T₀ ⟶ X ⟶ S` on all of `Spec T₀`, and a
  basic open `x ∈ D(t) ⊆ W` inside the image of `Spec T₀` (the construction of
  `Omega.isInvertibleAt_dualizingSheaf_of_not_mem_smoothLocus`, lane OM1B, extracted here; SS3's
  `Curves.SemistableNormal.exists_away_etale_nodeChart`, Stacks Tag 0CBY).

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §1.2
(`semi-stable.tex`, T:1700–1712: "this is so étale-locally, where `X` is `R[u,v]/(uv − h)`").
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
open DeJongAlterations.Algebra.NodeBlowupChart

universe u

namespace DeJongAlterations.StableModification.Omega.PoleChart

open Curves.SemistableOpen Curves.SemistableNormal Curves
open DeJong (IsNodalCurve IsSmoothAt)

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Curves.SemistableOpen.locallyOfFinitePresentation_spec

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **An étale node chart at a non-smooth point** (blueprint `lem:sm-omega-cd-etale-chart`). Let
`f` be a nodal curve over an integral, normal, locally Noetherian scheme, smooth over the generic
point, `x ∉ Sm f`, and `x ∈ W ⊆ f⁻¹ V` affine. Then there are an étale `φ : Γ(X, W) → T₀`, an
étale node chart of `ψ ≫ f` on `Spec T₀` (`ψ = Spec φ ≫ (W ⊆ X)`), and `t ∈ Γ(X, W)` with
`x ∈ D(t) ⊆ ψ(Spec T₀)`. -/
theorem exists_etaleNodeChart_of_not_mem_smoothLocus {X S : Scheme.{u}} (f : X ⟶ S)
    [IsNodalCurve f] [IsIntegral S] [IsLocallyNoetherian S] (hS : IsNormalScheme S)
    (hgen : ∀ x : X, f x = genericPoint S → IsSmoothAt f x)
    {x : X} (hx : x ∉ f.smoothLocus) {V : S.Opens} (hV : IsAffineOpen V) {W : X.Opens}
    (hW : IsAffineOpen W) (hle : W ≤ f ⁻¹ᵁ V) (hxW : x ∈ W) :
    ∃ (T₀ : Type u) (_ : CommRing T₀) (φ : Γ(X, W) →+* T₀) (_ : φ.Etale)
      (_ : EtaleNodeChart ((Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec) ≫ f) V ⊤)
      (t : Γ(X, W)), x ∈ X.basicOpen t ∧
        (X.basicOpen t : Set X) ⊆ Set.range (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec) := by
  have hxV : f x ∈ V := hle hxW
  let : Algebra Γ(S, V) Γ(X, W) := (f.appLE V W hle).hom.toAlgebra
  have : Module.Flat Γ(S, V) Γ(X, W) :=
    HasRingHomProperty.appLE @Flat f inferInstance ⟨V, hV⟩ ⟨W, hW⟩ hle
  have : Algebra.FinitePresentation Γ(S, V) Γ(X, W) :=
    HasRingHomProperty.appLE @LocallyOfFinitePresentation f inferInstance ⟨V, hV⟩ ⟨W, hW⟩ hle
  have hsq : hW.fromSpec ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W))) ≫ hV.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hle).symm
  set 𝔭 := hW.primeIdealOf ⟨x, hxW⟩
  have hx𝔭 : hW.fromSpec 𝔭 = x := hW.fromSpec_primeIdealOf ⟨x, hxW⟩
  obtain ⟨K, _, _, _, z, hzmax, hz𝔭⟩ := exists_geometricPoint (R := Γ(S, V)) 𝔭.asIdeal
  set a : Spec (.of K) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) K)) ≫ hV.fromSpec
  have ha : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) K)) ≫ hV.fromSpec = a := rfl
  set zp : PrimeSpectrum (K ⊗[Γ(S, V)] Γ(X, W)) := ⟨z, hzmax.isPrime⟩
  have hzc : IsClosed ({zp} : Set (Spec (.of (K ⊗[Γ(S, V)] Γ(X, W))))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hzmax
  set y := tensorChart f hsq ha zp
  have hyx : pullback.fst f a y = x := by
    rw [← jB_comap_eq f hsq ha zp]
    have : PrimeSpectrum.comap (algebraMap Γ(X, W) (K ⊗[Γ(S, V)] Γ(X, W))) zp = 𝔭 :=
      PrimeSpectrum.ext hz𝔭
    rw [this, hx𝔭]
  have hy : IsClosed ({y} : Set (pullback (C := Scheme.{u}) f a)) :=
    isClosed_image_of_isClosed (tensorChart f hsq ha) (tensorChart_snd f hsq ha) hzc
  rcases IsNodalCurve.geometricNodes (g := f) K a y hy with hs | hn
  · -- a smooth point of the geometric fibre: then `x` is smooth (the fibre criterion)
    exfalso
    apply hx
    have h := mem_smoothLocus_of_tensorChart_spec f hV hW hle K zp hzc hs
    have h𝔭 : PrimeSpectrum.comap (algebraMap Γ(X, W) (K ⊗[Γ(S, V)] Γ(X, W))) zp = 𝔭 :=
      PrimeSpectrum.ext hz𝔭
    rwa [h𝔭, hx𝔭] at h
  · -- a node of the geometric fibre: SS3's étale chart
    have hzn := isGeometricOrdinaryDoublePoint_of_tensorChart f hsq ha zp hzc hn
    have hzn' : IsFormalNode K z := (isGeometricOrdinaryDoublePoint_spec_iff zp).mp hzn
    obtain ⟨f₀, hf₀, hchart⟩ := exists_away_etale_nodeChart z hzn'
    have hsq₁ := localization_chart_sq f hsq f₀
    have hxB₁ : pullback.fst f a y ∈ Set.range
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) (Localization.Away f₀))) ≫
          hW.fromSpec) := by
      rw [hyx, ← hx𝔭]
      exact mem_range_localization_chart f₀ 𝔭 (hz𝔭 ▸ hf₀)
    obtain ⟨z₁, hz₁y, hz₁c⟩ := exists_tensorChart_eq f hsq₁ ha y hy hxB₁
    have : z₁.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal z₁).mp hz₁c
    have : Module.Flat Γ(S, V) (Localization.Away f₀) := Module.Flat.trans _ Γ(X, W) _
    have : Algebra.FinitePresentation Γ(S, V) (Localization.Away f₀) :=
      Algebra.FinitePresentation.trans _ Γ(X, W) _
    have hz₁n := isGeometricOrdinaryDoublePoint_of_tensorChart f hsq₁ ha z₁ hz₁c (hz₁y ▸ hn)
    have hz₁n' : IsFormalNode K z₁.asIdeal := (isGeometricOrdinaryDoublePoint_spec_iff z₁).mp hz₁n
    obtain ⟨O, _, _, _, c, Wa, _, _, _, _, _, 𝔔, _, h𝔔, hcompat, hcoord, hc𝔔⟩ :=
      hchart K z₁.asIdeal hz₁n'
    -- the prime of `Γ(X, W)` under `𝔔` is the point `x`
    have hxz₁ := jB_comap_eq f hsq₁ ha z₁
    rw [hz₁y, hyx, ← hx𝔭, Scheme.Hom.comp_apply] at hxz₁
    have hz₁𝔭 := hW.fromSpec.isOpenEmbedding.injective hxz₁
    -- the étale map `Γ(X, W) → Wa`
    let φ : Γ(X, W) →+* Wa := (algebraMap (Localization.Away f₀) Wa).comp
      (algebraMap Γ(X, W) (Localization.Away f₀))
    have hφ : φ.Etale := RingHom.Etale.stableUnderComposition _ _
      (RingHom.etale_algebraMap.mpr inferInstance) (RingHom.etale_algebraMap.mpr inferInstance)
    let x₀ : PrimeSpectrum Wa := ⟨𝔔, inferInstance⟩
    have hcomap : PrimeSpectrum.comap φ x₀ = 𝔭 := by
      ext1
      change Ideal.comap ((algebraMap (Localization.Away f₀) Wa).comp
        (algebraMap Γ(X, W) (Localization.Away f₀))) 𝔔 = 𝔭.asIdeal
      rw [← Ideal.comap_comap, h𝔔]
      exact congrArg PrimeSpectrum.asIdeal hz₁𝔭
    -- `Spec Wa` is normal
    let ψ₀ : Spec (CommRingCat.of Wa) ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec
    have : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.mpr hφ
    have : IsNodalCurve (ψ₀ ≫ f) := IsNodalCurve.etale_comp ψ₀ f
    have hgen₀ : ∀ y, (ψ₀ ≫ f) y = genericPoint S → IsSmoothAt (ψ₀ ≫ f) y := fun y hy =>
      isSmoothAt_comp (isSmoothAt_of_smooth ψ₀ y) (hgen (ψ₀ y) hy)
    obtain ⟨hdom, hic⟩ := isNormalScheme_of_isNodalCurve (ψ₀ ≫ f) hS hgen₀ x₀
    obtain ⟨hQ1, hQ2⟩ := isDomain_isIntegrallyClosed_of_ringEquiv
      (Spec.stalkIso (CommRingCat.of Wa) x₀).commRingCatIsoToRingEquiv ⟨hdom, hic⟩
    -- the node parameter is a non-zero-divisor near the point
    set P := 𝔔.comap (algebraMap (Node O c) Wa)
    have hP := Curves.SemistableNormal.isDomain_isIntegrallyClosed_localization_of_flat
      (B := Node O c) (W := Wa) 𝔔 P rfl
    have : IsDomain (Localization.AtPrime P) := hP.1
    have hcne := algebraMap_ne_zero_of_isDomain c P (hcoord 0) (hcoord 1)
    set 𝔮 := P.comap (algebraMap O (Node O c))
    have : Nonempty V := ⟨⟨f x, hxV⟩⟩
    have : IsDomain Γ(S, V) := IsIntegral.component_integral V
    have : IsIntegrallyClosed Γ(S, V) :=
      Geometry.NormalCurveModification.affineSections_isIntegrallyClosed hS V hV
    have hO := Curves.isDomain_isIntegrallyClosed_localization_of_etale Γ(S, V) 𝔮
    have : IsDomain (Localization.AtPrime 𝔮) := hO.1
    have hc𝔮 : algebraMap O (Localization.AtPrime 𝔮) c ∈ nonZeroDivisors _ :=
      mem_nonZeroDivisors_of_ne_zero hcne
    have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing Γ(S, V) O
    obtain ⟨s, hs𝔮, hcs⟩ := exists_notMem_mem_nonZeroDivisors_away c 𝔮 hc𝔮
    -- the chart over `O_s`
    let ν' := chartAwayMap c s Wa
    have hν' := etale_chartAwayMap c s Wa
    let φ' : Γ(X, W) →+* chartAway c s Wa := (algebraMap Wa (chartAway c s Wa)).comp φ
    have hφ' : φ'.Etale := RingHom.Etale.stableUnderComposition _ _ hφ
      (RingHom.etale_algebraMap.mpr inferInstance)
    have hcompat' : ∀ r : Γ(S, V), ν' (algebraMap (Localization.Away s)
        (Node (Localization.Away s) (algebraMap O _ c))
          (algebraMap Γ(S, V) (Localization.Away s) r)) = φ' (f.appLE V W hle r) := by
      intro r
      rw [IsScalarTower.algebraMap_apply Γ(S, V) O (Localization.Away s) r,
        chartAwayMap_algebraMap, ← hcompat r]
      change _ = algebraMap Wa (chartAway c s Wa) (algebraMap (Localization.Away f₀) Wa
        (algebraMap Γ(X, W) (Localization.Away f₀) (algebraMap Γ(S, V) Γ(X, W) r)))
      rw [← IsScalarTower.algebraMap_apply Γ(S, V) Γ(X, W) (Localization.Away f₀)]
    let ψ : Spec (CommRingCat.of (chartAway c s Wa)) ⟶ X :=
      Spec.map (CommRingCat.ofHom φ') ≫ hW.fromSpec
    let C := EtaleNodeChart.ofSpec f hV hW hle φ' (ψ := ψ) rfl (Localization.Away s)
      (algebraMap O _ c) hcs ν' hν' hcompat'
    have : Etale (Spec.map (CommRingCat.ofHom φ')) := HasRingHomProperty.Spec_iff.mpr hφ'
    -- the point over `x`
    have hs' : algebraMap (Node O c) Wa (algebraMap O (Node O c) s) ∉ 𝔔 := hs𝔮
    have hdisj : Disjoint (Submonoid.powers (algebraMap (Node O c) Wa (algebraMap O (Node O c) s))
        : Set Wa) (𝔔 : Set Wa) := by
      rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    have h𝔔' : (𝔔.map (algebraMap Wa (chartAway c s Wa))).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint _ _ _ inferInstance hdisj
    let x' : PrimeSpectrum (chartAway c s Wa) := ⟨_, h𝔔'⟩
    have hψx' : ψ x' = x := by
      change hW.fromSpec (PrimeSpectrum.comap φ' x') = x
      have : PrimeSpectrum.comap φ' x' = 𝔭 := by
        rw [← hcomap]
        ext1
        change Ideal.comap ((algebraMap Wa (chartAway c s Wa)).comp φ)
          (𝔔.map (algebraMap Wa (chartAway c s Wa))) = 𝔔.comap φ
        rw [← Ideal.comap_comap]
        congr 1
        exact IsLocalization.under_map_of_isPrime_disjoint _ _ inferInstance hdisj
      rw [this, hx𝔭]
    -- shrink to a basic open inside the image
    have hrange : IsOpen (Set.range ψ) := ψ.isOpenMap.isOpen_range
    obtain ⟨t, htle, hxt⟩ := hW.exists_basicOpen_le (V := ⟨Set.range ψ, hrange⟩)
      ⟨x, ⟨x', hψx'⟩⟩ hxW
    exact ⟨chartAway c s Wa, inferInstance, φ', hφ', C, t, hxt, htle⟩

section Relation

variable {X X' S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (ψ : X' ⟶ X)

/-- Sections of `ω` given by a differential: `ω(W) ∋ toDualizingSheaf (s)` is `s|_{W ∩ Sm f}`. -/
theorem dualizingSheafSectionsEquiv_toDualizingSheaf (W : X.Opens)
    (s : Γ(relativeDifferentials f, W)) :
    dualizingSheafSectionsEquiv f W ((toDualizingSheaf f).app W s) =
      (relativeDifferentials f).presheaf.map (homOfLE (inf_le_left : W ⊓ f.smoothLocus ≤ W)).op s := by
  change (relativeDifferentials f).presheaf.map _ ((relativeDifferentials f).presheaf.map _ s) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- `ψ^♯` commutes with restrictions: `(ψ^♯ a|_U)|_D = (ψ^♯ a)|_D`. -/
theorem res_app_res_eq {W U : X.Opens} (hU : U ≤ W) {W'' D : X'.Opens} (hWW'' : W'' ≤ ψ ⁻¹ᵁ W)
    (hDU : D ≤ ψ ⁻¹ᵁ U) (hDW'' : D ≤ W'') (a : Γ(X, W)) :
    res hDU (ψ.app U (res hU a)) = res hDW'' (ψ.appLE W W'' hWW'' a) := by
  change (X.presheaf.map _ ≫ ψ.app U ≫ X'.presheaf.map _) a =
    (ψ.appLE W W'' hWW'' ≫ X'.presheaf.map _) a
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/-- **The generator relation on `D(u)`** (blueprint `lem:sm-omega-cd-generator-relation`, scheme
part). Let `σ` generate `ω` on `W` with `c σ = da`, let `σ_T` be a section of `Ω¹_{X'/S}` over
`D(u₀) ∪ D(v₀) ⊆ W''` with `u₀ σ_T = du₀` on `D(u₀)`, and let the pullback `θ_ψ(σ)` be `g σ_T`.
Then `u₀ · d(ψ^♯ a) = ψ^♯ c · g · du₀` on `D(u₀)`. -/
theorem relation_basicOpen_left {W : X.Opens} (σ : Γ(dualizingSheaf f, W)) (a c : Γ(X, W))
    (hc : c • σ = (toDualizingSheaf f).app W ((universalDerivation f).sec W a))
    {W'' : X'.Opens} (hWW'' : W'' ≤ ψ ⁻¹ᵁ W) {u₀ v₀ : Γ(X', W'')}
    (σT : Γ(relativeDifferentials (ψ ≫ f), X'.basicOpen u₀ ⊔ X'.basicOpen v₀))
    (hσu : res (X'.basicOpen_le u₀) u₀ • (relativeDifferentials (ψ ≫ f)).presheaf.map
        (homOfLE le_sup_left).op σT =
      (universalDerivation (ψ ≫ f)).sec _ (res (X'.basicOpen_le u₀) u₀))
    (hG : X'.basicOpen u₀ ⊔ X'.basicOpen v₀ ≤ ψ ⁻¹ᵁ (W ⊓ f.smoothLocus)) (g : Γ(X', W''))
    (hg : res (sup_le (X'.basicOpen_le u₀) (X'.basicOpen_le v₀)) g • σT =
      (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE hG).op
        ((pullbackDifferentials f ψ).app (W ⊓ f.smoothLocus) (dualizingSheafSectionsEquiv f W σ))) :
    res (X'.basicOpen_le u₀) u₀ • (universalDerivation (ψ ≫ f)).sec (X'.basicOpen u₀)
        (res (X'.basicOpen_le u₀) (ψ.appLE W W'' hWW'' a)) =
      res (X'.basicOpen_le u₀) (ψ.appLE W W'' hWW'' c * g) •
        (universalDerivation (ψ ≫ f)).sec (X'.basicOpen u₀) (res (X'.basicOpen_le u₀) u₀) := by
  set m := dualizingSheafSectionsEquiv f W σ
  set θ := pullbackDifferentials f ψ
  have hWU : W ⊓ f.smoothLocus ≤ W := inf_le_left
  -- `c|_{W ∩ U} • m = d(a|_{W ∩ U})`
  have h1 : res hWU c • m = (universalDerivation f).sec _ (res hWU a) := by
    rw [← dualizingSheafSectionsEquiv_smul, hc, dualizingSheafSectionsEquiv_toDualizingSheaf,
      sec_res]
  -- pull back along `ψ`
  have h2 := congrArg (secMap₀ ψ θ (W ⊓ f.smoothLocus)) h1
  rw [secMap₀_smul] at h2
  change ψ.app _ (res hWU c) • secMap₀ ψ θ _ m = (pullbackDifferentials f ψ).app _
    ((universalDerivation f).d (res hWU a)) at h2
  rw [pullbackDifferentials_app_d] at h2
  -- restrict to `D(u₀)`
  have hDu : X'.basicOpen u₀ ≤ ψ ⁻¹ᵁ (W ⊓ f.smoothLocus) := le_sup_left.trans hG
  have h3 := congrArg ((relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE hDu).op) h2
  rw [Ω_map_res_smul] at h3
  change _ = (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE hDu).op
    ((universalDerivation (ψ ≫ f)).sec _ (ψ.app _ (res hWU a))) at h3
  rw [← sec_res, res_app_res_eq ψ hWU hWW'' hDu (X'.basicOpen_le u₀),
    res_app_res_eq ψ hWU hWW'' hDu (X'.basicOpen_le u₀)] at h3
  have h4 : (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE hDu).op (secMap₀ ψ θ _ m) =
      res (X'.basicOpen_le u₀) g • (relativeDifferentials (ψ ≫ f)).presheaf.map
        (homOfLE le_sup_left).op σT := by
    have hg' : res (sup_le (X'.basicOpen_le u₀) (X'.basicOpen_le v₀)) g • σT =
        (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE hG).op (secMap₀ ψ θ _ m) := hg
    rw [← map_map_eq (h₁ := hG) (h₂ := le_sup_left), ← hg', Ω_map_res_smul, res_res]
  rw [h4] at h3
  rw [← h3, ← hσu]
  simp only [smul_smul, map_mul]
  congr 1
  ring

/-- **The generator relation on `D(v)`**: as `relation_basicOpen_right`, with `v₀ σ_T = -dv₀` on
`D(v₀)`; then `v₀ · d(ψ^♯ a) = ψ^♯ c · (-g) · dv₀` on `D(v₀)`. -/
theorem relation_basicOpen_right {W : X.Opens} (σ : Γ(dualizingSheaf f, W)) (a c : Γ(X, W))
    (hc : c • σ = (toDualizingSheaf f).app W ((universalDerivation f).sec W a))
    {W'' : X'.Opens} (hWW'' : W'' ≤ ψ ⁻¹ᵁ W) {u₀ v₀ : Γ(X', W'')}
    (σT : Γ(relativeDifferentials (ψ ≫ f), X'.basicOpen u₀ ⊔ X'.basicOpen v₀))
    (hσv : res (X'.basicOpen_le v₀) v₀ • (relativeDifferentials (ψ ≫ f)).presheaf.map
        (homOfLE le_sup_right).op σT =
      -(universalDerivation (ψ ≫ f)).sec _ (res (X'.basicOpen_le v₀) v₀))
    (hG : X'.basicOpen u₀ ⊔ X'.basicOpen v₀ ≤ ψ ⁻¹ᵁ (W ⊓ f.smoothLocus)) (g : Γ(X', W''))
    (hg : res (sup_le (X'.basicOpen_le u₀) (X'.basicOpen_le v₀)) g • σT =
      (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE hG).op
        ((pullbackDifferentials f ψ).app (W ⊓ f.smoothLocus) (dualizingSheafSectionsEquiv f W σ))) :
    res (X'.basicOpen_le v₀) v₀ • (universalDerivation (ψ ≫ f)).sec (X'.basicOpen v₀)
        (res (X'.basicOpen_le v₀) (ψ.appLE W W'' hWW'' a)) =
      res (X'.basicOpen_le v₀) (ψ.appLE W W'' hWW'' c * -g) •
        (universalDerivation (ψ ≫ f)).sec (X'.basicOpen v₀) (res (X'.basicOpen_le v₀) v₀) := by
  set m := dualizingSheafSectionsEquiv f W σ
  set θ := pullbackDifferentials f ψ
  have hWU : W ⊓ f.smoothLocus ≤ W := inf_le_left
  -- `c|_{W ∩ U} • m = d(a|_{W ∩ U})`
  have h1 : res hWU c • m = (universalDerivation f).sec _ (res hWU a) := by
    rw [← dualizingSheafSectionsEquiv_smul, hc, dualizingSheafSectionsEquiv_toDualizingSheaf,
      sec_res]
  -- pull back along `ψ`
  have h2 := congrArg (secMap₀ ψ θ (W ⊓ f.smoothLocus)) h1
  rw [secMap₀_smul] at h2
  change ψ.app _ (res hWU c) • secMap₀ ψ θ _ m = (pullbackDifferentials f ψ).app _
    ((universalDerivation f).d (res hWU a)) at h2
  rw [pullbackDifferentials_app_d] at h2
  -- restrict to `D(v₀)`
  have hDv : X'.basicOpen v₀ ≤ ψ ⁻¹ᵁ (W ⊓ f.smoothLocus) := le_sup_right.trans hG
  have h3 := congrArg ((relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE hDv).op) h2
  rw [Ω_map_res_smul] at h3
  change _ = (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE hDv).op
    ((universalDerivation (ψ ≫ f)).sec _ (ψ.app _ (res hWU a))) at h3
  rw [← sec_res, res_app_res_eq ψ hWU hWW'' hDv (X'.basicOpen_le v₀),
    res_app_res_eq ψ hWU hWW'' hDv (X'.basicOpen_le v₀)] at h3
  have h4 : (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE hDv).op (secMap₀ ψ θ _ m) =
      res (X'.basicOpen_le v₀) g • (relativeDifferentials (ψ ≫ f)).presheaf.map
        (homOfLE le_sup_right).op σT := by
    have hg' : res (sup_le (X'.basicOpen_le u₀) (X'.basicOpen_le v₀)) g • σT =
        (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE hG).op (secMap₀ ψ θ _ m) := hg
    rw [← map_map_eq (h₁ := hG) (h₂ := le_sup_right), ← hg', Ω_map_res_smul, res_res]
  rw [h4] at h3
  have hdv : (universalDerivation (ψ ≫ f)).sec _ (res (X'.basicOpen_le v₀) v₀) =
      -(res (X'.basicOpen_le v₀) v₀ • (relativeDifferentials (ψ ≫ f)).presheaf.map
        (homOfLE le_sup_right).op σT) := by
    rw [hσv, neg_neg]
  rw [← h3, hdv]
  simp only [smul_smul, map_mul, map_neg, smul_neg]
  rw [← neg_smul]
  congr 1
  ring

end Relation

section Unit

variable {X X' S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (ψ : X' ⟶ X)

set_option backward.isDefEq.respectTransparency false in
/-- **The pulled-back generator of `ω` is a unit multiple of the chart generator** (blueprint
`lem:sm-omega-cd-generator-relation`, the unit). Let `Γ(X, W) → Γ(X', W'')` be étale, `W ∩ Sm f` a
finite union of basic opens, `σ` a free generator of `ω` on `W`, `G = ψ⁻¹(W ∩ Sm f) ∩ W''`, and
`σ_T ∈ Γ(G, Ω¹_{X'/S})` with `c ↦ c σ_T` bijective on `Γ(X', W'')`. If `θ_ψ(σ)|_G = g σ_T`, then `g`
is a unit: by étale base change of `Ω¹` over `W ∩ Sm f` (`bijective_baseChangeSec_of_eq_iSup`)
`σ_T = Σ tᵢ θ_ψ(aᵢ σ) = (Σ tᵢ ψ^♯ aᵢ) g σ_T`. -/
theorem isUnit_of_eq_smul_generator {V : S.Opens} (hV : IsAffineOpen V) {W : X.Opens}
    (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) {W'' : X'.Opens} (hW'' : IsAffineOpen W'')
    (hWW'' : W'' ≤ ψ ⁻¹ᵁ W) (hét : (ψ.appLE W W'' hWW'').hom.Etale) {n : ℕ}
    (b : Fin n → Γ(X, W)) (hb : W ⊓ f.smoothLocus = ⨆ i, X.basicOpen (b i))
    (σ : Γ(dualizingSheaf f, W)) (hσ : Function.Bijective fun c : Γ(X, W) => c • σ)
    {G : X'.Opens} (hGeq : ψ ⁻¹ᵁ (W ⊓ f.smoothLocus) ⊓ W'' = G) (hGW : G ≤ W'')
    (σT : Γ(relativeDifferentials (ψ ≫ f), G))
    (hbijT : Function.Bijective fun c : Γ(X', W'') => res hGW c • σT) (g : Γ(X', W''))
    (hg : res hGW g • σT = (relativeDifferentials (ψ ≫ f)).presheaf.map
      (homOfLE (hGeq.ge.trans inf_le_left)).op
        (secMap₀ ψ (pullbackDifferentials f ψ) (W ⊓ f.smoothLocus)
          (dualizingSheafSectionsEquiv f W σ))) :
    IsUnit g := by
  set θ := pullbackDifferentials f ψ
  set m := dualizingSheafSectionsEquiv f W σ
  let := pullAlgebra ψ hWW''
  have hY : W ⊓ f.smoothLocus ≤ W := inf_le_left
  have hΘ := bijective_baseChangeSec_of_eq_iSup f ψ hV hW hWV hW'' hWW'' hét hY b hb
  let τ : SecOver (relativeDifferentials (ψ ≫ f))
      (inf_le_right : ψ ⁻¹ᵁ (W ⊓ f.smoothLocus) ⊓ W'' ≤ W'') :=
    (SecOver.equiv _ _).symm ((relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE hGeq.le).op σT)
  obtain ⟨z, hz⟩ := hΘ.2 τ
  let m' : SecOver (relativeDifferentials f) hY := (SecOver.equiv _ _).symm m
  let := pullModule ψ hWW'' (G := relativeDifferentials (ψ ≫ f))
    (inf_le_right : ψ ⁻¹ᵁ (W ⊓ f.smoothLocus) ⊓ W'' ≤ W'')
  have := pullIsScalarTower ψ hWW'' (G := relativeDifferentials (ψ ≫ f))
    (inf_le_right : ψ ⁻¹ᵁ (W ⊓ f.smoothLocus) ⊓ W'' ≤ W'')
  -- every section of `Ω¹_X` over `W ∩ U` is `a • m`
  have hmul : ∀ n' : SecOver (relativeDifferentials f) hY, ∃ a : Γ(X, W), a • m' = n' := by
    intro n'
    obtain ⟨a, ha⟩ := hσ.surjective ((dualizingSheafSectionsEquiv f W).symm (SecOver.equiv _ _ n'))
    refine ⟨a, (SecOver.equiv _ _).injective ?_⟩
    rw [SecOver.smul_def]
    change res hY a • m = _
    rw [← dualizingSheafSectionsEquiv_smul]
    change dualizingSheafSectionsEquiv f W ((fun c : Γ(X, W) => c • σ) a) = _
    rw [ha, AddEquiv.apply_symm_apply]
  have hspan : ∀ z, ∃ c : Γ(X', W''),
      baseChangeSec ψ θ hWW'' hY z = c • secLinear ψ θ hWW'' hY m' := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, zero_smul]⟩
    | tmul t' n' =>
      obtain ⟨a, rfl⟩ := hmul n'
      refine ⟨t' * ψ.appLE W W'' hWW'' a, ?_⟩
      change (secLinear ψ θ hWW'' hY).liftBaseChange _ (t' ⊗ₜ (a • m')) = _
      rw [LinearMap.liftBaseChange_tmul, LinearMap.map_smul, mul_smul]
      rfl
    | add x y hx hy =>
      obtain ⟨c₁, h₁⟩ := hx
      obtain ⟨c₂, h₂⟩ := hy
      exact ⟨c₁ + c₂, by rw [map_add, h₁, h₂, add_smul]⟩
  obtain ⟨c, hc⟩ := hspan z
  rw [hz] at hc
  -- compare in `Γ(G, Ω¹)`
  have h1 := congrArg (SecOver.equiv _ _) hc
  change (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE hGeq.le).op σT =
    res (inf_le_right : ψ ⁻¹ᵁ (W ⊓ f.smoothLocus) ⊓ W'' ≤ W'') c •
      (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE inf_le_left).op
        (secMap₀ ψ θ (W ⊓ f.smoothLocus) m) at h1
  rw [← map_map_eq (h₁ := hGeq.ge.trans inf_le_left) (h₂ := hGeq.le), ← hg, Ω_map_res_smul,
    smul_smul, res_res] at h1
  have h1' : (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE hGeq.le).op σT =
      (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE hGeq.le).op (res hGW (c * g) • σT) := by
    rw [Ω_map_res_smul, res_res, map_mul]
    exact h1
  have h2 := (relativeDifferentials (ψ ≫ f)).map_injective_of_le _ hGeq.ge h1'
  have h3 : (fun c : Γ(X', W'') => res hGW c • σT) 1 =
      (fun c : Γ(X', W'') => res hGW c • σT) (c * g) := by
    simp only [map_one, one_smul]
    exact h2
  exact IsUnit.of_mul_eq_one_right c (hbijT.injective h3).symm

end Unit

section Data

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]

/-- **Étale node data at a non-smooth point** (blueprint `lem:sm-omega-cd-generator-relation`).
An affine `x ∈ W ⊆ f⁻¹ V` with a free generator `σ` of `ω` on `W`, an étale and faithfully flat
`Γ(X, W) → T` with an étale node structure `O[u,v]/(uv - c) → T` over `Γ(S, V)` (`O` étale over
`Γ(S, V)`), such that every prime of `T` over a non-smooth point of `W` contains `u, v`, and a unit
`g ∈ T` with `u · d(ψ^♯ a) = ψ^♯ c' · g · du` on `D(u)` and `v · d(ψ^♯ a) = -ψ^♯ c' · g · dv` on
`D(v)` whenever `c' σ = da` (i.e. `ψ^* σ = g · du/u = -g · dv/v`). -/
structure NodePoleData (x : X) where
  /-- The affine open of the base. -/
  V : S.Opens
  isAffineOpen_V : IsAffineOpen V
  /-- The affine open of `X`. -/
  W : X.Opens
  isAffineOpen_W : IsAffineOpen W
  le : W ≤ f ⁻¹ᵁ V
  mem : x ∈ W
  /-- The generator of `ω` on `W`. -/
  σ : Γ(dualizingSheaf f, W)
  bijective_σ : Function.Bijective (fun c : Γ(X, W) => c • σ)
  /-- The étale chart ring. -/
  T : Type u
  [commRing : CommRing T]
  [algebra : Algebra Γ(X, W) T]
  [algebraBase : Algebra Γ(S, V) T]
  isScalarTower : letI := (f.appLE V W le).hom.toAlgebra; IsScalarTower Γ(S, V) Γ(X, W) T
  [etale : Algebra.Etale Γ(X, W) T]
  [faithfullyFlat : Module.FaithfullyFlat Γ(X, W) T]
  /-- The étale base of the node. -/
  O : Type u
  [commRingO : CommRing O]
  [algebraO : Algebra Γ(S, V) O]
  [etaleO : Algebra.Etale Γ(S, V) O]
  /-- The equation of the node. -/
  c : O
  [algebraNode : Algebra (Node O c) T]
  [isScalarTowerNode : IsScalarTower Γ(S, V) (Node O c) T]
  [etaleNode : Algebra.Etale (Node O c) T]
  node : ∀ p : PrimeSpectrum Γ(X, W), isAffineOpen_W.fromSpec p ∉ f.smoothLocus →
    ∀ P : Ideal T, P.IsPrime → P.comap (algebraMap Γ(X, W) T) = p.asIdeal →
      algebraMap (Node O c) T (coordinate c 0) ∈ P ∧ algebraMap (Node O c) T (coordinate c 1) ∈ P
  /-- The unit comparing `ψ^* σ` with `du/u`. -/
  g : T
  isUnit_g : IsUnit g
  /-- The localization `T_u`. -/
  Tu : Type u
  [commRingTu : CommRing Tu]
  [algebraTu : Algebra T Tu]
  [isLocalizationTu : IsLocalization.Away (algebraMap (Node O c) T (coordinate c 0)) Tu]
  [algebraBaseTu : Algebra Γ(S, V) Tu]
  [isScalarTowerTu : IsScalarTower Γ(S, V) T Tu]
  rel_u : ∀ a c' : Γ(X, W), c' • σ = (toDualizingSheaf f).app W ((universalDerivation f).sec W a) →
    algebraMap T Tu (algebraMap (Node O c) T (coordinate c 0)) •
        KaehlerDifferential.D Γ(S, V) Tu (algebraMap T Tu (algebraMap Γ(X, W) T a)) =
      algebraMap T Tu (algebraMap Γ(X, W) T c' * g) •
        KaehlerDifferential.D Γ(S, V) Tu (algebraMap T Tu (algebraMap (Node O c) T (coordinate c 0)))
  /-- The localization `T_v`. -/
  Tv : Type u
  [commRingTv : CommRing Tv]
  [algebraTv : Algebra T Tv]
  [isLocalizationTv : IsLocalization.Away (algebraMap (Node O c) T (coordinate c 1)) Tv]
  [algebraBaseTv : Algebra Γ(S, V) Tv]
  [isScalarTowerTv : IsScalarTower Γ(S, V) T Tv]
  rel_v : ∀ a c' : Γ(X, W), c' • σ = (toDualizingSheaf f).app W ((universalDerivation f).sec W a) →
    algebraMap T Tv (algebraMap (Node O c) T (coordinate c 1)) •
        KaehlerDifferential.D Γ(S, V) Tv (algebraMap T Tv (algebraMap Γ(X, W) T a)) =
      algebraMap T Tv (algebraMap Γ(X, W) T c' * -g) •
        KaehlerDifferential.D Γ(S, V) Tv (algebraMap T Tv (algebraMap (Node O c) T (coordinate c 1)))

attribute [instance] NodePoleData.commRing NodePoleData.algebra NodePoleData.algebraBase
  NodePoleData.etale NodePoleData.faithfullyFlat NodePoleData.commRingO NodePoleData.algebraO
  NodePoleData.etaleO NodePoleData.algebraNode NodePoleData.isScalarTowerNode
  NodePoleData.etaleNode NodePoleData.commRingTu NodePoleData.algebraTu
  NodePoleData.isLocalizationTu NodePoleData.algebraBaseTu NodePoleData.isScalarTowerTu
  NodePoleData.commRingTv NodePoleData.algebraTv NodePoleData.isLocalizationTv
  NodePoleData.algebraBaseTv NodePoleData.isScalarTowerTv

end Data

section Existence

variable {X S : Scheme.{u}}

/-- Restriction of functions to the same open is the identity. -/
theorem res_self {U : X.Opens} (k : U ≤ U) (a : Γ(X, U)) : res k a = a := by
  change X.presheaf.map (homOfLE k).op a = a
  rw [show homOfLE k = 𝟙 U from rfl, op_id, X.presheaf.map_id]
  rfl

/-- Restriction of functions between equal opens is bijective. -/
theorem res_bijective_of_le {U U' : X.Opens} (h : U' ≤ U) (h' : U ≤ U') :
    Function.Bijective (res h) := by
  refine ⟨fun a b hab => ?_, fun a => ⟨res h' a, ?_⟩⟩
  · have := congrArg (res h') hab
    rwa [res_res, res_res, res_self, res_self] at this
  · rw [res_res, res_self]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Étale node data from an étale node chart**: an étale `ψ : X' ⟶ X` compatible with the smooth
loci, a free generator `σ` of `ω` on an affine `x ∈ W ⊆ f⁻¹ V`, and an étale node chart of `ψ ≫ f`
on an affine `W' ⊆ ψ⁻¹ W` mapping onto `W` give `NodePoleData f x`, with `T = Γ(X', W')`. -/
theorem nonempty_nodePoleData_of_chart (f : X ⟶ S) [LocallyOfFinitePresentation f] {X' : Scheme.{u}}
    (ψ : X' ⟶ X) [Etale ψ] (hsmψ : ∀ y, y ∈ (ψ ≫ f).smoothLocus ↔ ψ y ∈ f.smoothLocus)
    {x : X} {V : S.Opens} (hV : IsAffineOpen V) {W : X.Opens} (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) (hxW : x ∈ W) (σ : Γ(dualizingSheaf f, W))
    (hσ : Function.Bijective fun c : Γ(X, W) => c • σ) {W' : X'.Opens} (hW' : IsAffineOpen W')
    (hW'W : W' ≤ ψ ⁻¹ᵁ W) (hsurj : ∀ y ∈ W, ∃ y' ∈ W', ψ y' = y)
    (C₁ : EtaleNodeChart (ψ ≫ f) V W') : Nonempty (NodePoleData f x) := by
  have H := C₁.twoChartAffine
  have hW''eq : X'.basicOpen (1 : Γ(X', W')) = W' := basicOpen_one_eq
  have hW'' : IsAffineOpen (X'.basicOpen (1 : Γ(X', W'))) := hW'.basicOpen 1
  have hW''W' : X'.basicOpen (1 : Γ(X', W')) ≤ W' := X'.basicOpen_le _
  have hW''W : X'.basicOpen (1 : Γ(X', W')) ≤ ψ ⁻¹ᵁ W := hW''W'.trans hW'W
  have hsurj'' : ∀ y ∈ W, ∃ y' ∈ X'.basicOpen (1 : Γ(X', W')), ψ y' = y := by
    intro y hy
    obtain ⟨y', hy', rfl⟩ := hsurj y hy
    exact ⟨y', hW''eq.ge hy', rfl⟩
  -- the two-chart generator `du/u = -dv/v` on `W''`
  obtain ⟨σT, hσu, hσv, hbijT⟩ := (H.twoChartData 1).exists_bijective
  have hGsm := H.basicOpen_inf_smoothLocus 1
  have hGeq : ψ ⁻¹ᵁ (W ⊓ f.smoothLocus) ⊓ X'.basicOpen (1 : Γ(X', W')) =
      X'.basicOpen (res (X'.basicOpen_le (1 : Γ(X', W'))) (C₁.coord 0)) ⊔
        X'.basicOpen (res (X'.basicOpen_le (1 : Γ(X', W'))) (C₁.coord 1)) := by
    rw [← hGsm]
    apply le_antisymm
    · rintro y ⟨⟨-, hy⟩, hy''⟩
      exact ⟨hy'', (hsmψ y).mpr hy⟩
    · rintro y ⟨hy'', hy⟩
      exact ⟨⟨hW''W hy'', (hsmψ y).mp hy⟩, hy''⟩
  have hGW := sup_le (X'.basicOpen_le (res (X'.basicOpen_le (1 : Γ(X', W'))) (C₁.coord 0)))
    (X'.basicOpen_le (res (X'.basicOpen_le (1 : Γ(X', W'))) (C₁.coord 1)))
  have hGψ := hGeq.ge.trans (inf_le_left : ψ ⁻¹ᵁ (W ⊓ f.smoothLocus) ⊓
    X'.basicOpen (1 : Γ(X', W')) ≤ ψ ⁻¹ᵁ (W ⊓ f.smoothLocus))
  obtain ⟨g, hg⟩ := hbijT.surjective ((relativeDifferentials (ψ ≫ f)).presheaf.map
    (homOfLE hGψ).op (secMap₀ ψ (pullbackDifferentials f ψ) _ (dualizingSheafSectionsEquiv f W σ)))
  change res hGW g • σT = _ at hg
  -- `g` is a unit
  have hét : (ψ.appLE W (X'.basicOpen (1 : Γ(X', W'))) hW''W).hom.Etale :=
    HasRingHomProperty.appLE @Etale ψ inferInstance ⟨_, hW⟩ ⟨_, hW''⟩ hW''W
  have hK : IsCompact ((W ⊓ f.smoothLocus : X.Opens) : Set X) := by
    have : ((W ⊓ f.smoothLocus : X.Opens) : Set X) = ψ '' ((X'.basicOpen
        (res (X'.basicOpen_le (1 : Γ(X', W'))) (C₁.coord 0)) ⊔
          X'.basicOpen (res (X'.basicOpen_le (1 : Γ(X', W'))) (C₁.coord 1)) : X'.Opens) :
            Set X') := by
      ext y
      constructor
      · rintro ⟨hyW, hyU⟩
        obtain ⟨y', hy', rfl⟩ := hsurj'' y hyW
        refine ⟨y', ?_, rfl⟩
        rw [← hGsm]
        exact ⟨hy', (hsmψ y').mpr hyU⟩
      · rintro ⟨y', hy', rfl⟩
        exact hGψ hy'
    rw [this]
    exact ((hW''.basicOpen _).isCompact.union (hW''.basicOpen _).isCompact).image ψ.continuous
  obtain ⟨n, b, hb⟩ := exists_eq_iSup_basicOpen_of_isCompact hW hK inf_le_left
  have hgu : IsUnit g := isUnit_of_eq_smul_generator f ψ hV hW hWV hW'' hW''W hét b hb σ hσ
    hGeq hGW σT hbijT g hg
  -- the algebra structures
  let T := Γ(X', X'.basicOpen (1 : Γ(X', W')))
  let : Algebra Γ(X, W) T := pullAlgebra ψ hW''W
  have hle'' : X'.basicOpen (1 : Γ(X', W')) ≤ (ψ ≫ f) ⁻¹ᵁ V := hW''W'.trans C₁.le
  let : Algebra Γ(S, V) T := ((ψ ≫ f).appLE V _ hle'').hom.toAlgebra
  have hST : letI := (f.appLE V W hWV).hom.toAlgebra; IsScalarTower Γ(S, V) Γ(X, W) T := by
    let := (f.appLE V W hWV).hom.toAlgebra
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change (ψ ≫ f).appLE V _ hle'' r = (f.appLE V W hWV ≫ ψ.appLE W _ hW''W) r
    rw [Scheme.Hom.appLE_comp_appLE]
  have : Algebra.Etale Γ(X, W) T := hét
  have : Module.FaithfullyFlat Γ(X, W) T :=
    faithfullyFlat_of_surjective ψ hW hW'' hW''W inferInstance hsurj''
  let : Algebra (Node C₁.O C₁.c) T := C₁.nodeAlgebra hW''W'
  have : IsScalarTower Γ(S, V) (Node C₁.O C₁.c) T := C₁.isScalarTower hW''W'
  have : Algebra.Etale (Node C₁.O C₁.c) T :=
    RingHom.Etale.stableUnderComposition _ _ C₁.etale_toNode
      (RingHom.Etale.of_bijective (res_bijective_of_le hW''W' hW''eq.ge))
  -- the primes over the non-smooth points contain `u, v`
  have hnode : ∀ p : PrimeSpectrum Γ(X, W), hW.fromSpec p ∉ f.smoothLocus →
      ∀ P : Ideal T, P.IsPrime → P.comap (algebraMap Γ(X, W) T) = p.asIdeal →
        algebraMap (Node C₁.O C₁.c) T (coordinate C₁.c 0) ∈ P ∧
          algebraMap (Node C₁.O C₁.c) T (coordinate C₁.c 1) ∈ P := by
    intro p hp P hP hPp
    let y' := hW''.fromSpec ⟨P, hP⟩
    have hy' : y' ∈ X'.basicOpen (1 : Γ(X', W')) := by
      rw [← SetLike.mem_coe, ← hW''.range_fromSpec]; exact Set.mem_range_self _
    have hψy' : ψ y' = hW.fromSpec p := by
      have h1 := congrArg (fun φ' => φ' (⟨P, hP⟩ : PrimeSpectrum T))
        (IsAffineOpen.SpecMap_appLE_fromSpec ψ hW hW'' hW''W)
      simp only [Scheme.Hom.comp_apply] at h1
      rw [← h1]
      congr 1
      exact PrimeSpectrum.ext hPp
    have hsm' : y' ∉ (ψ ≫ f).smoothLocus := fun h => hp (hψy' ▸ (hsmψ y').mp h)
    have hprime : (hW''.primeIdealOf ⟨y', hy'⟩).asIdeal = P := by
      rw [IsAffineOpen.primeIdealOf_fromSpec hW'' ⟨P, hP⟩ hy']
    have hmem : ∀ i : Fin 2, algebraMap (Node C₁.O C₁.c) T (coordinate C₁.c i) ∈ P := by
      intro i
      by_contra hi
      apply hsm'
      have hyb : y' ∈ X'.basicOpen (res (X'.basicOpen_le (1 : Γ(X', W'))) (C₁.coord i)) := by
        rw [mem_basicOpen_iff_notMem hW'' hy', hprime]
        exact hi
      have hle : X'.basicOpen (res (X'.basicOpen_le (1 : Γ(X', W'))) (C₁.coord i)) ≤
          X'.basicOpen (1 : Γ(X', W')) ⊓ (ψ ≫ f).smoothLocus := by
        rw [hGsm]
        fin_cases i
        · exact le_sup_left
        · exact le_sup_right
      exact (hle hyb).2
    exact ⟨hmem 0, hmem 1⟩
  -- the localizations `T_u`, `T_v` and the relations
  have hTx : ∀ i : Fin 2, ∃ (Tx : Type u) (_ : CommRing Tx) (_ : Algebra T Tx)
      (_ : IsLocalization.Away (algebraMap (Node C₁.O C₁.c) T (coordinate C₁.c i)) Tx)
      (_ : Algebra Γ(S, V) Tx) (_ : IsScalarTower Γ(S, V) T Tx),
      ∀ a c' : Γ(X, W), c' • σ = (toDualizingSheaf f).app W ((universalDerivation f).sec W a) →
        algebraMap T Tx (algebraMap (Node C₁.O C₁.c) T (coordinate C₁.c i)) •
            KaehlerDifferential.D Γ(S, V) Tx (algebraMap T Tx (algebraMap Γ(X, W) T a)) =
          algebraMap T Tx (algebraMap Γ(X, W) T c' * (if i = 0 then g else -g)) •
            KaehlerDifferential.D Γ(S, V) Tx
              (algebraMap T Tx (algebraMap (Node C₁.O C₁.c) T (coordinate C₁.c i))) := by
    intro i
    set x₀ : T := algebraMap (Node C₁.O C₁.c) T (coordinate C₁.c i) with hx₀
    let : Algebra T Γ(X', X'.basicOpen x₀) := (res (X'.basicOpen_le x₀)).toAlgebra
    have hloc : IsLocalization.Away x₀ Γ(X', X'.basicOpen x₀) := hW''.isLocalization_basicOpen x₀
    have hlex : X'.basicOpen x₀ ≤ (ψ ≫ f) ⁻¹ᵁ V := (X'.basicOpen_le x₀).trans hle''
    let : Algebra Γ(S, V) Γ(X', X'.basicOpen x₀) := ((ψ ≫ f).appLE V _ hlex).hom.toAlgebra
    have : IsScalarTower Γ(S, V) T Γ(X', X'.basicOpen x₀) := IsScalarTower.of_algebraMap_eq
      fun r => by
        change (ψ ≫ f).appLE V _ hlex r = ((ψ ≫ f).appLE V _ hle'' ≫ X'.presheaf.map _) r
        rw [Scheme.Hom.appLE_map]
    refine ⟨Γ(X', X'.basicOpen x₀), inferInstance, inferInstance, hloc, inferInstance, this,
      fun a c' hc' => ?_⟩
    let e := sectionsEquiv (ψ ≫ f) (hW''.basicOpen x₀) hV hlex
    have hd : ∀ b, e.symm ((universalDerivation (ψ ≫ f)).sec _ b) =
        KaehlerDifferential.D Γ(S, V) Γ(X', X'.basicOpen x₀) b := fun b =>
      (e.symm_apply_eq).mpr (sectionsEquiv_d _ _ _ _ b).symm
    have h : res (X'.basicOpen_le x₀) x₀ • (universalDerivation (ψ ≫ f)).sec (X'.basicOpen x₀)
          (res (X'.basicOpen_le x₀) (ψ.appLE W _ hW''W a)) =
        res (X'.basicOpen_le x₀) (ψ.appLE W _ hW''W c' * (if i = 0 then g else -g)) •
          (universalDerivation (ψ ≫ f)).sec (X'.basicOpen x₀) (res (X'.basicOpen_le x₀) x₀) := by
      fin_cases i
      · exact relation_basicOpen_left f ψ σ a c' hc' hW''W σT hσu hGψ g hg
      · exact relation_basicOpen_right f ψ σ a c' hc' hW''W σT hσv hGψ g hg
    have h2 := congrArg e.symm h
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, hd, hd] at h2
    exact h2
  obtain ⟨Tu, _, _, _, _, _, hrelu⟩ := hTx 0
  obtain ⟨Tv, _, _, _, _, _, hrelv⟩ := hTx 1
  refine ⟨{
    V := V
    isAffineOpen_V := hV
    W := W
    isAffineOpen_W := hW
    le := hWV
    mem := hxW
    σ := σ
    bijective_σ := hσ
    T := T
    isScalarTower := hST
    O := C₁.O
    c := C₁.c
    node := hnode
    g := g
    isUnit_g := hgu
    Tu := Tu
    rel_u := fun a c' hc' => ?_
    Tv := Tv
    rel_v := fun a c' hc' => ?_ }⟩
  · simpa using hrelu a c' hc'
  · simpa using hrelv a c' hc'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Étale node data exist at every non-smooth point** (blueprint
`lem:sm-omega-cd-generator-relation`) of a nodal curve over an integral, normal, locally Noetherian
scheme, smooth over the generic point. -/
theorem nonempty_nodePoleData (f : X ⟶ S) [IsNodalCurve f] [IsIntegral S] [IsLocallyNoetherian S]
    (hS : IsNormalScheme S) (hgen : ∀ x : X, f x = genericPoint S → IsSmoothAt f x) {x : X}
    (hx : x ∉ f.smoothLocus) : Nonempty (NodePoleData f x) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f x) (U := ⊤) trivial
  have hω := isInvertibleModule_dualizingSheaf_of_isNodalCurve f hS hgen
  have : (dualizingSheaf f).IsQuasicoherent :=
    RosenlichtComponent.isQuasicoherent_of_isInvertibleModule _ hω
  obtain ⟨W₀, hW₀, hxW₀, hW₀V, σ₀, hσ₀⟩ :=
    RosenlichtComponent.exists_generator (dualizingSheaf f) (hω x) (O := f ⁻¹ᵁ V) hxV
  obtain ⟨T₀, _, φ, hφ, C, t, hxt, htle⟩ :=
    exists_etaleNodeChart_of_not_mem_smoothLocus f hS hgen hx hV hW₀ hW₀V hxW₀
  have : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.mpr hφ
  have hle' : (⊤ : (Spec (CommRingCat.of T₀)).Opens) ≤
      (Spec.map (CommRingCat.ofHom φ) ≫ hW₀.fromSpec) ⁻¹ᵁ W₀ := by
    intro y _
    change hW₀.fromSpec _ ∈ W₀
    have := Set.mem_range_self (f := hW₀.fromSpec) (Spec.map (CommRingCat.ofHom φ) y)
    rwa [hW₀.range_fromSpec] at this
  have hW'eq := basicOpen_appLE_eq (Spec.map (CommRingCat.ofHom φ) ≫ hW₀.fromSpec) hle' t
  refine nonempty_nodePoleData_of_chart f (Spec.map (CommRingCat.ofHom φ) ≫ hW₀.fromSpec)
    (fun y => ⟨fun h => smoothDescendsAlongEtale_of_isNodalCurve f _ _ y h,
      fun h => Curves.isSmoothAt_comp (Curves.isSmoothAt_of_smooth _ y) h⟩)
    hV (hW₀.basicOpen t) ((X.basicOpen_le t).trans hW₀V) hxt _
    (RosenlichtComponent.bijective_smul_restrict_basicOpen _ hW₀ σ₀ hσ₀ t)
    ((isAffineOpen_top _).basicOpen _) (hW'eq.le.trans inf_le_left) (fun y hy => ?_)
    (C.restrictBasicOpen _)
  obtain ⟨y', rfl⟩ := htle hy
  refine ⟨y', ?_, rfl⟩
  rw [hW'eq]
  exact ⟨hy, trivial⟩

end Existence

end DeJongAlterations.StableModification.Omega.PoleChart
