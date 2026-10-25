import DeJongAlterations.StableModification.Omega.EtaleChart
import DeJongAlterations.StableModification.Omega.InvertibleNodal
import DeJongAlterations.StableModification.Omega.InvertibleSmooth
import DeJongAlterations.StableModification.Curves.SemistableNormalNode
import DeJongAlterations.StableModification.Curves.SemistableNormalScheme
import DeJongAlterations.StableModification.Curves.StandardModels

/-!
# `ω_{X/S}` is invertible on a nodal curve (`lem:sm-omega-invertible`)

Step 4 of lane OM1B (blueprint `sm-omega-invertible.tex`, `lem:sm-omega-invertible`; M. Temkin,
*Stable modification of relative curves*, §1.2, T:1691–1712). Let `S` be an integral, normal,
locally Noetherian scheme and `f : X ⟶ S` a nodal curve (`DeJong.IsNodalCurve`) which is smooth
over the generic point of `S`. Then `ω_{X/S} = j_*(Ω¹_{U/S})` is invertible.

* At a smooth point this is `isInvertibleAt_dualizingSheaf_of_mem_smoothLocus` (relative dimension
  one, `Omega/InvertibleSmooth.lean`).
* At a non-smooth point `x`, a closed point of a geometric fibre over `x` is a formal node (a
  smooth geometric point would make `x` smooth, `mem_smoothLocus_of_tensorChart_spec`), so lane
  SS3's `exists_away_etale_nodeChart` (Stacks, Tag 0CBY) gives an étale neighbourhood `Spec T → X`
  of `x` and an étale map `O[u,v]/(uv − c) → T`. Normality of `Spec T`
  (`isNormalScheme_of_isNodalCurve`, applied to the étale composite) makes `c` a
  non-zero-divisor near the point (`algebraMap_ne_zero_of_isDomain`); after localizing `O`
  (`exists_notMem_mem_nonZeroDivisors_away`, `etale_chartAwayMap`) this is an étale node chart
  of `Spec T_s → S` (`EtaleNodeChart.ofSpec`), and
  `ω` descends (`isInvertibleAt_dualizingSheaf_of_etale_of_surjective`), since smoothness of a nodal
  curve descends along étale maps (`smoothDescendsAlongEtale_of_isNodalCurve`).

The Noetherian hypothesis is used only to spread out the non-zero-divisor `c` from the local ring
of `O` to a basic open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
open DeJongAlterations.Algebra.NodeBlowupChart

universe u

namespace DeJongAlterations.StableModification.Omega

open Curves.SemistableOpen Curves.SemistableNormal Curves
open DeJong (IsNodalCurve IsSmoothAt)

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Curves.SemistableOpen.locallyOfFinitePresentation_spec

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **`ω` is invertible at the non-smooth points of a nodal curve** with smooth generic fibre over
a normal locally Noetherian integral base. -/
theorem isInvertibleAt_dualizingSheaf_of_not_mem_smoothLocus {X S : Scheme.{u}} (f : X ⟶ S)
    [IsNodalCurve f] [IsIntegral S] [IsLocallyNoetherian S] (hS : IsNormalScheme S)
    (hgen : ∀ x : X, f x = genericPoint S → IsSmoothAt f x)
    {x : X} (hx : x ∉ f.smoothLocus) : IsInvertibleAt (dualizingSheaf f) x := by
  -- affine charts
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f x) (U := ⊤) trivial
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := f ⁻¹ᵁ V) hxV
  have hle : W ≤ f ⁻¹ᵁ V := hWV
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
    have hle' : (⊤ : (Spec (CommRingCat.of (chartAway c s Wa))).Opens) ≤ ψ ⁻¹ᵁ W := by
      intro y _
      change hW.fromSpec _ ∈ W
      have := Set.mem_range_self (f := hW.fromSpec) (Spec.map (CommRingCat.ofHom φ') y)
      rwa [hW.range_fromSpec] at this
    set h := ψ.appLE W ⊤ hle' t
    have hW'eq := basicOpen_appLE_eq ψ hle' t
    have hWW' : (Spec (CommRingCat.of (chartAway c s Wa))).basicOpen h ≤ ψ ⁻¹ᵁ X.basicOpen t :=
      hW'eq.le.trans inf_le_left
    refine isInvertibleAt_dualizingSheaf_of_etale_of_surjective f ψ hV (hW.basicOpen t)
      ((X.basicOpen_le t).trans hle) ((isAffineOpen_top _).basicOpen h) hWW'
      (C.restrictBasicOpen h).twoChartAffine
      (fun y _ hy => smoothDescendsAlongEtale_of_isNodalCurve f _ ψ y hy) ?_ hxt
    intro y hy
    obtain ⟨y', rfl⟩ := htle hy
    refine ⟨y', ?_, rfl⟩
    rw [hW'eq]
    exact ⟨hy, trivial⟩

/-- **`ω_{X/S}` is invertible on a nodal curve** (`lem:sm-omega-invertible`). Let `S` be an
integral, normal, locally Noetherian scheme and `f : X ⟶ S` a nodal curve, smooth over the generic
point of `S`. Then `ω_{X/S}` is invertible at every point. -/
theorem isInvertibleAt_dualizingSheaf_of_isNodalCurve {X S : Scheme.{u}} (f : X ⟶ S)
    [IsNodalCurve f] [IsIntegral S] [IsLocallyNoetherian S] (hS : IsNormalScheme S)
    (hgen : ∀ x : X, f x = genericPoint S → IsSmoothAt f x) (x : X) :
    IsInvertibleAt (dualizingSheaf f) x := by
  by_cases hx : x ∈ f.smoothLocus
  · exact isInvertibleAt_dualizingSheaf_of_mem_smoothLocus f
      (fun K _ _ a Z hZ => IsNodalCurve.pureGeometricFibers K a Z hZ) hx
  · exact isInvertibleAt_dualizingSheaf_of_not_mem_smoothLocus f hS hgen hx

/-- **`ω_{X/S}` is an invertible `𝒪_X`-module** (`lem:sm-omega-invertible`) for a nodal curve with
smooth generic fibre over an integral, normal, locally Noetherian scheme. -/
theorem isInvertibleModule_dualizingSheaf_of_isNodalCurve {X S : Scheme.{u}} (f : X ⟶ S)
    [IsNodalCurve f] [IsIntegral S] [IsLocallyNoetherian S] (hS : IsNormalScheme S)
    (hgen : ∀ x : X, f x = genericPoint S → IsSmoothAt f x) :
    IsInvertibleModule (dualizingSheaf f) :=
  (isInvertibleModule_iff _).mpr fun x => isInvertibleAt_dualizingSheaf_of_isNodalCurve f hS hgen x

end DeJongAlterations.StableModification.Omega
