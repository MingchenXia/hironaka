/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MemberPrincipalPullbackExact
import Hironaka.Invariant.MemberPullback
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupSNCTransform

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.MemberPullback
open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupExceptionalDivisor BlowupStrictSubmanifold BlowupStrictIdeal BlowupSNCTransform NormalCrossings SimultaneousNormalCrossings RelativePrincipalizationSpan DerivativeIdeal
noncomputable section
variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {C : Set X} {π : Y → X}
theorem exists_chart_generators (hπ : IsBlowupAlong n C π) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hnc : HasNormalCrossings n C E) (i : Fin E.length) {z : Y}
    (hzC : π z ∈ C) (hzH : π z ∈ E.get i) :
    ∃ (k : ℕ) (t j : Fin n) (W : Y → ComplexModel n), k ≤ j.1 ∧
      ((∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i) ↔ k ≤ t.1) ∧
      HolomorphicAt n (fun y => W y t) z ∧ HolomorphicAt n (fun y => W y j) z ∧
      (∀ g, (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (E.get i))).mem z g ↔
        IsInSpanAt (n := n) (· = fun y => monomial k j (W y) t) z g) ∧
      (∀ g, (exceptionalDivisor hπ).ideal.mem z g ↔
        IsInSpanAt (n := n) (· = fun y => W y j) z g) ∧
      (∀ g, (vanishingIdeal (n := n) (geoStrictTransform π C (E.get i))).mem z g ↔
        IsInSpanAt (n := n) (· = if t = j then (fun _ => (1 : ℂ)) else fun y => W y t) z g) := by
  classical
  have hn : 0 < n := pos_of_isBlowupAlong hπ hzC
  obtain ⟨kC, kN, Φ, s, hΦt, -, -, hflat⟩ := isAdaptedAt_of_hasNormalCrossings hn (subset_univ C) hE
    (isTransverse_univ_of_isSNCDivisor hE) hnc hzC
  set t := s i with ht
  have hz' : π z ∈ flatDomain Φ := ⟨mem_chart_source _ (π z), Φ.center_mem_source⟩
  have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kC) :=
    fun hy hyΦ => (hflat hy hyΦ).1
  have hflatH : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) t = 0) :=
    fun hy hyΦ => (hflat hy hyΦ).2.2 i hzH
  have hflatH' : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace {t}) :=
    fun hy hyΦ => by rw [mem_coordSubspace_singleton]; exact hflatH hy hyΦ
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
    exists_monomialLocalInverse hπ hΦt hflatC hz'
  have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ kC j := fun z' hz'' => by
    show monomial kC j (W z') ∈ Φ.target
    rw [(hWeq z' hz'').2]; exact Φ.mapsTo_toFun (hWeq z' hz'').1.2
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦt hflatC hj
  have hFinj : ∀ u ∈ O, Function.Injective (fderiv ℂ
      (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ)) (chartAt (ComplexModel n) u u)) :=
    fun u hu => injective_fderiv_of_monomialInverse hO hWs hWmem hℓs (hℓ ℓ hℓs hℓπ) hu
  refine ⟨kC, t, j, W, hj, ?_, holomorphicAt_coord hO hWs t hzO, holomorphicAt_coord hO hWs j hzO,
    ?_, ?_, ?_⟩
  · -- `C ⊆ H` near `π z` iff the coordinate of `H` is not a free coordinate of `C`
    constructor
    · intro hCH
      by_contra hlt
      push Not at hlt
      have hpt : Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) ∈ Φ.target :=
        Φ.mapsTo_toFun hz'.2
      have hpC := (hflatC hz'.1 hz'.2).mp hzC
      have hpH := (hflatH hz'.1 hz'.2).mp hzH
      -- the curve `ε ↦ e⁻¹ Φ⁻¹ (Φ (e x) + ε e_t)` runs inside `C` and leaves `H`
      have hwc : Continuous fun ε : ℂ => Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) +
          ε • EuclideanSpace.single t (1 : ℂ) := by fun_prop
      have htend : Tendsto (fun ε : ℂ => Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) +
          ε • EuclideanSpace.single t (1 : ℂ)) (𝓝 0)
          (𝓝 (Φ.toFun (chartAt (ComplexModel n) (π z) (π z)))) := by
        simpa using hwc.tendsto 0
      have hinv : Φ.invFun (Φ.toFun (chartAt (ComplexModel n) (π z) (π z))) =
          chartAt (ComplexModel n) (π z) (π z) := Φ.left_inv _ hz'.2
      have hψ : Tendsto (fun ε : ℂ => (chartAt (ComplexModel n) (π z)).symm
          (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) +
            ε • EuclideanSpace.single t (1 : ℂ)))) (𝓝 0) (𝓝 (π z)) := by
        have h1 : ContinuousAt Φ.invFun (Φ.toFun (chartAt (ComplexModel n) (π z) (π z))) :=
          Φ.invFun_holomorphic.continuousOn.continuousAt (Φ.isOpen_target.mem_nhds hpt)
        have h2 : ContinuousAt (chartAt (ComplexModel n) (π z)).symm
            (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) (π z) (π z)))) := by
          rw [hinv]
          exact (chartAt (ComplexModel n) (π z)).continuousAt_symm
            ((chartAt (ComplexModel n) (π z)).map_source hz'.1)
        have h3 := (h2.comp h1).tendsto.comp htend
        simpa [Function.comp_def, hinv, (chartAt (ComplexModel n) (π z)).left_inv hz'.1] using h3
      have hwt : ∀ᶠ ε in 𝓝 (0 : ℂ), Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) +
          ε • EuclideanSpace.single t (1 : ℂ) ∈ Φ.target := by
        exact htend (Φ.isOpen_target.mem_nhds hpt)
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp ((hψ.eventually hCH).and hwt)
      have hε : dist ((r / 2 : ℝ) : ℂ) 0 < r := by
        rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      obtain ⟨hCHε, hwtε⟩ := hball hε
      have hsrc := Φ.mapsTo_invFun hwtε
      have htgt := hΦt hsrc
      have hys := (chartAt (ComplexModel n) (π z)).map_target htgt
      have hey := (chartAt (ComplexModel n) (π z)).right_inv htgt
      have hyΦ : chartAt (ComplexModel n) (π z) ((chartAt (ComplexModel n) (π z)).symm
          (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) +
            ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single t (1 : ℂ)))) ∈ Φ.source := by
        rw [hey]; exact hsrc
      have hΦy : Φ.toFun (chartAt (ComplexModel n) (π z) ((chartAt (ComplexModel n) (π z)).symm
          (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) +
            ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single t (1 : ℂ))))) =
          Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) +
            ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single t (1 : ℂ) := by
        rw [hey]; exact Φ.right_inv _ hwtε
      have hyC := (hflatC hys hyΦ).mpr (by
        rw [hΦy]
        intro l hl
        have hlt' : l ≠ t := fun h => by rw [h] at hl; omega
        simp [hpC l hl, hlt'])
      have hyH := (hflatH hys hyΦ).mp (hCHε hyC)
      rw [hΦy] at hyH
      simp [hpH] at hyH
      linarith
    · intro hkt
      filter_upwards [(isOpen_flatDomain Φ).mem_nhds hz'] with y hy hyC
      refine (hflatH hy.1 hy.2).mpr ?_
      exact (hflatC hy.1 hy.2).mp hyC t hkt
  · intro g
    rw [pullback_mem_iff_of_generator hπ.contMDiff (holomorphicAt_flatCoord Φ t hz')
      (vanishingIdeal_mem_iff_flatCoord Φ hflatH hz') g]
    refine isInSpanAt_eq_congr ?_ g
    filter_upwards [hO.mem_nhds hzO] with y hy
    simp only [Function.comp_apply, flatCoord]
    rw [← (hWeq y hy).2]
  · intro g
    rw [exceptionalDivisor_mem_iff_of_chart hπ hΦt hflatC hj hO hWs hWeq hzO g,
      isInSpanAt_range_one_iff]
  · intro g
    have hHu : ∀ u ∈ O, (u ∈ geoStrictTransform π C (E.get i) ↔ j ∉ ({t} : Finset (Fin n)) ∧
        W u ∈ coordSubspace {t}) := fun u hu =>
      mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatH' hj hO hWs hWeq hℓ hu
    by_cases htj : t = j
    · rw [if_pos htj, vanishingIdeal_mem_iff_of_disjoint hO (fun u hu hH => ((hHu u hu).mp hH).1
        (by simp [htj])) hzO g, isInSpanAt_range_one_iff]
    · rw [if_neg htj]
      have hHu' : ∀ u ∈ O, (u ∈ geoStrictTransform π C (E.get i) ↔ W u t = 0) := fun u hu => by
        rw [hHu u hu, mem_coordSubspace_singleton]
        exact ⟨fun h => h.2, fun h => ⟨by simp [Ne.symm htj], h⟩⟩
      rw [← LocalGiraudTransform.vanishingIdeal_zeroSet_mem_iff hO
        (fun u hu => holomorphicAt_coord hO hWs t hu)
        (fun u hu _ => let ⟨v, hv⟩ := exists_chartDeriv_coord_ne_zero hWs hu (hFinj u hu) t
          ⟨complexChartAt (n := n) u, v, mem_complexChartAt_source u, hv⟩) hzO g]
      refine vanishingIdeal_mem_congr ?_ g
      filter_upwards [hO.mem_nhds hzO] with u hu
      exact ⟨fun h => ⟨(hHu' u hu).mp h, hu⟩, fun h => (hHu' u hu).mpr h.1⟩


theorem mem_pullback_member_iff_of_not_subset (hπ : IsBlowupAlong n C π) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hnc : HasNormalCrossings n C E) (i : Fin E.length) {z : Y}
    (hCH : ¬ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (E.get i))).mem z g ↔
      (vanishingIdeal (n := n) (geoStrictTransform π C (E.get i))).mem z g := by
  have hHc : IsClosed (E.get i) := hE.1 _ (List.get_mem _ _)
  have hzC : π z ∈ C := by
    by_contra hzC
    exact hCH (by
      filter_upwards [hπ.1.1.isOpen_compl.mem_nhds hzC] with y hy hyC
      exact absurd hyC hy)
  by_cases hzH : π z ∈ E.get i
  · obtain ⟨k, t, j, W, hkj, hdich, hWt, -, hpb, -, hH'⟩ :=
      exists_chart_generators hπ hE hnc i hzC hzH
    have hkt : ¬ k ≤ t.1 := fun h => hCH (hdich.mpr h)
    have htj : t ≠ j := fun h => hkt (h ▸ hkj)
    rw [hpb, hH', if_neg htj]
    refine isInSpanAt_eq_congr (Eventually.of_forall fun y => ?_) g
    simp [monomial_apply, hkt]
  · -- both ideals are the unit ideal at `z`
    have hgen : ∀ g', (vanishingIdeal (n := n) (E.get i)).mem (π z) g' ↔
        IsInSpanAt (n := n) (· = fun _ => (1 : ℂ)) (π z) g' := fun g' => by
      rw [vanishingIdeal_mem_iff_of_disjoint hHc.isOpen_compl (fun y hy => hy) hzH g',
        isInSpanAt_range_one_iff]
    rw [pullback_mem_iff_of_generator hπ.contMDiff (holomorphicAt_const 1) hgen g]
    have hopen : IsOpen (π ⁻¹' (E.get i)ᶜ) := hHc.isOpen_compl.preimage hπ.contMDiff.continuous
    rw [vanishingIdeal_mem_iff_of_disjoint hopen (fun y hy hyH' =>
      hy (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hHc hyH')) hzH g,
      isInSpanAt_range_one_iff]
    rfl

end
end Hironaka.MemberPullback
