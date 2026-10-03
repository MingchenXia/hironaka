/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MemberInterAlong
import Hironaka.Blowup.NormalCrossingsComparison
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.BlowupSNCTransform
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Invariant.BoundaryCount
import Hironaka.Blowup.LiftedOpenModel
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Blowup.SimultaneousNormalCrossings
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The boundary count along a submanifold transverse to the divisor

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), proof of `pr:resol`, Step 1a (the intersections `H^s_α` of `s`
members restricted to the submanifold; "by blowing up `C = H^s_α` we separate divisors contributing to `H^s_α`, thus
creating new points all with `s(x) < s`") and Step 2 (the monomial case); Bierstone--Milman 2008
(`bierstone-milman08-functoriality`) §5.

Let `π : Y → X` be the blowup along `C`, `C ⊆ N`, `E` a simple normal crossings divisor transverse
to `N` with which `C` has only normal crossings, and `S` a set of indices of members.

* `card_filter_mem_geoStrictTransform_lt_along`: if near `π z` the centre contains `N ∩ H_S`, a point `z` of the
  strict transform `N'` over `C` does not lie on all the `H_i'`, `i ∈ S`. (the hypothesis there is `C ⊇ H_S` near `π
  z`, which fails along `N`, where `C = N ∩ H_S`.)
* `boundaryCount_map_geoStrictTransform_lt_boundaryCount_along`: if near `x = π z` the centre contains the trace on
  `N` of the intersection of the members through `x`, then `s'(z) < s(x)` at every `z ∈ N'` over `C` (Step 1aa
  inside `N`).
* Step 1a's restriction to `N ∩ H_S`: the list `E_S` of the members with index not in `S` is transverse to `N ∩ H_S`
  (`isTransverse_inter_memberInter_of_forall`, any list of such members; `isTransverse_inter_memberInter_drop`), is
  a simple normal crossings divisor (`isSNCDivisor_drop`), and every member of `E` missing from it contains `N ∩
  H_S`; so `(M, N ∩ H_S, E_S, 𝔞, d)` is well formed when `𝔞` is coherent (`isWellFormed_inter_memberInter_drop`, `0
  < n`).

Proof of the drop: in coordinates at `π z` adapted to `C ⊆ N` and `E`
(`SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings`: `C = ℂ^{k_C} × 0`,
`N = ℂ^{k_N} × 0`, the members through `π z` the hyperplanes `{w_{s i} = 0}`, `s i < k_N`) and a
monomial chart `j ≥ k_C` around `z`, `z ∈ N'` gives `j < k_N` and `W_t(z) = 0` for `t ≥ k_N`
(`BlowupSNCTransform.mem_geoStrictTransform_iff_of_chart`), and `z ∈ H_i'` gives `s i ≠ j`,
`W_{s i}(z) = 0`.  Then the points `σ_j(W z + ε e_j)` lie on `N` (their coordinates `t ≥ k_N` are
`W_t(z)·(W_j(z) + ε) = 0`) and on every member of `S`, so near `π z` in `C`; but their `j`-th
coordinate is `ε ≠ 0` with `j ≥ k_C`.  Transversality of `E_S`: in the transversality coordinates
of `E` at a point of `N ∩ H_S`, `N ∩ H_S = L_{S₀ ∪ ⋃_{i ∈ S} T_i}`, and the hyperplane index of a
member `j ∉ S` through the point is none of the `T_i`, `i ∈ S` (two members through a point that agree
near it are the same member, `SimultaneousNormalCrossings.eq_of_eventually_mem_iff`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BoundaryCountAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupStrictSubmanifold BlowupSNCTransform NormalCrossings SimultaneousNormalCrossings MarkedIdeals BoundaryCount NormalCrossingsComparison MemberInterAlong

noncomputable section

variable {n : ℕ}

/-! ### Step 1a's restriction to `N ∩ H_S`: the divisor without the members of `S` -/

section Drop

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **The members outside `S` are transverse to `N ∩ H_S`** (`E` simple normal crossings and
transverse to `N`): for any list `E'` of members `E.get j`, `j ∉ S`.  In the transversality
coordinates at a point, `N ∩ H_S = L_{S₀ ∪ ⋃_{i ∈ S} T_i}`, and the index of a member `j ∉ S`
through the point is not among the `T_i`, `i ∈ S`: two members through a point with the same
hyperplane agree near it, hence are the same member. -/
theorem isTransverse_inter_memberInter_of_forall {N : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) (S : Finset (Fin E.length))
    {E' : List (Set X)} (hE' : ∀ H ∈ E', ∃ j, j ∉ S ∧ E.get j = H) :
    IsTransverse n (N ∩ memberInter E S) E' := by
  classical
  intro x hx
  obtain ⟨S₀, T, ⟨Φ, hΦt, hΦ0, hΦA⟩, hT1⟩ := hT x hx.1
  choose j hjS hjE using fun k : Fin E'.length => hE' (E'.get k) (List.get_mem _ _)
  -- the trace `N ∩ H_S` in the coordinates of `E`
  have hnone : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ N ∩ memberInter E S ↔
          Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S₀ ∪ S.biUnion T)) := by
    intro y hy hyΦ
    have hunion : ∀ w : ComplexModel n, w ∈ coordSubspace (S₀ ∪ S.biUnion T) ↔
        w ∈ coordSubspace S₀ ∧ w ∈ coordSubspace (S.biUnion T) := fun w => by
      simp only [coordSubspace, Finset.mem_union, mem_ofPred_eq]
      exact ⟨fun h => ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩,
        fun h j hj => hj.elim (h.1 j) (h.2 j)⟩
    rw [hunion, mem_coordSubspace_biUnion]
    exact and_congr (hΦA none hx.1 hy hyΦ)
      (forall₂_congr fun i hi => hΦA (some i) (hx.2 i hi) hy hyΦ)
  refine ⟨S₀ ∪ S.biUnion T, fun k => T (j k), ⟨Φ, hΦt, hΦ0, ?_⟩, fun k hk => ?_⟩
  · rintro (_ | k) hxk y hy hyΦ
    · exact hnone hy hyΦ
    · change x ∈ E'.get k at hxk
      change y ∈ E'.get k ↔ _
      rw [← hjE k] at hxk ⊢
      exact hΦA (some (j k)) hxk hy hyΦ
  · rw [← hjE k] at hk
    obtain ⟨hcard, hdisj⟩ := hT1 (j k) hk
    refine ⟨hcard, Finset.disjoint_union_right.mpr ⟨hdisj, ?_⟩⟩
    refine (Finset.disjoint_biUnion_right _ _ _).mpr fun i hi => ?_
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (hT1 i (hx.2 i hi)).1
    show Disjoint (T (j k)) (T i)
    rw [ha, hb, Finset.disjoint_singleton]
    intro hab
    -- the two members have the same hyperplane, so they agree near `x`
    have hTeq : T (j k) = T i := by rw [ha, hb, hab]
    have hopen : IsOpen {y | y ∈ (complexChartAt (n := n) x).val.source ∧
        (complexChartAt (n := n) x).val y ∈ Φ.source} :=
      (complexChartAt (n := n) x).val.isOpen_inter_preimage Φ.isOpen_source
    have hxmem : x ∈ {y | y ∈ (complexChartAt (n := n) x).val.source ∧
        (complexChartAt (n := n) x).val y ∈ Φ.source} :=
      ⟨mem_chart_source _ x, Φ.center_mem_source⟩
    have hev : ∀ᶠ y in 𝓝 x, y ∈ E.get i ↔ y ∈ E.get (j k) := by
      filter_upwards [hopen.mem_nhds hxmem] with y hy
      have h1 : y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (T i) :=
        hΦA (some i) (hx.2 i hi) hy.1 hy.2
      have h2 : y ∈ E.get (j k) ↔
          Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (T (j k)) :=
        hΦA (some (j k)) hk hy.1 hy.2
      rw [h1, h2, hTeq]
    exact hjS k ((eq_of_eventually_mem_iff hE (hx.2 i hi) hk hev) ▸ hi)

/-- **The members outside `S` are transverse to `N ∩ H_S`**, index form:
`E_S = ((finRange #E).filter (· ∉ S)).map E.get`. -/
theorem isTransverse_inter_memberInter_drop {N : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) (S : Finset (Fin E.length)) :
    IsTransverse n (N ∩ memberInter E S)
      (((List.finRange E.length).filter fun i => i ∉ S).map E.get) :=
  isTransverse_inter_memberInter_of_forall hE hT S fun H hH => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hH
    exact ⟨i, by simpa using (List.mem_filter.mp hi).2, rfl⟩

/-- **`E_S` is a simple normal crossings divisor** (a sublist of `E`). -/
theorem isSNCDivisor_drop {E : List (Set X)} (hE : IsSNCDivisor n E) (S : Finset (Fin E.length)) :
    IsSNCDivisor n (((List.finRange E.length).filter fun i => i ∉ S).map E.get) := by
  refine isSNCDivisor_of_sublist hE ?_
  have h := (List.filter_sublist (p := fun i : Fin E.length => decide (i ∉ S))
    (l := List.finRange E.length)).map E.get
  rwa [List.map_get_finRange] at h

/-- **The restriction of a well-formed marked ideal to `N ∩ H_S`, with the divisor `E_S`, is well
formed** (`0 < n`), for any coherent ideal `𝔟` and mark `μ`: Step 1a's
`(M, N ∩ H_S, E_S, 𝓒_N(𝔞), μ_𝓒)` with the coefficient ideal along `N`. -/
theorem isWellFormed_inter_memberInter_drop (hn : 0 < n) {𝔪 : MarkedIdeal n X}
    (h𝔪 : 𝔪.IsWellFormed) (S : Finset (Fin 𝔪.E.length)) {𝔟 : GermIdeal n X}
    (h𝔟 : 𝔟.IsCoherent) (μ : ℕ) :
    ({ N := 𝔪.N ∩ memberInter 𝔪.E S,
       E := ((List.finRange 𝔪.E.length).filter fun i => i ∉ S).map 𝔪.E.get,
       ideal := 𝔟, d := μ } : MarkedIdeal n X).IsWellFormed :=
  ⟨isClosedSubmanifold_inter_memberInter hn h𝔪.isClosedSubmanifold_N.1 h𝔪.isSNCDivisor
      h𝔪.isTransverse S,
    h𝔟, isSNCDivisor_drop h𝔪.isSNCDivisor S,
    isTransverse_inter_memberInter_drop h𝔪.isSNCDivisor h𝔪.isTransverse S⟩

end Drop

/-! ### The drop of the boundary count at points of `N'` over the centre -/

section Blowup

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

open Classical in
theorem card_filter_mem_geoStrictTransform_lt_along (hπ : IsBlowupAlong n C π) {N : Set X}
    (hCN : C ⊆ N) {E : List (Set X)} (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (hnc : HasNormalCrossings n C E) (S : Finset (Fin E.length)) {z : Y} (hz : π z ∈ C)
    (hzN : z ∈ geoStrictTransform π C N)
    (hC : ∀ᶠ y in 𝓝 (π z), y ∈ N → y ∈ memberInter E S → y ∈ C) :
    (S.filter fun i => z ∈ geoStrictTransform π C (E.get i)).card < S.card := by
  refine Finset.card_lt_card (Finset.filter_ssubset.mpr ?_)
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  have hzS : ∀ i ∈ S, π z ∈ E.get i := fun i hi =>
    geoStrictTransform_subset_preimage hπ.contMDiff.continuous (hE.1 _ (List.get_mem _ _))
      (hall i hi)
  have hn : 0 < n := pos_of_isBlowupAlong hπ hz
  obtain ⟨kC, kN, Φ, s, hΦt, -, -, hflat⟩ := isAdaptedAt_of_hasNormalCrossings hn hCN hE hT hnc hz
  have hz' : π z ∈ flatDomain Φ := ⟨mem_chart_source _ (π z), Φ.center_mem_source⟩
  have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kC) :=
    fun hy hyΦ => (hflat hy hyΦ).1
  have hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈
          coordSubspace (Finset.univ.filter fun t : Fin n => kN ≤ t.1)) :=
    fun hy hyΦ => by rw [coordSubspace_eq_complexCoordinatePlane]; exact (hflat hy hyΦ).2.1
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
    exists_monomialLocalInverse hπ hΦt hflatC hz'
  -- every member of `S` passes through `z`: its coordinate is not `j` and vanishes at `W z`
  have hHi : ∀ i ∈ S, s i ≠ j ∧ W z (s i) = 0 := fun i hi => by
    have hflatH : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
        chartAt (ComplexModel n) (π z) y ∈ Φ.source →
          (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace {s i}) :=
      fun hy hyΦ => by
        rw [mem_coordSubspace_singleton]
        exact (hflat hy hyΦ).2.2 i (hzS i hi)
    have h := (mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatH hj hO hWs hWeq hℓ hzO).mp
      (hall i hi)
    exact ⟨fun hsj => h.1 (by simp [hsj]), mem_coordSubspace_singleton.mp h.2⟩
  -- `z ∈ N'`: the chart index is a coordinate of `N`, and the normal coordinates of `N` vanish
  have hNz := (mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatN hj hO hWs hWeq hℓ hzO).mp
    hzN
  have hjN : j.1 < kN := by
    by_contra hle
    exact hNz.1 (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega)
  have hWN : ∀ t : Fin n, kN ≤ t.1 → W z t = 0 := fun t ht =>
    hNz.2 t (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ht)
  have hWj : W z j = 0 := by
    have h := (hflatC (hWeq z hzO).1.1 (hWeq z hzO).1.2).mp hz
    rw [← (hWeq z hzO).2, monomial_mem_plane_iff hj] at h
    exact h
  have hpt : monomial kC j (W z) ∈ Φ.target := by
    rw [(hWeq z hzO).2]
    exact Φ.mapsTo_toFun (hWeq z hzO).1.2
  have hcont : Continuous fun ε : ℂ => monomial kC j (W z + ε • EuclideanSpace.single j (1 : ℂ)) :=
    (contDiff_monomial kC j).continuous.comp (by fun_prop)
  have htend : Tendsto (fun ε : ℂ => monomial kC j (W z + ε • EuclideanSpace.single j (1 : ℂ)))
      (𝓝 0) (𝓝 (monomial kC j (W z))) := by
    simpa using hcont.tendsto 0
  -- the curve `ε ↦ Φ⁻¹(σ_j(W z + ε e_j))`, read back in `X`, tends to `π z`
  have hγ : Tendsto (fun ε : ℂ => (chartAt (ComplexModel n) (π z)).symm
      (Φ.invFun (monomial kC j (W z + ε • EuclideanSpace.single j (1 : ℂ))))) (𝓝 0)
        (𝓝 (π z)) := by
    have h1 : Φ.invFun (monomial kC j (W z)) = chartAt (ComplexModel n) (π z) (π z) := by
      rw [(hWeq z hzO).2]
      exact Φ.left_inv _ (hWeq z hzO).1.2
    have h2 : ContinuousAt Φ.invFun (monomial kC j (W z)) :=
      Φ.invFun_holomorphic.continuousOn.continuousAt (Φ.isOpen_target.mem_nhds hpt)
    have h3 : ContinuousAt (chartAt (ComplexModel n) (π z)).symm
        (Φ.invFun (monomial kC j (W z))) := by
      rw [h1]
      exact (chartAt (ComplexModel n) (π z)).continuousAt_symm (mem_chart_target _ _)
    have h4 : Tendsto (fun ε : ℂ => (chartAt (ComplexModel n) (π z)).symm
        (Φ.invFun (monomial kC j (W z + ε • EuclideanSpace.single j (1 : ℂ))))) (𝓝 0)
          (𝓝 ((chartAt (ComplexModel n) (π z)).symm (Φ.invFun (monomial kC j (W z))))) :=
      (h3.comp h2).tendsto.comp htend
    rwa [h1, (chartAt (ComplexModel n) (π z)).left_inv (mem_chart_source _ _)] at h4
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    ((htend.eventually (Φ.isOpen_target.mem_nhds hpt)).and (hγ.eventually hC))
  have hε : dist ((r / 2 : ℝ) : ℂ) 0 < r := by
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  obtain ⟨hwt, hyC'⟩ := hball hε
  have hsrc := Φ.mapsTo_invFun hwt
  have htgt := hΦt hsrc
  have hys := (chartAt (ComplexModel n) (π z)).map_target htgt
  have hey := (chartAt (ComplexModel n) (π z)).right_inv htgt
  have hyΦ : chartAt (ComplexModel n) (π z) ((chartAt (ComplexModel n) (π z)).symm
      (Φ.invFun (monomial kC j (W z + ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ)))))
        ∈ Φ.source := by
    rw [hey]; exact hsrc
  have hΦy : Φ.toFun (chartAt (ComplexModel n) (π z) ((chartAt (ComplexModel n) (π z)).symm
      (Φ.invFun (monomial kC j (W z + ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ)))))) =
      monomial kC j (W z + ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ)) := by
    rw [hey]; exact Φ.right_inv _ hwt
  -- the point lies on `N`: its coordinates `t ≥ k_N` are `W_t(z) · (W_j(z) + ε) = 0`
  have hyN : (chartAt (ComplexModel n) (π z)).symm
      (Φ.invFun (monomial kC j (W z + ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ))))
        ∈ N := by
    refine (hflatN hys hyΦ).mpr ?_
    rw [hΦy]
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have htj : t ≠ j := fun h => by rw [h] at ht; omega
    simp [monomial_apply, htj, hWN t ht]
  have hyC : (chartAt (ComplexModel n) (π z)).symm
      (Φ.invFun (monomial kC j (W z + ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single j (1 : ℂ))))
        ∈ C := by
    refine hyC' hyN fun i hi => ?_
    refine ((hflat hys hyΦ).2.2 i (hzS i hi)).mpr ?_
    rw [hΦy]
    obtain ⟨hsj, hW0⟩ := hHi i hi
    simp [monomial_apply, hsj, hW0]
  have h := (hflatC hys hyΦ).mp hyC
  rw [hΦy, monomial_mem_plane_iff hj] at h
  simp [hWj] at h
  linarith

open Classical in
/-- **Step 1aa inside `N`: blowing up the trace on `N` of the intersection of the members through a
point lowers the count at the points of `N'` over it.**  If near `x = π z` the centre contains
`N ∩ ⋂_{x ∈ H_i} H_i`, then `s'(z) < s(x)` for `z ∈ N'` over `C`. -/
theorem boundaryCount_map_geoStrictTransform_lt_boundaryCount_along (hπ : IsBlowupAlong n C π)
    {N : Set X} (hCN : C ⊆ N) {E : List (Set X)} (hE : IsSNCDivisor n E)
    (hT : IsTransverse n N E) (hnc : HasNormalCrossings n C E) {z : Y} (hz : π z ∈ C)
    (hzN : z ∈ geoStrictTransform π C N)
    (hC : ∀ᶠ y in 𝓝 (π z), y ∈ N → (∀ i : Fin E.length, π z ∈ E.get i → y ∈ E.get i) → y ∈ C) :
    boundaryCount (E.map (geoStrictTransform π C)) z < boundaryCount E (π z) := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin E.length),
      S = Finset.univ.filter fun i : Fin E.length => π z ∈ E.get i := ⟨_, rfl⟩
  have hcount : boundaryCount E (π z) = S.card := by rw [hS]; rfl
  have hsub : (Finset.univ.filter fun i : Fin E.length => z ∈ geoStrictTransform π C (E.get i)) =
      S.filter fun i => z ∈ geoStrictTransform π C (E.get i) := by
    ext i
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨geoStrictTransform_subset_preimage hπ.contMDiff.continuous
      (hE.1 _ (List.get_mem _ _)) h, h⟩, fun h => h.2⟩
  rw [boundaryCount_map, hsub, hcount]
  refine card_filter_mem_geoStrictTransform_lt_along hπ hCN hE hT hnc S hz hzN ?_
  filter_upwards [hC] with y hy hyN hyS
  exact hy hyN fun i hi => hyS i (by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩)

end Blowup

end

end Hironaka.BoundaryCountAlong
