/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MonomialPart
import Hironaka.Blowup.SimultaneousNormalCrossings
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.BlowupSNCTransform
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Invariant.CompanionReduction
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Blowup.LiftedOpenModel
import Hironaka.MarkedIdeal.LocalGiraudTransform
import Hironaka.Invariant.MemberPullback
import Hironaka.Blowup.NormalCrossings
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Monomial ideals under the blowup of a centre with normal crossings: the generator form

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), the monomial charts of `le:inclusions` and Step 2b of the proof
of `pr:resol` (the transform of a monomial marked ideal); Bierstone--Milman 2008
(`bierstone-milman08-functoriality`) §5.

Let `π : Y → X` be the blowup along `C`, `E` a simple normal crossings divisor with which `C` has
only normal crossings, and `z ∈ Y` over `C`.

* `exists_monomial_chart`: there are a monomial chart `W` (holomorphic on an open `U ∋ z`, with
  injective differential at `z`, so `W - W z` is a coordinate system at `z`), an index `j` and
  indices `s i` of the members, such that `𝒪(-D) = (W_j)` at every point of `U`; for every member
  `E_i` whose strict transform `E_i'` passes through `z`, `𝓘_{E_i'} = (W_{s i})` on `U`, with
  `s i ≠ j`, `W_{s i}(z) = 0`, the `s i` distinct; and for local generators `u_i` of `𝓘_{E_i}` at
  `π z` and exponents `a_i`,
  `(∏_{π z ∈ E_i} u_i^{a_i}) ∘ π = c · W_j^{e} · ∏_{z ∈ E_i'} W_{s i}^{a_i}` near `z`, with
  `c(z) ≠ 0` and `e = ∑_{π z ∈ E_i, C ⊆ E_i near π z} a_i`.
* Helpers: `mem_centre_iff_of_generator`, `mem_iff_of_vanishingIdeal_eq` (zero sets from generators),
  `prod_map_append_singleton`.

Proof of the chart statement: coordinates `Φ` at `π z` adapted to `C` and `E`
(`SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings`), `E_i = {Φ_{s i} = 0}`; the
monomial chart `σⱼ` through `z` (`exists_monomialLocalInverse`), `Φ ∘ π = σⱼ(W)`; then
`Φ_{s i} ∘ π = W_{s i} W_j` (`k_C ≤ s i ≠ j`, the members containing `C`), `= W_j` (`s i = j`),
or `= W_{s i}` (`s i < k_C`); the generators `u_i` differ from `Φ_{s i}` by units
(`exists_unit_of_isInSpanAt`), and the factors `W_{s i}` with `W_{s i}(z) ≠ 0` are units too.
"`C ⊆ E_i` near `π z` iff `k_C ≤ s i`" is `eventually_subset_iff_le` (as in `MemberPullback`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MonomialBlowup

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupFlatCoordinates Hironaka.BlowupMonomialCharts Hironaka.BlowupLocalSurjectivity Hironaka.BlowupExceptionalDivisor Hironaka.BlowupStrictSubmanifold Hironaka.BlowupStrictIdeal Hironaka.BlowupSNCTransform Hironaka.NormalCrossings Hironaka.SimultaneousNormalCrossings Hironaka.MemberPullback Hironaka.MonomialPart Hironaka.GermIdealOrder Hironaka.IdealWeightPowers Hironaka.BlowupControlledTransform Hironaka.InvertibleIdealQuotient

noncomputable section

variable {n : ℕ}

/-! ### Generators of one principal ideal differ by a unit -/

section Germ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Two generators of one principal ideal differ by a unit**: if `u ∈ (φ)` and `φ ∈ (u)` at `x`,
and `φ` vanishes identically near no point (frequently nonzero near `x`), then `u = c φ` near `x`
with `c(x) ≠ 0`. -/
theorem exists_unit_of_isInSpanAt {x : M} {u φ : M → ℂ}
    (huφ : IsInSpanAt (n := n) (· = φ) x u) (hφu : IsInSpanAt (n := n) (· = u) x φ)
    (hne : ∃ᶠ y in 𝓝 x, φ y ≠ 0) :
    ∃ c : M → ℂ, HolomorphicAt n c x ∧ c x ≠ 0 ∧ u =ᶠ[𝓝 x] fun y => c y * φ y := by
  obtain ⟨-, c, hc, hcu⟩ := isInSpanAt_eq_iff.mp huφ
  obtain ⟨hφ, c', hc', hcφ⟩ := isInSpanAt_eq_iff.mp hφu
  refine ⟨c, hc, fun h0 => ?_, hcu⟩
  have hf : HolomorphicAt n (fun y => 1 - c' y * c y) x :=
    GiraudAlong.holomorphicAt_sub (holomorphicAt_const 1) (hc'.mul hc)
  have h1 : (fun y => (1 - c' y * c y) * φ y) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hcu, hcφ] with y h1 h2
    have h3 : φ y = c' y * (c y * φ y) := by rw [← h1]; exact h2
    show (1 - c' y * c y) * φ y = 0
    linear_combination h3
  have h3 := (eventually_eq_zero_of_mul_eventually_eq_zero hf hφ hne h1).self_of_nhds
  simp [h0] at h3

end Germ

/-! ### Members containing the centre, in adapted coordinates -/

section Adapted

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **`C ⊆ H` near `x` iff the coordinate of `H` is not a free coordinate of `C`**: in coordinates
`Φ` at `x` in which `C = ℂᵏ × 0` and `H = {w_t = 0}` (`x ∈ C ∩ H`). -/
theorem eventually_subset_iff_le {x : X}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}
    (hΦt : Φ.source ⊆ (chartAt (ComplexModel n) x).target) {C H : Set X} {k : ℕ} {t : Fin n}
    (hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))
    (hflatH : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ H ↔ Φ.toFun (chartAt (ComplexModel n) x y) t = 0))
    (hxC : x ∈ C) (hxH : x ∈ H) :
    (∀ᶠ y in 𝓝 x, y ∈ C → y ∈ H) ↔ k ≤ t.1 := by
  have hz' : x ∈ flatDomain Φ := ⟨mem_chart_source _ x, Φ.center_mem_source⟩
  constructor
  · intro hCH
    by_contra hlt
    push Not at hlt
    have hpt : Φ.toFun (chartAt (ComplexModel n) x x) ∈ Φ.target := Φ.mapsTo_toFun hz'.2
    have hpC := (hflatC hz'.1 hz'.2).mp hxC
    have hpH := (hflatH hz'.1 hz'.2).mp hxH
    -- the curve `ε ↦ e⁻¹ Φ⁻¹ (Φ (e x) + ε e_t)` runs inside `C` and leaves `H`
    have hwc : Continuous fun ε : ℂ => Φ.toFun (chartAt (ComplexModel n) x x) +
        ε • EuclideanSpace.single t (1 : ℂ) := by fun_prop
    have htend : Tendsto (fun ε : ℂ => Φ.toFun (chartAt (ComplexModel n) x x) +
        ε • EuclideanSpace.single t (1 : ℂ)) (𝓝 0)
        (𝓝 (Φ.toFun (chartAt (ComplexModel n) x x))) := by
      simpa using hwc.tendsto 0
    have hinv : Φ.invFun (Φ.toFun (chartAt (ComplexModel n) x x)) =
        chartAt (ComplexModel n) x x := Φ.left_inv _ hz'.2
    have hψ : Tendsto (fun ε : ℂ => (chartAt (ComplexModel n) x).symm
        (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) x x) +
          ε • EuclideanSpace.single t (1 : ℂ)))) (𝓝 0) (𝓝 x) := by
      have h1 : ContinuousAt Φ.invFun (Φ.toFun (chartAt (ComplexModel n) x x)) :=
        Φ.invFun_holomorphic.continuousOn.continuousAt (Φ.isOpen_target.mem_nhds hpt)
      have h2 : ContinuousAt (chartAt (ComplexModel n) x).symm
          (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) x x))) := by
        rw [hinv]
        exact (chartAt (ComplexModel n) x).continuousAt_symm
          ((chartAt (ComplexModel n) x).map_source hz'.1)
      have h3 := (h2.comp h1).tendsto.comp htend
      simpa [Function.comp_def, hinv, (chartAt (ComplexModel n) x).left_inv hz'.1] using h3
    have hwt : ∀ᶠ ε in 𝓝 (0 : ℂ), Φ.toFun (chartAt (ComplexModel n) x x) +
        ε • EuclideanSpace.single t (1 : ℂ) ∈ Φ.target :=
      htend (Φ.isOpen_target.mem_nhds hpt)
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp ((hψ.eventually hCH).and hwt)
    have hε : dist ((r / 2 : ℝ) : ℂ) 0 < r := by
      rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    obtain ⟨hCHε, hwtε⟩ := hball hε
    have hsrc := Φ.mapsTo_invFun hwtε
    have htgt := hΦt hsrc
    have hys := (chartAt (ComplexModel n) x).map_target htgt
    have hey := (chartAt (ComplexModel n) x).right_inv htgt
    have hyΦ : chartAt (ComplexModel n) x ((chartAt (ComplexModel n) x).symm
        (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) x x) +
          ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single t (1 : ℂ)))) ∈ Φ.source := by
      rw [hey]; exact hsrc
    have hΦy : Φ.toFun (chartAt (ComplexModel n) x ((chartAt (ComplexModel n) x).symm
        (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) x x) +
          ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single t (1 : ℂ))))) =
        Φ.toFun (chartAt (ComplexModel n) x x) +
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

end Adapted

/-! ### The monomial chart over a point of the centre -/

section Chart

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

open Classical in
/-- **The monomial chart over a point of the centre** (the ambient half of `hir:monomial-blowup`,
in the generator form).  Let `π` be the blowup along `C`, `E` a simple normal crossings divisor
with which `C` has only normal crossings, and `π z ∈ C`.  There are a monomial chart `W` on an open
`U ∋ z` (with injective differential at `z`), an index `j` and indices `s i` such that:
`W_j(z) = 0` and `𝒪(-D) = (W_j)` on `U`; for every member `E_i` with `z ∈ E_i'`: `π z ∈ E_i`,
`s i ≠ j`, `W_{s i}(z) = 0` and `𝓘_{E_i'} = (W_{s i})` on `U`; the `s i` of the members through
`π z` are distinct; and for holomorphic generators `u_i` of `𝓘_{E_i}` at `π z` and exponents
`a_i`, `(∏_{π z ∈ E_i} u_i^{a_i}) ∘ π = c · W_j^e · ∏_{z ∈ E_i'} W_{s i}^{a_i}` near `z`,
`c(z) ≠ 0`, `e = ∑_{π z ∈ E_i, C ⊆ E_i near π z} a_i`. -/
theorem exists_monomial_chart (hπ : IsBlowupAlong n C π) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hnc : HasNormalCrossings n C E) {z : Y} (hzC : π z ∈ C) :
    ∃ (j : Fin n) (s : Fin E.length → Fin n) (W : Y → ComplexModel n) (U : Set Y),
      IsOpen U ∧ z ∈ U ∧
      (∀ y ∈ U, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W y) ∧
      Function.Injective (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ))
        (chartAt (ComplexModel n) z z)) ∧
      W z j = 0 ∧
      (∀ y ∈ U, ∀ g, (exceptionalDivisor hπ).ideal.mem y g ↔
        IsInSpanAt (n := n) (· = fun w => W w j) y g) ∧
      (∀ i, z ∈ geoStrictTransform π C (E.get i) → π z ∈ E.get i ∧ s i ≠ j ∧ W z (s i) = 0 ∧
        ∀ y ∈ U, ∀ g, (vanishingIdeal (n := n) (geoStrictTransform π C (E.get i))).mem y g ↔
          IsInSpanAt (n := n) (· = fun w => W w (s i)) y g) ∧
      Set.InjOn s {i | π z ∈ E.get i} ∧
      ∀ (a : Fin E.length → ℕ) (u : Fin E.length → X → ℂ),
        (∀ i, π z ∈ E.get i → HolomorphicAt n (u i) (π z) ∧
          ∀ g, (vanishingIdeal (n := n) (E.get i)).mem (π z) g ↔
            IsInSpanAt (n := n) (· = u i) (π z) g) →
        ∃ c : Y → ℂ, HolomorphicAt n c z ∧ c z ≠ 0 ∧
          (fun w => ∏ i ∈ Finset.univ.filter (fun i => π z ∈ E.get i), u i (π w) ^ a i)
            =ᶠ[𝓝 z] fun w => c w *
              W w j ^ (∑ i ∈ Finset.univ.filter
                (fun i => π z ∈ E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i), a i) *
              ∏ i ∈ Finset.univ.filter (fun i => z ∈ geoStrictTransform π C (E.get i)),
                W w (s i) ^ a i := by
  classical
  have hn : 0 < n := pos_of_isBlowupAlong hπ hzC
  obtain ⟨kC, kN, Φ, s, hΦt, -, hsinj, hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn (subset_univ C) hE (isTransverse_univ_of_isSNCDivisor hE)
      hnc hzC
  have hx' : π z ∈ flatDomain Φ := ⟨mem_chart_source _ (π z), Φ.center_mem_source⟩
  have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kC) :=
    fun hy hyΦ => (hflat hy hyΦ).1
  have hflatH : ∀ i, π z ∈ E.get i → ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) (s i) = 0) :=
    fun i hi y hy hyΦ => (hflat hy hyΦ).2.2 i hi
  have hflatH' : ∀ i, π z ∈ E.get i → ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace {s i}) :=
    fun i hi y hy hyΦ => by rw [mem_coordSubspace_singleton]; exact hflatH i hi hy hyΦ
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
    exists_monomialLocalInverse hπ hΦt hflatC hx'
  have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ kC j := fun z' hz'' => by
    show monomial kC j (W z') ∈ Φ.target
    rw [(hWeq z' hz'').2]; exact Φ.mapsTo_toFun (hWeq z' hz'').1.2
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦt hflatC hj
  have hFinj : ∀ u ∈ O, Function.Injective (fderiv ℂ
      (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ)) (chartAt (ComplexModel n) u u)) :=
    fun u hu => injective_fderiv_of_monomialInverse hO hWs hWmem hℓs (hℓ ℓ hℓs hℓπ) hu
  have hCu : ∀ u ∈ O, (π u ∈ C ↔ W u j = 0) := fun u hu => by
    rw [hflatC (hWeq u hu).1.1 (hWeq u hu).1.2, ← (hWeq u hu).2, monomial_mem_plane_iff hj]
  have hWzj : W z j = 0 := (hCu z hzO).mp hzC
  have hHu : ∀ i, π z ∈ E.get i → ∀ u ∈ O, (u ∈ geoStrictTransform π C (E.get i) ↔
      j ∉ ({s i} : Finset (Fin n)) ∧ W u ∈ coordSubspace {s i}) :=
    fun i hi u hu => mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC (hflatH' i hi) hj hO hWs
      hWeq hℓ hu
  have hzH : ∀ i, z ∈ geoStrictTransform π C (E.get i) → π z ∈ E.get i := fun i hi =>
    geoStrictTransform_subset_preimage hπ.contMDiff.continuous (hE.1 _ (List.get_mem _ _)) hi
  -- the strict transform through `z`, in the chart
  have hS' : ∀ i, π z ∈ E.get i →
      (z ∈ geoStrictTransform π C (E.get i) ↔ s i ≠ j ∧ W z (s i) = 0) := by
    intro i hi
    rw [hHu i hi z hzO, mem_coordSubspace_singleton, Finset.mem_singleton]
    exact ⟨fun h => ⟨fun h' => h.1 h'.symm, h.2⟩, fun h => ⟨fun h' => h.1 h'.symm, h.2⟩⟩
  refine ⟨j, s, W, O, hO, hzO, hWs, hFinj z hzO, hWzj, fun y hy g => ?_, fun i hi => ?_, hsinj,
    fun a u hu => ?_⟩
  · rw [exceptionalDivisor_mem_iff_of_chart hπ hΦt hflatC hj hO hWs hWeq hy g,
      isInSpanAt_range_one_iff]
  · have hxi := hzH i hi
    obtain ⟨hsj, hWs0⟩ := (hS' i hxi).mp hi
    refine ⟨hxi, hsj, hWs0, fun y hy g => ?_⟩
    have hHu' : ∀ u ∈ O, (u ∈ geoStrictTransform π C (E.get i) ↔ W u (s i) = 0) := fun u hu => by
      rw [hHu i hxi u hu, mem_coordSubspace_singleton, Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨fun h' => hsj h'.symm, h⟩⟩
    rw [← LocalGiraudTransform.vanishingIdeal_zeroSet_mem_iff hO
      (fun u hu => holomorphicAt_coord hO hWs (s i) hu)
      (fun u hu _ => let ⟨v, hv⟩ := exists_chartDeriv_coord_ne_zero hWs hu (hFinj u hu) (s i)
        ⟨complexChartAt (n := n) u, v, mem_complexChartAt_source u, hv⟩) hy g]
    refine vanishingIdeal_mem_congr ?_ g
    filter_upwards [hO.mem_nhds hy] with u hu
    exact ⟨fun h => ⟨(hHu' u hu).mp h, hu⟩, fun h => (hHu' u hu).mpr h.1⟩
  · -- unit factors `u i = c i · Φ_{s i}` near `π z`
    have hunit : ∀ i, ∃ c : X → ℂ, π z ∈ E.get i → HolomorphicAt n c (π z) ∧ c (π z) ≠ 0 ∧
        u i =ᶠ[𝓝 (π z)] fun y => c y * flatCoord Φ (s i) y := by
      intro i
      by_cases hi : π z ∈ E.get i
      · obtain ⟨huhol, hgen⟩ := hu i hi
        have hgenφ := vanishingIdeal_mem_iff_flatCoord Φ (hflatH i hi) hx'
        have hφhol : HolomorphicAt n (flatCoord Φ (s i)) (π z) :=
          holomorphicAt_flatCoord Φ (s i) hx'
        have huI : (vanishingIdeal (n := n) (E.get i)).mem (π z) (u i) :=
          (hgen (u i)).mpr (isInSpanAt_self rfl huhol)
        have hφI : (vanishingIdeal (n := n) (E.get i)).mem (π z) (flatCoord Φ (s i)) :=
          (hgenφ _).mpr (isInSpanAt_self rfl hφhol)
        have hne : ∃ᶠ y in 𝓝 (π z), flatCoord Φ (s i) y ≠ 0 :=
          (frequently_flatMap_ne_zero hΦt hx' {s i}).mono fun y hy =>
            hy.2.1 (s i) (Finset.mem_singleton_self _)
        obtain ⟨c, hc, hcz, hcu⟩ :=
          exists_unit_of_isInSpanAt ((hgenφ (u i)).mp huI) ((hgen _).mp hφI) hne
        exact ⟨c, fun _ => ⟨hc, hcz, hcu⟩⟩
      · exact ⟨fun _ => 1, fun h => absurd h hi⟩
    choose c hc using hunit
    -- `C ⊆ E_i` near `π z` iff `k_C ≤ s i`
    have hdich : ∀ i, π z ∈ E.get i →
        ((∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i) ↔ kC ≤ (s i).1) :=
      fun i hi => eventually_subset_iff_le hΦt hflatC (hflatH i hi) hzC hi
    -- the unit part of each factor
    let g : Fin E.length → Y → ℂ := fun i =>
      if kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0 then fun w => W w (s i) ^ a i else fun _ => 1
    have hgpos : ∀ i, (kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0) → g i = fun w => W w (s i) ^ a i :=
      fun i hP => by simp only [g]; rw [if_pos hP]
    have hgneg : ∀ i, ¬ (kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0) → g i = fun _ => 1 :=
      fun i hP => by simp only [g]; rw [if_neg hP]
    have hghol : ∀ i, HolomorphicAt n (g i) z := by
      intro i
      by_cases hP : kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0
      · rw [hgpos i hP]
        exact CompanionReduction.holomorphicAt_pow_of (holomorphicAt_coord hO hWs (s i) hzO) (a i)
      · rw [hgneg i hP]
        exact holomorphicAt_const 1
    have hgz : ∀ i, g i z ≠ 0 := by
      intro i
      by_cases hP : kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0
      · rw [hgpos i hP]
        exact pow_ne_zero _ hP.2.2
      · rw [hgneg i hP]
        exact one_ne_zero
    -- the factor of each member through `π z`
    have hπt : Tendsto π (𝓝 z) (𝓝 (π z)) := hπ.contMDiff.continuous.tendsto z
    have hper : ∀ i ∈ Finset.univ.filter (fun i => π z ∈ E.get i), ∀ᶠ w in 𝓝 z,
        u i (π w) ^ a i = (c i (π w) ^ a i * g i w) *
          W w j ^ (if (∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i) then a i else 0) *
          W w (s i) ^ (if z ∈ geoStrictTransform π C (E.get i) then a i else 0) := by
      intro i hiT
      have hi : π z ∈ E.get i := (Finset.mem_filter.mp hiT).2
      filter_upwards [hπt.eventually (hc i hi).2.2, hO.mem_nhds hzO] with w hw hwO
      have hflatW : flatCoord Φ (s i) (π w) = monomial kC j (W w) (s i) := by
        simp only [flatCoord]
        rw [(hWeq w hwO).2]
      rw [hw, mul_pow, hflatW, monomial_apply]
      by_cases hsj : s i = j
      · have hJ : ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i := (hdich i hi).mpr (hsj ▸ hj)
        have hS : z ∉ geoStrictTransform π C (E.get i) := fun h => ((hS' i hi).mp h).1 hsj
        have hP : ¬ (kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0) := fun h => h.2.1 hsj
        rw [hgneg i hP, if_neg (fun h => h.2 hsj), if_pos hJ, if_neg hS, hsj]
        ring
      · by_cases hk : kC ≤ (s i).1
        · have hJ : ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i := (hdich i hi).mpr hk
          by_cases hWz : W z (s i) = 0
          · have hS : z ∈ geoStrictTransform π C (E.get i) := (hS' i hi).mpr ⟨hsj, hWz⟩
            have hP : ¬ (kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0) := fun h => h.2.2 hWz
            rw [hgneg i hP, if_pos ⟨hk, hsj⟩, if_pos hJ, if_pos hS]
            ring
          · have hS : z ∉ geoStrictTransform π C (E.get i) := fun h => hWz ((hS' i hi).mp h).2
            have hP : kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0 := ⟨hk, hsj, hWz⟩
            rw [hgpos i hP, if_pos ⟨hk, hsj⟩, if_pos hJ, if_neg hS]
            ring
        · have hJ : ¬ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i := fun h => hk ((hdich i hi).mp h)
          have hWz : W z (s i) = 0 := by
            have h1 : monomial kC j (W z) (s i) = W z (s i) := by
              rw [monomial_apply, if_neg (fun h => hk h.1)]
            rw [← h1, (hWeq z hzO).2]
            exact (hflatH i hi (mem_chart_source _ (π z)) Φ.center_mem_source).mp hi
          have hS : z ∈ geoStrictTransform π C (E.get i) := (hS' i hi).mpr ⟨hsj, hWz⟩
          have hP : ¬ (kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0) := fun h => hk h.1
          rw [hgneg i hP, if_neg (fun h => hk h.1), if_neg hJ, if_pos hS]
          ring
    refine ⟨fun w => ∏ i ∈ Finset.univ.filter (fun i => π z ∈ E.get i), c i (π w) ^ a i * g i w,
      ?_, ?_, ?_⟩
    · have hπd : ∀ᶠ w in 𝓝 z,
          MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
        Eventually.of_forall fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
      refine holomorphicAt_finset_prod _ fun i hiT => ?_
      have hi : π z ∈ E.get i := (Finset.mem_filter.mp hiT).2
      exact (CompanionReduction.holomorphicAt_pow_of
        (HadamardBridge.holomorphicAt_comp_map hπd (hc i hi).1) (a i)).mul (hghol i)
    · refine Finset.prod_ne_zero_iff.mpr fun i hiT => ?_
      have hi : π z ∈ E.get i := (Finset.mem_filter.mp hiT).2
      exact mul_ne_zero (pow_ne_zero _ (hc i hi).2.1) (hgz i)
    · have hall := (Filter.eventually_all_finset _).mpr hper
      filter_upwards [hall] with w hw
      rw [Finset.prod_congr rfl hw, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.filter_filter]
      congr 1
      have hpw : ∀ i, W w (s i) ^ (if z ∈ geoStrictTransform π C (E.get i) then a i else 0) =
          if z ∈ geoStrictTransform π C (E.get i) then W w (s i) ^ a i else 1 := by
        intro i
        split_ifs <;> simp
      rw [Finset.prod_congr rfl fun i _ => hpw i, ← Finset.prod_filter, Finset.filter_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hzH i h, h⟩⟩

end Chart

/-! ### The transform in coordinates adapted to the transformed divisor -/

section SNCForm

section Germ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- Where `𝓘_A = (h)` and `A` is closed, `A` is the zero set of `h`. -/
theorem mem_iff_of_vanishingIdeal_eq {A : Set M} (hA : IsClosed A) {h : M → ℂ} {y : M}
    (hh : HolomorphicAt n h y)
    (hI : ∀ g, (vanishingIdeal (n := n) A).mem y g ↔ IsInSpanAt (n := n) (· = h) y g) :
    y ∈ A ↔ h y = 0 := by
  constructor
  · intro hy
    obtain ⟨-, hev⟩ := (hI h).mpr (isInSpanAt_self rfl hh)
    exact hev.self_of_nhds hy
  · intro h0
    by_contra hy
    have h1 : (vanishingIdeal (n := n) A).mem y (fun _ => 1) := by
      refine ⟨holomorphicAt_const (n := n) (x := y) (1 : ℂ), ?_⟩
      filter_upwards [hA.isOpen_compl.mem_nhds hy] with y' hy' hA'
      exact absurd hA' hy'
    obtain ⟨-, a, -, ha⟩ := isInSpanAt_eq_iff.mp ((hI _).mp h1)
    have := ha.self_of_nhds
    simp [h0] at this

/-- Products over the indices of `E.map f ++ [P]`: the indices of `E`, then the last one. -/
theorem prod_map_append_singleton {α β R : Type*} [CommMonoid R] (E : List α) (f : α → β)
    (P : β) (F : Fin (E.map f ++ [P]).length → R) :
    ∏ i, F i = (∏ i : Fin E.length, F ⟨i.1, by simp⟩) * F ⟨E.length, by simp⟩ := by
  rw [← Fin.prod_congr' F (length_map_append_singleton E f P).symm, Fin.prod_univ_castSucc]
  rfl

end Germ

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- Where `𝒪(-D) = (h)`, `D = π⁻¹ C` is the zero set of `h`. -/
theorem mem_centre_iff_of_generator (hπ : IsBlowupAlong n C π) {h : Y → ℂ} {y : Y}
    (hh : HolomorphicAt n h y)
    (hD : ∀ g, (exceptionalDivisor hπ).ideal.mem y g ↔ IsInSpanAt (n := n) (· = h) y g) :
    π y ∈ C ↔ h y = 0 := by
  have hsupp : y ∈ (exceptionalDivisor hπ).support ↔ π y ∈ C := by
    rw [support_exceptionalDivisor hπ]; rfl
  rw [← hsupp]
  constructor
  · intro hy
    exact hy h ((hD h).mpr (isInSpanAt_self rfl hh))
  · intro h0 g hg
    obtain ⟨-, a, -, hga⟩ := isInSpanAt_eq_iff.mp ((hD g).mp hg)
    rw [hga.self_of_nhds]
    simp [h0]

end SNCForm

end

end Hironaka.MonomialBlowup
