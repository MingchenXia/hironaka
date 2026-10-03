/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.MonomialBlowupAlong
import Hironaka.Invariant.MonomialResolution
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
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Blowup.LiftedOpenModel
import Hironaka.MarkedIdeal.LocalGiraudTransform
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MemberPullback
import Hironaka.Blowup.MonomialBlowup
import Hironaka.Invariant.MonomialPart
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.Blowup.SimultaneousNormalCrossings
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Monomial ideals under the blowup of a centre with normal crossings, along a submanifold:
# coordinates adapted to the strict transform

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2b of the proof of `pr:resol` and the transform of marked
ideals along a submanifold, §2.1 (3)--(5); Bierstone--Milman 2008 (`bierstone-milman08-functoriality`) §5.

Let `π : Y → X` be the blowup along `C`, `C ⊆ N`, `E` a divisor, and `z ∈ Y` over `C`.

* `exists_monomial_chart_of_isAdaptedAt`: from coordinates at `π z` adapted to `C ⊆ N` and `E`
  (`BlowupSNCTransform.IsAdaptedAt`: `C = ℂ^{k_C} × 0`, `N = ℂ^{k_N} × 0`, the members through
  `π z` the hyperplanes `{w_{s i} = 0}` with `s i < k_N`), the monomial chart `W` of
  `MonomialBlowup.exists_monomial_chart` (all its clauses), together with: on its domain `U`,
  `N' = {y | j < k_N ∧ W_t(y) = 0 for t ≥ k_N}`; in particular `j < k_N` when `z ∈ N'`.
* `exists_snc_chart_geoTransform_along`: for a marked ideal `(M, N, E, 𝔞, d)` with `N` a closed
  submanifold, `𝔞` coherent, `E` simple normal crossings and transverse to `N`, `C` an admissible
  centre and `z ∈ N'` over `C`: if `Res_N 𝔞 = Res_N (∏_{π z ∈ E_i} u_i^{a_i})` at `π z` (`u_i`
  generators of `𝓘_{E_i}`) and `d ≤ e = ∑_{π z ∈ E_i, C ⊆ E_i near π z} a_i`, there are `k` and
  coordinates `Θ` centred at `z` such that `N' = {Θ_t = 0, t ≥ k}` near `z`, every member of
  `E' = (E_1', …, E_s', π⁻¹ C)` through `z` is a hyperplane `{Θ_{σ i} = 0}` with `σ i < k`
  (`σ` injective on them), and `Res_{N'} 𝔞' = Res_{N'} (∏_{z ∈ E'_i} Θ_{σ i}^{a'_i})` at `z`,
  `a'_i = a_i` (`i < s`), `a'_s = e - d`.  So the `Θ_{σ i}` restricted to `N'` are among the
  coordinates `Θ_0, …, Θ_{k-1}` of `N'`: the transform restricted to `N'` is monomial in
  coordinates of `N'` adapted to `E'|_{N'}`.
* `exists_snc_chart_geoTransform_along_of_flat`: the same from flat coordinates `Φ` at `π z`
  (the members through `π z` the hyperplanes `{Φ_{σ₀ i} = 0}`,
  `Res_N 𝔞 = Res_N (∏ Φ_{σ₀ i}^{a_i})`).
* helper: `isInSpanOnAt_eq_congr` (a restricted principal relation depends only on the germ of
  the generator).
* off the centre: `isInSpanOnAt_geoTransform_iff_pullback_of_notMem` (`Res_{N'} 𝔞' = Res_{N'} π^*𝔞` at `z` with `π z
  ∉ C`) and `exists_snc_chart_geoTransform_along_of_notMem`: from centred flat coordinates `Φ` at `π z ∉ C` with `N
  = {Φ_t = 0, t ≥ k}`, the members through `π z` the hyperplanes `{Φ_{σ₀ i} = 0}` (`σ₀ i < k`, `σ₀` injective on
  them) and `Res_N 𝔞 = Res_N (∏ Φ_{σ₀ i}^{a_i})`, the same shape at `z` with `Θ = Φ ∘ π`
  (`MonomialResolution.exists_chart_comp`): together with `exists_snc_chart_geoTransform_along` every point of `N'`
  is covered.

Proof: the proof of `MonomialBlowup.exists_monomial_chart` run on the adapted coordinates of
`IsAdaptedAt` instead of those of `C` and `E` alone, plus the description of `N'` in the monomial
chart (`BlowupSNCTransform.mem_geoStrictTransform_iff_of_chart` with `N = L_{t ≥ k_N}`); then the
recentring `Θ = W - W z` (`exists_recentred_coords`) as in `exists_snc_chart_geoTransform`, and the
generator from `MonomialBlowupAlong.isInSpanOnAt_geoTransform_iff_of_eq`.  The adapted coordinates
at `π z` exist by `SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings` (`C ⊆ N`, `E`
SNC and transverse to `N`, `C` with normal crossings with `E`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MonomialBlowupAlongChart

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupFlatCoordinates Hironaka.BlowupMonomialCharts Hironaka.BlowupLocalSurjectivity Hironaka.BlowupExceptionalDivisor Hironaka.BlowupStrictSubmanifold Hironaka.BlowupStrictIdeal Hironaka.BlowupSNCTransform Hironaka.NormalCrossings Hironaka.SimultaneousNormalCrossings Hironaka.MemberPullback Hironaka.MonomialPart Hironaka.GermIdealOrder Hironaka.IdealWeightPowers Hironaka.BlowupControlledTransform Hironaka.InvertibleIdealQuotient Hironaka.RelativePrincipalizationSpan Hironaka.MonomialBlowup Hironaka.MonomialBlowupAlong

noncomputable section

variable {n : ℕ}

/-! ### A restricted principal relation depends only on the germ of the generator -/

section Germ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- If `h = h'` near `x`, then `g` is on `A` near `x` a multiple of `h` iff of `h'`. -/
theorem isInSpanOnAt_eq_congr {A : Set M} {x : M} {h h' : M → ℂ} (hhh' : h =ᶠ[𝓝 x] h')
    (g : M → ℂ) :
    IsInSpanOnAt (n := n) A (· = h) x g ↔ IsInSpanOnAt (n := n) A (· = h') x g := by
  constructor
  · intro hg
    refine IsInSpanOnAt.trans (fun s hs => ?_) hg
    subst hs
    exact ⟨1, fun _ => h', fun _ _ => 1, fun _ => rfl,
      fun _ => holomorphicAt_const (n := n) (x := x) (1 : ℂ), by
        filter_upwards [hhh'] with y hy _
        simp [hy]⟩
  · intro hg
    refine IsInSpanOnAt.trans (fun s hs => ?_) hg
    subst hs
    exact ⟨1, fun _ => h, fun _ _ => 1, fun _ => rfl,
      fun _ => holomorphicAt_const (n := n) (x := x) (1 : ℂ), by
        filter_upwards [hhh'] with y hy _
        simp [hy]⟩

end Germ

/-! ### The monomial chart in coordinates adapted to `C ⊆ N` and `E` -/

section Chart

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

open Classical in
/-- **The monomial chart over a point of the centre, adapted to `C ⊆ N` and `E`.**  Let `π` be
the blowup along `C`, `E` a divisor with closed members, and `π z ∈ C`, and let coordinates at
`π z` be adapted to `C ⊆ N` and `E` (`IsAdaptedAt`).  Then the conclusion of
`MonomialBlowup.exists_monomial_chart` holds (the monomial chart `W` on `U ∋ z`, the index `j` of
the exceptional divisor, the indices `s i` of the strict transforms of the members, the monomial
pullback formula), and moreover there is `k_N` with `s i < k_N` for the members through `π z` and,
on `U`, `y ∈ N' ↔ j < k_N ∧ W_t(y) = 0 for every t ≥ k_N` (`N' = closure (π⁻¹ (N \ C))`). -/
theorem exists_monomial_chart_of_isAdaptedAt (hπ : IsBlowupAlong n C π) {N : Set X}
    {E : List (Set X)} (hEc : ∀ H ∈ E, IsClosed H) {z : Y} (hzC : π z ∈ C)
    (had : IsAdaptedAt n C N E (π z)) :
    ∃ (kN : ℕ) (j : Fin n) (s : Fin E.length → Fin n) (W : Y → ComplexModel n) (U : Set Y),
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
      (∀ i, π z ∈ E.get i → (s i).1 < kN) ∧
      (∀ y ∈ U, (y ∈ geoStrictTransform π C N ↔
        j.1 < kN ∧ W y ∈ complexCoordinatePlane n kN)) ∧
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
  obtain ⟨kC, kN, Φ, s, hΦt, hslt, hsinj, hflat⟩ := had
  have hx' : π z ∈ flatDomain Φ := ⟨mem_chart_source _ (π z), Φ.center_mem_source⟩
  have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kC) :=
    fun hy hyΦ => (hflat hy hyΦ).1
  have hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈
          coordSubspace (Finset.univ.filter fun t : Fin n => kN ≤ t.1)) :=
    fun hy hyΦ => by rw [coordSubspace_eq_complexCoordinatePlane]; exact (hflat hy hyΦ).2.1
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
  -- the strict transform of `N` in the chart
  have hNu : ∀ u ∈ O, (u ∈ geoStrictTransform π C N ↔
      j.1 < kN ∧ W u ∈ complexCoordinatePlane n kN) := fun u hu => by
    rw [mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatN hj hO hWs hWeq hℓ hu,
      coordSubspace_eq_complexCoordinatePlane]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  have hzH : ∀ i, z ∈ geoStrictTransform π C (E.get i) → π z ∈ E.get i := fun i hi =>
    geoStrictTransform_subset_preimage hπ.contMDiff.continuous (hEc _ (List.get_mem _ _)) hi
  -- the strict transform through `z`, in the chart
  have hS' : ∀ i, π z ∈ E.get i →
      (z ∈ geoStrictTransform π C (E.get i) ↔ s i ≠ j ∧ W z (s i) = 0) := by
    intro i hi
    rw [hHu i hi z hzO, mem_coordSubspace_singleton, Finset.mem_singleton]
    exact ⟨fun h => ⟨fun h' => h.1 h'.symm, h.2⟩, fun h => ⟨fun h' => h.1 h'.symm, h.2⟩⟩
  refine ⟨kN, j, s, W, O, hO, hzO, hWs, hFinj z hzO, hWzj, fun y hy g => ?_, fun i hi => ?_,
    hsinj, hslt, hNu, fun a u hu => ?_⟩
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

/-! ### The transform along `N'` in coordinates adapted to `N'` and the transformed divisor -/

section SNCForm

open MarkedIdeals MarkedIdeals.MarkedIdeal

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

open Classical in
/-- **`hir:monomial-blowup` along `N'`, in coordinates adapted to `N'` and the transformed
divisor.**  Let `(M, N, E, 𝔞, d)` have `N` a closed submanifold, `𝔞` coherent, `E` simple normal
crossings and transverse to `N`, `C` an admissible centre, and `z ∈ N'` over `C`.  If
`Res_N 𝔞 = Res_N (∏_{π z ∈ E_i} u_i^{a_i})` at `π z` (`u_i` holomorphic generators of `𝓘_{E_i}`)
and `d ≤ e = ∑_{π z ∈ E_i, C ⊆ E_i near π z} a_i`, then there are `k`, coordinates `Θ` centred at
`z`, indices `σ` (injective on the members of `E' = (E_1', …, E_s', π⁻¹ C)` through `z`) and
exponents `a'` (`a'_i = a_i` for `i < s`, `a'_s = e - d`) such that near `z`:
`N' = {Θ_t = 0, t ≥ k}`; every member of `E'` through `z` is the hyperplane `{Θ_{σ i} = 0}`, with
`σ i < k`; and `Res_{N'} 𝔞' = Res_{N'} (∏_{z ∈ E'_i} Θ_{σ i}^{a'_i})` at `z`. -/
theorem exists_snc_chart_geoTransform_along (hπ : IsBlowupAlong n C π) {𝔪 : MarkedIdeal n X}
    (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) (hC : 𝔪.IsAdmissibleCentre C)
    (hE : IsSNCDivisor n 𝔪.E) (hTr : IsTransverse n 𝔪.N 𝔪.E) {z : Y}
    (hz : z ∈ (𝔪.geoTransform C π).N) (hzC : π z ∈ C)
    (a : Fin 𝔪.E.length → ℕ) (u : Fin 𝔪.E.length → X → ℂ)
    (hu : ∀ i, π z ∈ 𝔪.E.get i → HolomorphicAt n (u i) (π z) ∧
      ∀ g, (vanishingIdeal (n := n) (𝔪.E.get i)).mem (π z) g ↔
        IsInSpanAt (n := n) (· = u i) (π z) g)
    (hgen : ∀ g, IsInSpanOnAt (n := n) 𝔪.N (𝔪.ideal.mem (π z)) (π z) g ↔
      IsInSpanOnAt (n := n) 𝔪.N
        (· = fun x => ∏ i ∈ Finset.univ.filter (fun i => π z ∈ 𝔪.E.get i), u i x ^ a i)
        (π z) g)
    (hd : 𝔪.d ≤ ∑ i ∈ Finset.univ.filter
      (fun i => π z ∈ 𝔪.E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ 𝔪.E.get i), a i) :
    ∃ (k : ℕ) (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z))
      (σ : Fin (𝔪.geoTransform C π).E.length → Fin n)
      (a' : Fin (𝔪.geoTransform C π).E.length → ℕ),
      Θ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z) = 0 ∧
      (∀ {y : Y}, y ∈ (chartAt (ComplexModel n) z).source →
        chartAt (ComplexModel n) z y ∈ Θ.source →
          (y ∈ (𝔪.geoTransform C π).N ↔
            Θ.toFun (chartAt (ComplexModel n) z y) ∈ complexCoordinatePlane n k)) ∧
      (∀ i, z ∈ (𝔪.geoTransform C π).E.get i → (σ i).1 < k) ∧
      Set.InjOn σ {i | z ∈ (𝔪.geoTransform C π).E.get i} ∧
      (∀ i, z ∈ (𝔪.geoTransform C π).E.get i → ∀ {y : Y},
        y ∈ (chartAt (ComplexModel n) z).source → chartAt (ComplexModel n) z y ∈ Θ.source →
          (y ∈ (𝔪.geoTransform C π).E.get i ↔
            Θ.toFun (chartAt (ComplexModel n) z y) (σ i) = 0)) ∧
      (∀ i (hi : i.1 < 𝔪.E.length), a' i = a ⟨i.1, hi⟩) ∧
      (∀ i, ¬ i.1 < 𝔪.E.length → a' i = (∑ i ∈ Finset.univ.filter
        (fun i => π z ∈ 𝔪.E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ 𝔪.E.get i), a i) - 𝔪.d) ∧
      ∀ g, IsInSpanOnAt (n := n) (𝔪.geoTransform C π).N
          ((𝔪.geoTransform C π).ideal.mem z) z g ↔
        IsInSpanOnAt (n := n) (𝔪.geoTransform C π).N
          (· = fun y => ∏ i ∈ Finset.univ.filter (fun i => z ∈ (𝔪.geoTransform C π).E.get i),
            flatCoord Θ (σ i) y ^ a' i) z g := by
  classical
  have hn : 0 < n := pos_of_isBlowupAlong hπ hzC
  have had : IsAdaptedAt n C 𝔪.N 𝔪.E (π z) :=
    isAdaptedAt_of_hasNormalCrossings hn hC.subset_N hE hTr hC.2.2 hzC
  obtain ⟨k, j, s, W, U, hU, hzU, hWs, hinj, hWzj, hD, hH, hsinj, hslt, hNU, hmono⟩ :=
    exists_monomial_chart_of_isAdaptedAt hπ hE.1 hzC had
  have hzN : j.1 < k ∧ W z ∈ complexCoordinatePlane n k := (hNU z hzU).mp hz
  obtain ⟨Θ, hΘt, hΘ0, hΘ⟩ := exists_recentred_coords hU hWs hzU hinj
  -- zero sets on `U`
  have hCu : ∀ y ∈ U, (π y ∈ C ↔ W y j = 0) := fun y hy =>
    mem_centre_iff_of_generator hπ (holomorphicAt_coord hU hWs j hy) (hD y hy)
  have hHu : ∀ i, z ∈ geoStrictTransform π C (𝔪.E.get i) → ∀ y ∈ U,
      (y ∈ geoStrictTransform π C (𝔪.E.get i) ↔ W y (s i) = 0) := fun i hi y hy =>
    mem_iff_of_vanishingIdeal_eq isClosed_closure (holomorphicAt_coord hU hWs (s i) hy)
      ((hH i hi).2.2.2 y hy)
  -- the recentred coordinates
  have hflat : ∀ {y : Y}, y ∈ (chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y ∈ Θ.source →
        y ∈ U ∧ ∀ k, Θ.toFun (chartAt (ComplexModel n) z y) k = W y k - W z k :=
    fun {y} hy hyΘ => by
      obtain ⟨hyU, hΘy⟩ := hΘ hy hyΘ
      exact ⟨hyU, fun k => by
        show Θ.toFun ((complexChartAt (n := n) z).val y) k = _
        rw [hΘy, PiLp.sub_apply]⟩
  have hget : ∀ i : Fin (𝔪.geoTransform C π).E.length, (𝔪.geoTransform C π).E.get i =
      if h : i.1 < 𝔪.E.length then geoStrictTransform π C (𝔪.E.get ⟨i.1, h⟩) else π ⁻¹' C :=
    fun i => get_map_append_singleton 𝔪.E (geoStrictTransform π C) (π ⁻¹' C) i
  let σ : Fin (𝔪.geoTransform C π).E.length → Fin n := fun i =>
    if h : i.1 < 𝔪.E.length then s ⟨i.1, h⟩ else j
  let a' : Fin (𝔪.geoTransform C π).E.length → ℕ := fun i =>
    if h : i.1 < 𝔪.E.length then a ⟨i.1, h⟩ else (∑ i ∈ Finset.univ.filter
      (fun i => π z ∈ 𝔪.E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ 𝔪.E.get i), a i) - 𝔪.d
  refine ⟨k, Θ, σ, a', hΘt, hΘ0, ?_, ?_, ?_, ?_, fun i hi => dif_pos hi, fun i hi => dif_neg hi,
    ?_⟩
  · -- `N'` is the coordinate subspace `{Θ_t = 0, t ≥ k}`
    intro y hy hyΘ
    obtain ⟨hyU, hΘy⟩ := hflat hy hyΘ
    show y ∈ geoStrictTransform π C 𝔪.N ↔ _
    rw [hNU y hyU]
    constructor
    · rintro ⟨-, hW⟩ t ht
      rw [hΘy t, hW t ht, hzN.2 t ht, sub_zero]
    · intro hΘN
      refine ⟨hzN.1, fun t ht => ?_⟩
      have h1 := hΘN t ht
      rwa [hΘy t, hzN.2 t ht, sub_zero] at h1
  · -- the indices of the members through `z` are coordinates of `N'`
    intro i hi
    rw [hget i] at hi
    simp only [σ]
    by_cases h : i.1 < 𝔪.E.length
    · simp only [dif_pos h] at hi ⊢
      exact hslt _ (hH _ hi).1
    · simp only [dif_neg h]
      exact hzN.1
  · -- the indices of the members through `z` are distinct
    intro i hi i' hi' hii'
    simp only [Set.mem_ofPred_eq] at hi hi'
    rw [hget i] at hi
    rw [hget i'] at hi'
    simp only [σ] at hii'
    by_cases h : i.1 < 𝔪.E.length <;> by_cases h' : i'.1 < 𝔪.E.length
    · rw [dif_pos h] at hi hii'
      rw [dif_pos h'] at hi' hii'
      exact Fin.ext (Fin.mk.inj_iff.mp (hsinj (hH _ hi).1 (hH _ hi').1 hii'))
    · rw [dif_pos h] at hi hii'
      rw [dif_neg h'] at hii'
      exact absurd hii' (hH _ hi).2.1
    · rw [dif_neg h] at hii'
      rw [dif_pos h'] at hi' hii'
      exact absurd hii'.symm (hH _ hi').2.1
    · exact eq_of_not_lt h h'
  · -- the members through `z` are coordinate hyperplanes
    intro i hi y hy hyΘ
    obtain ⟨hyU, hΘy⟩ := hflat hy hyΘ
    rw [hget i] at hi ⊢
    simp only [σ]
    by_cases h : i.1 < 𝔪.E.length
    · simp only [dif_pos h] at hi ⊢
      rw [hΘy, (hH _ hi).2.2.1, sub_zero]
      exact hHu _ hi y hyU
    · simp only [dif_neg h]
      rw [hΘy, hWzj, sub_zero]
      exact hCu y hyU
  · -- the generator along `N'`
    intro g
    obtain ⟨c, hc, hcz, heq⟩ := hmono a u hu
    have hWj : HolomorphicAt n (fun w => W w j) z := holomorphicAt_coord hU hWs j hzU
    have hq : HolomorphicAt n (fun w => ∏ i ∈ Finset.univ.filter
        (fun i => z ∈ geoStrictTransform π C (𝔪.E.get i)), W w (s i) ^ a i) z :=
      holomorphicAt_finset_prod _ fun i _ =>
        CompanionReduction.holomorphicAt_pow_of (holomorphicAt_coord hU hWs (s i) hzU) (a i)
    refine (isInSpanOnAt_geoTransform_iff_of_eq hπ hN h𝔞 hC hz hgen (hD z hzU) hWj hc hcz hq hd
      heq g).trans (isInSpanOnAt_eq_congr ?_ g)
    filter_upwards [(isOpen_flatDomain Θ).mem_nhds (mem_flatDomain_self Θ)] with y hy
    obtain ⟨-, hΘy⟩ := hflat hy.1 hy.2
    have hfc : ∀ k, W z k = 0 → flatCoord Θ k y = W y k := fun k hk => by
      show Θ.toFun (chartAt (ComplexModel n) z y) k = _
      rw [hΘy, hk, sub_zero]
    have hpt : ∀ i : Fin (𝔪.geoTransform C π).E.length,
        (if z ∈ (𝔪.geoTransform C π).E.get i then flatCoord Θ (σ i) y ^ a' i else 1) =
          if h : i.1 < 𝔪.E.length then
            (if z ∈ geoStrictTransform π C (𝔪.E.get ⟨i.1, h⟩) then
              W y (s ⟨i.1, h⟩) ^ a ⟨i.1, h⟩ else 1)
          else W y j ^ ((∑ i ∈ Finset.univ.filter
            (fun i => π z ∈ 𝔪.E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ 𝔪.E.get i), a i) - 𝔪.d) := by
      intro i
      rw [hget i]
      by_cases h : i.1 < 𝔪.E.length
      · simp only [σ, a', dif_pos h]
        split_ifs with hzi
        · rw [hfc _ (hH _ hzi).2.2.1]
        · rfl
      · simp only [σ, a', dif_neg h]
        rw [if_pos (show z ∈ π ⁻¹' C from hzC), hfc _ hWzj]
    rw [Finset.prod_filter, Finset.prod_filter, Finset.prod_congr rfl fun i _ => hpt i]
    have hprod := prod_map_append_singleton 𝔪.E (geoStrictTransform π C) (π ⁻¹' C)
      (fun i => if h : i.1 < 𝔪.E.length then
            (if z ∈ geoStrictTransform π C (𝔪.E.get ⟨i.1, h⟩) then
              W y (s ⟨i.1, h⟩) ^ a ⟨i.1, h⟩ else 1)
          else W y j ^ ((∑ i ∈ Finset.univ.filter
            (fun i => π z ∈ 𝔪.E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ 𝔪.E.get i), a i) - 𝔪.d))
    refine Eq.trans (mul_comm _ _) (Eq.trans ?_ hprod.symm)
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Fin.val_mk, dif_pos i.2, Fin.eta]
    · simp only [Fin.val_mk, lt_irrefl, not_false_eq_true, dif_neg]

open Classical in
/-- **The same, from flat coordinates at `π z`**: if the members `E_i` through `π z` (`i ∈ T`)
are the coordinate hyperplanes `{Φ_{σ₀ i} = 0}` of a flattening `Φ` at `π z` and
`Res_N 𝔞 = Res_N (∏_{i ∈ T} Φ_{σ₀ i}^{a_i})` at `π z`, the conclusion of
`exists_snc_chart_geoTransform_along` holds (the `Φ_{σ₀ i}` generate the `𝓘_{E_i}`,
`MemberPullback.vanishingIdeal_mem_iff_flatCoord`; `Φ` need not be adapted to `N`). -/
theorem exists_snc_chart_geoTransform_along_of_flat (hπ : IsBlowupAlong n C π)
    {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hC : 𝔪.IsAdmissibleCentre C) (hE : IsSNCDivisor n 𝔪.E) (hTr : IsTransverse n 𝔪.N 𝔪.E)
    {z : Y} (hz : z ∈ (𝔪.geoTransform C π).N) (hzC : π z ∈ C)
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z))}
    {σ₀ : Fin 𝔪.E.length → Fin n} {T : Finset (Fin 𝔪.E.length)}
    (hT : ∀ i, i ∈ T ↔ π z ∈ 𝔪.E.get i)
    (hA : ∀ i ∈ T, ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ 𝔪.E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) (σ₀ i) = 0))
    (a : Fin 𝔪.E.length → ℕ)
    (hgen : ∀ g, IsInSpanOnAt (n := n) 𝔪.N (𝔪.ideal.mem (π z)) (π z) g ↔
      IsInSpanOnAt (n := n) 𝔪.N (· = fun x => ∏ i ∈ T, flatCoord Φ (σ₀ i) x ^ a i) (π z) g)
    (hd : 𝔪.d ≤ ∑ i ∈ Finset.univ.filter
      (fun i => π z ∈ 𝔪.E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ 𝔪.E.get i), a i) :
    ∃ (k : ℕ) (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z))
      (σ : Fin (𝔪.geoTransform C π).E.length → Fin n)
      (a' : Fin (𝔪.geoTransform C π).E.length → ℕ),
      Θ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z) = 0 ∧
      (∀ {y : Y}, y ∈ (chartAt (ComplexModel n) z).source →
        chartAt (ComplexModel n) z y ∈ Θ.source →
          (y ∈ (𝔪.geoTransform C π).N ↔
            Θ.toFun (chartAt (ComplexModel n) z y) ∈ complexCoordinatePlane n k)) ∧
      (∀ i, z ∈ (𝔪.geoTransform C π).E.get i → (σ i).1 < k) ∧
      Set.InjOn σ {i | z ∈ (𝔪.geoTransform C π).E.get i} ∧
      (∀ i, z ∈ (𝔪.geoTransform C π).E.get i → ∀ {y : Y},
        y ∈ (chartAt (ComplexModel n) z).source → chartAt (ComplexModel n) z y ∈ Θ.source →
          (y ∈ (𝔪.geoTransform C π).E.get i ↔
            Θ.toFun (chartAt (ComplexModel n) z y) (σ i) = 0)) ∧
      (∀ i (hi : i.1 < 𝔪.E.length), a' i = a ⟨i.1, hi⟩) ∧
      (∀ i, ¬ i.1 < 𝔪.E.length → a' i = (∑ i ∈ Finset.univ.filter
        (fun i => π z ∈ 𝔪.E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ 𝔪.E.get i), a i) - 𝔪.d) ∧
      ∀ g, IsInSpanOnAt (n := n) (𝔪.geoTransform C π).N
          ((𝔪.geoTransform C π).ideal.mem z) z g ↔
        IsInSpanOnAt (n := n) (𝔪.geoTransform C π).N
          (· = fun y => ∏ i ∈ Finset.univ.filter (fun i => z ∈ (𝔪.geoTransform C π).E.get i),
            flatCoord Θ (σ i) y ^ a' i) z g := by
  classical
  have hTeq : T = Finset.univ.filter (fun i => π z ∈ 𝔪.E.get i) := by
    ext i
    simp [hT]
  subst hTeq
  exact exists_snc_chart_geoTransform_along hπ hN h𝔞 hC hE hTr hz hzC a
    (fun i => flatCoord Φ (σ₀ i))
    (fun i hi => ⟨holomorphicAt_flatCoord Φ (σ₀ i) (mem_flatDomain_self Φ), fun g =>
      vanishingIdeal_mem_iff_flatCoord Φ (hA i ((hT i).mpr hi)) (mem_flatDomain_self Φ) g⟩)
    hgen hd

end SNCForm

/-! ### Off the centre -/

section OffCentre

open MarkedIdeals MarkedIdeals.MarkedIdeal

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **Off the centre the transform along `N'` is the pullback**: if `π z ∉ C`, then
`Res_{N'} 𝔞' = Res_{N'} π^*𝔞` at `z` (the ideal of the centre pulls back to the unit ideal near
`z`, so the colon by its `d`-th power changes nothing on `N'`). -/
theorem isInSpanOnAt_geoTransform_iff_pullback_of_notMem (hπ : IsBlowupAlong n C π)
    (𝔪 : MarkedIdeal n X) {z : Y} (hz : π z ∉ C) (g : Y → ℂ) :
    IsInSpanOnAt (n := n) (𝔪.geoTransform C π).N ((𝔪.geoTransform C π).ideal.mem z) z g ↔
      IsInSpanOnAt (n := n) (𝔪.geoTransform C π).N
        ((GermIdeal.pullback (m := n) π 𝔪.ideal).mem z) z g := by
  constructor
  · intro hg
    refine IsInSpanOnAt.trans (fun t ht => ?_) hg
    have h1 := one_mem_idealPow (n := n)
      (one_mem_pullback_vanishingIdeal (n := n) (π := π) hz hπ.1.1) 𝔪.d
    obtain ⟨K, s, c, hs, hc, hsum⟩ := (ht.2 _ h1).2
    exact ⟨K, s, c, hs, hc, by filter_upwards [hsum] with y hy hyN; simpa using hy hyN⟩
  · intro hg
    refine IsInSpanOnAt.trans (fun t ht => ?_) hg
    have hth : HolomorphicAt n t z := (GermIdeal.mem_pullback_iff.mp ht).1
    refine ⟨1, fun _ => t, fun _ _ => 1, fun _ => ⟨hth, fun h hh =>
      ⟨(holomorphicAt_of_mem_idealPow hh).mul hth, ⟨1, fun _ => t, fun _ => h, fun _ => ht,
        fun _ => holomorphicAt_of_mem_idealPow hh, Eventually.of_forall fun y _ => by simp⟩⟩⟩,
      fun _ => holomorphicAt_const (n := n) (x := z) (1 : ℂ),
      Eventually.of_forall fun y _ => by simp⟩

open Classical in
/-- **`hir:monomial-blowup` along `N'`, off the centre.**  Let `N` be closed, `𝔞` coherent, `E`
simple normal crossings, `0 < n`, and `π z ∉ C`.  Let `Φ` be centred flat coordinates at `π z` in
which `N = {Φ_t = 0, t ≥ k}` and the members `E_i` through `π z` are the hyperplanes
`{Φ_{σ₀ i} = 0}` (`σ₀ i < k`, `σ₀` injective on them), and suppose
`Res_N 𝔞 = Res_N (∏_{π z ∈ E_i} Φ_{σ₀ i}^{a_i})` at `π z`.  Then the same holds at `z` for the
transform `(M', N', E', 𝔞', d)`: there are coordinates `Θ` centred at `z` (`Θ = Φ ∘ π`) with
`N' = {Θ_t = 0, t ≥ k}` near `z`, the members of `E'` through `z` the hyperplanes
`{Θ_{σ i} = 0}` (`σ i < k`, `σ` injective on them), and
`Res_{N'} 𝔞' = Res_{N'} (∏_{z ∈ E'_i} Θ_{σ i}^{a'_i})` at `z`, `a'_i = a_i` for `i < s` (the
exceptional divisor does not pass through `z`). -/
theorem exists_snc_chart_geoTransform_along_of_notMem (hn : 0 < n) (hπ : IsBlowupAlong n C π)
    {𝔪 : MarkedIdeal n X} (hNc : IsClosed 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hE : IsSNCDivisor n 𝔪.E) {z : Y} (hzC : π z ∉ C) {k : ℕ}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z))}
    {σ₀ : Fin 𝔪.E.length → Fin n}
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) = 0)
    (hΦN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ 𝔪.N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n k))
    (hσk : ∀ i, π z ∈ 𝔪.E.get i → (σ₀ i).1 < k)
    (hσinj : Set.InjOn σ₀ {i | π z ∈ 𝔪.E.get i})
    (hA : ∀ i, π z ∈ 𝔪.E.get i → ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ 𝔪.E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) (σ₀ i) = 0))
    (a : Fin 𝔪.E.length → ℕ)
    (hgen : ∀ g, IsInSpanOnAt (n := n) 𝔪.N (𝔪.ideal.mem (π z)) (π z) g ↔
      IsInSpanOnAt (n := n) 𝔪.N (· = fun x => ∏ i ∈ Finset.univ.filter
        (fun i => π z ∈ 𝔪.E.get i), flatCoord Φ (σ₀ i) x ^ a i) (π z) g) :
    ∃ (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z))
      (σ : Fin (𝔪.geoTransform C π).E.length → Fin n)
      (a' : Fin (𝔪.geoTransform C π).E.length → ℕ),
      Θ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z) = 0 ∧
      (∀ {y : Y}, y ∈ (chartAt (ComplexModel n) z).source →
        chartAt (ComplexModel n) z y ∈ Θ.source →
          (y ∈ (𝔪.geoTransform C π).N ↔
            Θ.toFun (chartAt (ComplexModel n) z y) ∈ complexCoordinatePlane n k)) ∧
      (∀ i, z ∈ (𝔪.geoTransform C π).E.get i → (σ i).1 < k) ∧
      Set.InjOn σ {i | z ∈ (𝔪.geoTransform C π).E.get i} ∧
      (∀ i, z ∈ (𝔪.geoTransform C π).E.get i → ∀ {y : Y},
        y ∈ (chartAt (ComplexModel n) z).source → chartAt (ComplexModel n) z y ∈ Θ.source →
          (y ∈ (𝔪.geoTransform C π).E.get i ↔
            Θ.toFun (chartAt (ComplexModel n) z y) (σ i) = 0)) ∧
      (∀ i (hi : i.1 < 𝔪.E.length), a' i = a ⟨i.1, hi⟩) ∧
      ∀ g, IsInSpanOnAt (n := n) (𝔪.geoTransform C π).N
          ((𝔪.geoTransform C π).ideal.mem z) z g ↔
        IsInSpanOnAt (n := n) (𝔪.geoTransform C π).N
          (· = fun y => ∏ i ∈ Finset.univ.filter (fun i => z ∈ (𝔪.geoTransform C π).E.get i),
            flatCoord Θ (σ i) y ^ a' i) z g := by
  classical
  obtain ⟨Θ, hΘt, hΘ0, hΘ⟩ := MonomialResolution.exists_chart_comp hπ hzC Φ hΦ0
  set E' := (𝔪.geoTransform C π).E with hE'
  set σ' : Fin E'.length → Fin n := fun i =>
    if h : i.1 < 𝔪.E.length then σ₀ ⟨i.1, h⟩ else ⟨0, hn⟩ with hσ'
  set a' : Fin E'.length → ℕ := fun i => if h : i.1 < 𝔪.E.length then a ⟨i.1, h⟩ else 0 with ha'
  have hmem := MonomialResolution.mem_get_geoTransform_iff_of_notMem hπ 𝔪 hE (y := z) hzC
  refine ⟨Θ, σ', a', hΘt, hΘ0, fun {y} hy hyΘ => ?_, fun i hi => ?_, fun i hi j hj hij => ?_,
    fun i hi y hy hyΘ => ?_, fun i hi => dif_pos hi, fun g => ?_⟩
  · -- `N' = π⁻¹ N` off the centre
    obtain ⟨hyC, hyD, hyeq⟩ := hΘ hy hyΘ
    show y ∈ geoStrictTransform π C 𝔪.N ↔ _
    rw [mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hNc hyC, hyeq]
    exact hΦN hyD.1 hyD.2
  · obtain ⟨hil, hi'⟩ := (hmem i).mp hi
    simp only [hσ', dif_pos hil]
    exact hσk _ hi'
  · obtain ⟨hil, hi'⟩ := (hmem i).mp hi
    obtain ⟨hjl, hj'⟩ := (hmem j).mp hj
    simp only [hσ', dif_pos hil, dif_pos hjl] at hij
    exact Fin.ext (by simpa using congrArg Fin.val (hσinj hi' hj' hij))
  · obtain ⟨hil, hi'⟩ := (hmem i).mp hi
    obtain ⟨hyC, hyD, hyeq⟩ := hΘ hy hyΘ
    rw [MonomialResolution.mem_get_geoTransform_iff_of_notMem hπ 𝔪 hE hyC i, hyeq]
    simp only [hσ', dif_pos hil]
    rw [← hA _ hi' hyD.1 hyD.2]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hil, h⟩⟩
  · -- the generator: `Res_{N'} 𝔞' = Res_{N'} π^*𝔞 = Res_{N'} (m ∘ π)`, `m ∘ π = ∏ Θ_{σ i}^{a_i}`
    set m : X → ℂ := fun x => ∏ i ∈ Finset.univ.filter (fun i => π z ∈ 𝔪.E.get i),
      flatCoord Φ (σ₀ i) x ^ a i with hm
    have hstep : IsInSpanOnAt (n := n) (𝔪.geoTransform C π).N
        ((GermIdeal.pullback (m := n) π 𝔪.ideal).mem z) z g ↔
        IsInSpanOnAt (n := n) (𝔪.geoTransform C π).N (· = fun y => m (π y)) z g := by
      constructor
      · intro hg
        exact IsInSpanOnAt.trans (fun G hG => isInSpanOnAt_comp_of_mem_pullback hπ hNc
          (fun g hg => (hgen g).mp (IsInSpanAt.restrict (isInSpanAt_self hg
            (GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg)))) hG) hg
      · intro hg
        refine IsInSpanOnAt.trans (fun s hs => ?_) hg
        subst hs
        have hmN : IsInSpanOnAt (n := n) 𝔪.N (· = m) (π z) m :=
          ⟨1, fun _ => m, fun _ _ => 1, fun _ => rfl,
            fun _ => holomorphicAt_const (n := n) (x := π z) (1 : ℂ),
            Eventually.of_forall fun y _ => by simp⟩
        exact isInSpanOnAt_pullback_comp hπ hNc h𝔞 ((hgen m).mpr hmN)
    refine (isInSpanOnAt_geoTransform_iff_pullback_of_notMem hπ 𝔪 hzC g).trans
      (hstep.trans (isInSpanOnAt_eq_congr ?_ g))
    have hT' : (Finset.univ.filter fun i : Fin E'.length => z ∈ E'.get i) =
        (Finset.univ.filter fun i : Fin 𝔪.E.length => π z ∈ 𝔪.E.get i).map
          (MonomialResolution.castE 𝔪 C π) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      rw [hmem i]
      constructor
      · rintro ⟨hil, hi'⟩
        exact ⟨⟨i.1, hil⟩, hi', Fin.ext rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j.2, hj⟩
    filter_upwards [(isOpen_flatDomain Θ).mem_nhds (mem_flatDomain_self Θ)] with y hy
    obtain ⟨-, -, hyeq⟩ := hΘ hy.1 hy.2
    rw [hT', Finset.prod_map]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hil : (MonomialResolution.castE 𝔪 C π i).1 < 𝔪.E.length := i.2
    simp only [flatCoord, hσ', ha', dif_pos hil]
    rw [hyeq]
    rfl

end OffCentre

end

end Hironaka.MonomialBlowupAlongChart
