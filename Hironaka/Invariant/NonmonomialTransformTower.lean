/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MonomialResolution
import Hironaka.Blowup.ExceptionalIdealPushforward
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupSNCTransform
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Invariant.MemberPullback
import Hironaka.Blowup.MonomialBlowup
import Hironaka.Invariant.MonomialCase
import Hironaka.Invariant.MonomialPart
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.OrderTaylor
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Blowup.SimultaneousNormalCrossings
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The transforms of the monomial and nonmonomial parts along the companion tower (`N = M`)

Let `(X, X, E, 𝔞, d)` be a well-formed marked ideal whose ideal is nonzero at every point, `𝓝 = 𝓝(𝔞)`, `𝓜 = 𝓜(𝔞)`
(`MonomialPart`), `o ≥ 1` with `ord 𝓝 ≤ o` on `cosupp(𝔞, d)`, and `𝒪 = (𝓝, o) + (𝓜, d - o)` (`o < d`) or `(𝓝, o)`
(`o ≥ d`) the companion ideal.

* `frequently_mem_notMem_of_hasNormalCrossings`: points of `C` off the members not containing `C` near `x`
  accumulate at `x ∈ C`.
* `exceptionalDivisor_mem_of_vanishingIdeal_mem`: at the points of `D = π⁻¹ C` the ideal of `π⁻¹ C` lies in `𝒪(-D)`
  (`D` is a smooth hypersurface, `𝒪(-D) = (W_j)` with `dW_j ≠ 0`).
* `step` (one blowup): if `𝔞 = 𝔟 𝓜` as above, `𝔟` nonzero, `C` a closed submanifold with normal crossings with `E`,
  `C ⊆ cosupp(𝔟, o) ∩ cosupp(𝔞, d)` and `ord 𝔟 ≤ o` on `C`, then `σ^c(𝔞, d) = σ^c(𝔟, o) · 𝓜'` with `𝓜' = 𝒪(-(o -
  d)D) · σ^c(𝓜, d - o)` principal monomial at every point, and `σ^c(𝔟, o)` is again nonzero and contained in the
  ideal of no member of `E'` at its points (`exists_not_mem_vanishingIdeal_geoStrictTransform`).
-/

open Set Filter Finset
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.NonmonomialTransformTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder Hironaka.BlowupFlatCoordinates Hironaka.GiraudAlong Hironaka.DivisorExponent Hironaka.MemberPullback Hironaka.MonomialPart Hironaka.NormalCrossings Hironaka.MonomialCase Hironaka.MonomialResolution Hironaka.BlowupStrictSubmanifold Hironaka.BlowupExceptionalDivisor Hironaka.BlowupControlledTransform Hironaka.InvertibleIdealQuotient Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers Hironaka.CompanionReduction

noncomputable section

variable {n : ℕ}

/-! ### The generic-point argument -/

section Generic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {E : List (Set M)} {C : Set M}

open Classical in
/-- **Generic points of a centre with normal crossings**: points of `C` that lie on no member `E_i` through `x` with
`C ⊄ E_i` near `x` accumulate at `x ∈ C`.  In coordinates adapted to `C = {w_t = 0, t ∈ S₀}` and `E_i = {w_t = 0, t ∈ S_i}`,
`C ⊄ E_i` near `x` forces some `t ∈ S_i \ S₀`; move those coordinates off `0` and keep the others. -/
theorem frequently_mem_notMem_of_hasNormalCrossings (hnc : HasNormalCrossings n C E) {x : M} (hx : x ∈ C) :
    ∃ᶠ y in 𝓝 x, y ∈ C ∧ ∀ i : Fin E.length, x ∈ E.get i →
      ¬ (∀ᶠ y' in 𝓝 x, y' ∈ C → y' ∈ E.get i) → y ∉ E.get i := by
  obtain ⟨S₀, S, ⟨Φ, hΦsrc, hΦ0, hcoord⟩, -⟩ := hnc x hx
  have hxD : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  set T' : Finset (Fin n) := (Finset.univ.filter fun i : Fin E.length => x ∈ E.get i).biUnion
    (fun i => S i \ S₀) with hT'
  have hT'S₀ : ∀ t ∈ T', t ∉ S₀ := by
    intro t ht
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp ht
    exact (Finset.mem_sdiff.mp hi).2
  have hC : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace S₀) :=
    fun hy1 hy2 => hcoord none hx hy1 hy2
  have hEi : ∀ i, x ∈ E.get i → ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace (S i)) :=
    fun i hxi _ hy1 hy2 => hcoord (some i) hxi hy1 hy2
  refine (frequently_flatMap_ne_zero hΦsrc hxD T').mono fun y ⟨hyD, hne, heq⟩ => ⟨?_, fun i hxi hnot hyi => ?_⟩
  · refine (hC hyD.1 hyD.2).mpr fun t ht => ?_
    have h1 : flatMap Φ y t = flatMap Φ x t := heq t fun h => hT'S₀ t h ht
    have h2 : flatMap Φ x t = 0 := by
      have h : (Φ.toFun ((complexChartAt (n := n) x).val x)) t = 0 := by rw [hΦ0]; simp
      exact h
    exact h1.trans h2
  · -- `S i ⊄ S₀`, else `C ⊆ E_i` near `x`
    have hsub : ¬ S i ⊆ S₀ := by
      intro hS
      refine hnot ?_
      filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD] with y' hy' hy'C
      exact (hEi i hxi hy'.1 hy'.2).mpr fun t ht => (hC hy'.1 hy'.2).mp hy'C t (hS ht)
    obtain ⟨t, htS, htS₀⟩ := Finset.not_subset.mp hsub
    have htT : t ∈ T' := Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩, Finset.mem_sdiff.mpr ⟨htS, htS₀⟩⟩
    exact hne t htT ((hEi i hxi hyD.1 hyD.2).mp hyi t htS)

end Generic

/-! ### The exceptional divisor -/

section Exceptional

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X}

/-- **At the points of `D = π⁻¹ C` the ideal of `π⁻¹ C` lies in `𝒪(-D)`**: `π⁻¹ C` is a smooth hypersurface
(`BlowupSNCTransform.isSNCDivisor_preimage_centre`), so its ideal is generated by a coordinate `Φ_t`; `𝒪(-D) =
(W_j)` with `W_j` of nonzero differential (monomial chart); `W_j` vanishes on `π⁻¹ C`, so `W_j = c Φ_t`, and `c(z) ≠
0` since `W_j ∉ 𝔪_z²`; hence `Φ_t = c⁻¹ W_j ∈ 𝒪(-D)`. -/
theorem exceptionalDivisor_mem_of_vanishingIdeal_mem (hπ : IsBlowupAlong n C π) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hnc : HasNormalCrossings n C E) {z : Y} (hz : π z ∈ C) {g : Y → ℂ}
    (hg : (vanishingIdeal (n := n) (π ⁻¹' C)).mem z g) : (exceptionalDivisor hπ).ideal.mem z g := by
  have hn : 0 < n := SimultaneousNormalCrossings.pos_of_isBlowupAlong hπ hz
  obtain ⟨j, -, W, U, hU, hzU, hWs, hinj, -, hD, -⟩ := MonomialBlowup.exists_monomial_chart hπ hE hnc hz
  have hhol : ∀ y ∈ U, HolomorphicAt n (fun w => W w j) y := fun y hy =>
    BlowupStrictIdeal.holomorphicAt_coord hU hWs j hy
  have hzero : ∀ y ∈ U, (π y ∈ C ↔ W y j = 0) := fun y hy =>
    MonomialBlowup.mem_centre_iff_of_generator hπ (hhol y hy) (hD y hy)
  obtain ⟨Φ, σ, hΦsrc, hΦ0, -, hA⟩ := exists_snc_chart hn (BlowupSNCTransform.isSNCDivisor_preimage_centre hπ) z
  set i0 : Fin [π ⁻¹' C].length := ⟨0, by simp⟩ with hi0
  have hzi : z ∈ [π ⁻¹' C].get i0 := hz
  have hflat : ∀ {y : Y}, y ∈ (chartAt (ComplexModel n) z).source → chartAt (ComplexModel n) z y ∈ Φ.source →
      (y ∈ π ⁻¹' C ↔ Φ.toFun (chartAt (ComplexModel n) z y) (σ i0) = 0) := fun hy1 hy2 => hA i0 hzi hy1 hy2
  have hzD : z ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hIgen := vanishingIdeal_mem_iff_flatCoord Φ hflat hzD
  have hΦt : HolomorphicAt n (flatCoord Φ (σ i0)) z := holomorphicAt_flatCoord Φ (σ i0) hzD
  -- `W_j` lies in the ideal of `π⁻¹ C`
  have hWI : (vanishingIdeal (n := n) (π ⁻¹' C)).mem z (fun w => W w j) := by
    refine ⟨hhol z hzU, ?_⟩
    filter_upwards [hU.mem_nhds hzU] with y hy hyC
    exact (hzero y hy).mp hyC
  obtain ⟨-, c, hc, hWc⟩ := isInSpanAt_eq_iff.mp ((hIgen _).mp hWI)
  -- `c(z) ≠ 0`: otherwise `W_j ∈ 𝔪_z²`
  have hcz : c z ≠ 0 := by
    intro hc0
    obtain ⟨v, hv⟩ := exists_chartDeriv_coord_ne_zero hWs hzU hinj j
    have hm1 : (pointIdeal n z).mem z c := mem_pointIdeal_of_apply_eq_zero hc hc0
    have hΦz : flatCoord Φ (σ i0) z = 0 := by
      have h : (Φ.toFun (chartAt (ComplexModel n) z z)) (σ i0) = 0 := by rw [hΦ0]; simp
      exact h
    have hm2 : (pointIdeal n z).mem z (flatCoord Φ (σ i0)) := mem_pointIdeal_of_apply_eq_zero hΦt hΦz
    have hpt : ∀ y' g', (pointIdeal n z).mem y' g' → HolomorphicAt n g' y' := fun _ _ hg' => hg'.1
    have h2 := mul_mem_idealPow_add hpt (pow_mem_idealPow hm1 hc 1) (pow_mem_idealPow hm2 hΦt 1)
    have h2' : (idealPow (pointIdeal n z) 2).mem z (fun w => W w j) :=
      OrderTaylor.mem_idealPow_congr h2 (hWc.mono fun y hy => by simp [hy])
    have h0 := OrderTaylor.iterChartDeriv_eq_zero_of_mem_idealPow (e := complexChartAt (n := n) z)
      (mem_chart_source _ z) h2' [v] (by simp)
    exact hv (by simpa using h0)
  -- conclusion
  obtain ⟨hgh, c', hc', hgc⟩ := isInSpanAt_eq_iff.mp ((hIgen g).mp hg)
  refine (hD z hzU g).mpr (isInSpanAt_eq_iff.mpr ⟨hgh, fun y => c' y * (c y)⁻¹,
    hc'.mul (RelativePrincipalizationSpan.holomorphicAt_inv hc hcz), ?_⟩)
  filter_upwards [hgc, hWc, hc.continuousAt.eventually (isOpen_ne.mem_nhds hcz)] with y h1 h2 h3
  rw [h1, h2]
  field_simp

end Exceptional

/-! ### One blowup -/

section Step

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X}

/-- `𝔩^k = (h^k)` at a point where `𝔩 = (h)`. -/
theorem idealPow_mem_iff_of_generator {𝔩 : GermIdeal n Y} {z : Y} {h : Y → ℂ} (hh : HolomorphicAt n h z)
    (hgen : ∀ g, 𝔩.mem z g ↔ IsInSpanAt (n := n) (· = h) z g) (k : ℕ) (g : Y → ℂ) :
    (idealPow 𝔩 k).mem z g ↔ IsInSpanAt (n := n) (· = fun y => h y ^ k) z g := by
  constructor
  · intro hg
    obtain ⟨c, hc, hgc⟩ := exists_eq_mul_pow_of_mem_idealPow (fun g hg => (hgen g).mp hg) hg
    exact isInSpanAt_eq_iff.mpr ⟨holomorphicAt_of_mem_idealPow hg, c, hc, hgc⟩
  · intro hg
    obtain ⟨-, c, hc, hgc⟩ := isInSpanAt_eq_iff.mp hg
    have hpow := pow_mem_idealPow ((hgen h).mpr (isInSpanAt_self rfl hh)) hh k
    exact OrderTaylor.mem_idealPow_congr (mul_mem_idealPow hc hpow) hgc.symm

end Step

end

end Hironaka.NonmonomialTransformTower
