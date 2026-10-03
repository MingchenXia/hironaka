/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Coherence.OkaIdealOperations
import Hironaka.Coherence.CartanCoherenceDef
import Hironaka.Analytic.HolomorphicBoundedQuotient
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Coherence.OkaRelationSheaf
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Cartan's coherence theorem on manifolds from its local form in `ℂⁿ`

Source: Demailly, *Complex analytic and differential geometry*, II.4.29, first sentence of the
proof: "It is sufficient to prove the result when `A` is an analytic subset in a neighborhood
of `0` in `ℂⁿ`."

`LocalCartan n`: for finitely many functions `f_i` holomorphic on an open `Ω ⊆ ℂⁿ` and
`x₀ ∈ Ω`, the ideal of germs vanishing on `{f = 0}` is finitely generated near `x₀` in the sense
of `OkaIdealOperations.IdealFGAt` (generated at every point of a neighbourhood).

In the preferred chart `e` at `x`, the analytic presentation of `A` at `x` describes `e(A)` near `e x` as `{f = 0}`;
the generators `s_k` of its vanishing ideal near `e x` give the generators `s_k ∘ e` of `𝓘_A` near `x`.

What remains for Cartan's theorem is `LocalCartan n`.
-/

open Set Filter
open scoped Topology Manifold

universe u

namespace Hironaka.CartanLocalReduction

open Hironaka.HolomorphicIdealSheaves OkaRelationSheaf OkaIdealOperations CartanComponentIdeal

/-- **Cartan's theorem, local form in `ℂⁿ`.** -/
def LocalCartan (n : ℕ) : Prop :=
  ∀ (Ω : Set (ComplexModel n)), IsOpen Ω → ∀ (N : ℕ) (f : Fin N → ComplexModel n → ℂ),
    (∀ i, DifferentiableOn ℂ (f i) Ω) → ∀ x₀ ∈ Ω,
      IdealFGAt (vanishingIdealF {w | ∀ i, f i w = 0}) x₀

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A function holomorphic near `y` is holomorphic near `e y` in the coordinates of a chart
`e = chartAt x` containing `y`. -/
theorem holAt_comp_chart_symm {f : M → ℂ} {x y : M}
    (hy : y ∈ (chartAt (ComplexModel n) x).source) (hf : HolomorphicAt n f y) :
    HolAt (fun z => f ((chartAt (ComplexModel n) x).symm z)) (chartAt (ComplexModel n) x y) := by
  set e := chartAt (ComplexModel n) x
  have hT : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    have := e.continuousAt_symm (e.map_source hy)
    rw [ContinuousAt, e.left_inv hy] at this
    exact this
  filter_upwards [e.open_target.mem_nhds (e.map_source hy), hT.eventually hf] with z hz hfz
  rw [← mdifferentiableAt_iff_differentiableAt]
  exact hfz.comp z (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt_symm hz)

/-- A function holomorphic near `e y` in the coordinates of `e = chartAt x`, composed with `e`,
is holomorphic near `y`. -/
theorem holomorphicAt_comp_chart {W : ComplexModel n → ℂ} {x y : M}
    (hy : y ∈ (chartAt (ComplexModel n) x).source)
    (hW : HolAt W (chartAt (ComplexModel n) x y)) :
    HolomorphicAt n (fun p => W (chartAt (ComplexModel n) x p)) y := by
  set e := chartAt (ComplexModel n) x
  filter_upwards [e.open_source.mem_nhds hy, (e.continuousAt hy).eventually hW] with p hp hWp
  have hWm : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) W (e p) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact hWp
  exact hWm.comp p (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt hp)

/-- **Cartan's theorem on a manifold from its local form.** -/
theorem cartanCoherence_of_localCartan (hloc : LocalCartan n) : CartanCoherence n M := by
  classical
  intro A hA x
  obtain ⟨P⟩ := hA x
  set e := chartAt (ComplexModel n) x with hedef
  have hce : (complexChartAt (n := n) x).val = e := rfl
  have hxe : x ∈ e.source := mem_chart_source (ComplexModel n) x
  -- the set `{f = 0}` in coordinates
  set B : Set (ComplexModel n) := {w | ∀ i, P.generator i w = 0} with hBdef
  set Ω := P.coordinateNeighborhood
  have hΩ : IsOpen Ω := P.isOpen_coordinateNeighborhood
  have hxΩ : e x ∈ Ω := P.center_mem_coordinateNeighborhood
  have hΩt : Ω ⊆ e.target := P.coordinateNeighborhood_subset_target
  have hAB : ∀ y ∈ e.source, e y ∈ Ω → (y ∈ A ↔ e y ∈ B) := fun y hy hyΩ =>
    P.zeroLocus (y := y) hy hyΩ
  obtain ⟨U', hU', hxU', μ, _, s, hsd, hsI⟩ :=
    hloc Ω hΩ P.generatorCount P.generator P.generator_holomorphic (e x) hxΩ
  -- the generators on `M`
  set E := Fintype.equivFin μ
  set S : Fin (Fintype.card μ) → M → ℂ := fun i p => s (E.symm i) (e p) with hSdef
  refine ⟨e.source ∩ e ⁻¹' (U' ∩ Ω), e.isOpen_inter_preimage (hU'.inter hΩ),
    ⟨hxe, hxU', hxΩ⟩, Fintype.card μ, S, fun i p hp => ?_, fun y hy g => ?_⟩
  · have hd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s (E.symm i)) (e p) := by
      rw [mdifferentiableAt_iff_differentiableAt]
      exact (hsd _).differentiableAt (hU'.mem_nhds hp.2.1)
    exact (hd.comp p (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt hp.1)).mdifferentiableWithinAt
  obtain ⟨hye, hyU', hyΩ⟩ := hy
  have hT : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    have := e.continuousAt_symm (e.map_source hye)
    rw [ContinuousAt, e.left_inv hye] at this
    exact this
  -- near `e y`, membership in `B` is membership of `e⁻¹ w` in `A`
  have hBnear : ∀ᶠ w in 𝓝 (e y), (w ∈ B ↔ e.symm w ∈ A) := by
    filter_upwards [hΩ.mem_nhds hyΩ] with w hwΩ
    have hw := hAB (e.symm w) (e.map_target (hΩt hwΩ)) (by rwa [e.right_inv (hΩt hwΩ)])
    rw [e.right_inv (hΩt hwΩ)] at hw
    exact hw.symm
  -- near `y`, membership in `A` is membership of `e p` in `B`
  have hAnear : ∀ᶠ p in 𝓝 y, (p ∈ A ↔ e p ∈ B) := by
    filter_upwards [e.open_source.mem_nhds hye, (e.continuousAt hye).eventually
      (hΩ.mem_nhds hyΩ)] with p hp hpΩ
    exact hAB p hp hpΩ
  have hsy : ∀ k, HolAt (s k) (e y) := fun k => holAt_of_differentiableOn hU' (hsd k) hyU'
  constructor
  · rintro ⟨hg, hgA⟩
    have hG : vanishingIdealF B (e y) fun w => g (e.symm w) := by
      refine ⟨holAt_comp_chart_symm hye hg, ?_⟩
      filter_upwards [hBnear, hT.eventually hgA] with w hw hwA hwB
      exact hwA (hw.1 hwB)
    obtain ⟨-, c, hc, hgc⟩ := (hsI (e y) hyU' _).1 hG
    refine ⟨hg, Fintype.card μ, S, fun i p => c (E.symm i) (e p), fun i => ⟨i, rfl⟩,
      fun i => holomorphicAt_comp_chart hye (hc _), ?_⟩
    filter_upwards [e.open_source.mem_nhds hye, (e.continuousAt hye).eventually hgc]
      with p hp hpc
    simp only [e.left_inv hp] at hpc
    rw [hpc]
    exact (E.symm.sum_comp fun k => c k (e p) * s k (e p)).symm
  · rintro ⟨hg, N', s', a, hs', ha, hga⟩
    refine ⟨hg, ?_⟩
    -- every generator vanishes on `A` near `y`
    have hSv : ∀ i, ∀ᶠ p in 𝓝 y, p ∈ A → S i p = 0 := by
      intro i
      have hk := ((hsI (e y) hyU' _).2 (inSpanAt_self hsy (E.symm i))).2
      filter_upwards [hAnear, (e.continuousAt hye).eventually hk] with p hpA hpk hp
      exact hpk (hpA.1 hp)
    have hall : ∀ᶠ p in 𝓝 y, ∀ i, p ∈ A → S i p = 0 := eventually_all.2 hSv
    filter_upwards [hga, hall] with p hp hpS hpA
    rw [hp]
    refine Finset.sum_eq_zero fun j _ => ?_
    obtain ⟨i, hi⟩ := hs' j
    rw [← hi, hpS i hpA, mul_zero]

end Hironaka.CartanLocalReduction
