/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Coherence.CoherentIdealColon
import Hironaka.Coherence.CoherentIdealFiniteSpan

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold
namespace Hironaka.CoherentIdealColon
open Hironaka HolomorphicIdealSheaves OkaRelationSheaf OkaIdealOperations CartanLocalReduction InvertibleIdealQuotient
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A generator lies in the span of the family. -/
theorem isInSpanAt_range_self {N : ℕ} {S : Fin N → M → ℂ} {y : M}
    (hS : ∀ i, HolomorphicAt n (S i) y) (i : Fin N) :
    IsInSpanAt (n := n) (· ∈ range S) y (S i) :=
  ⟨hS i, 1, fun _ => S i, fun _ _ => 1, fun _ => ⟨i, rfl⟩, fun _ => holomorphicAt_const 1,
    Eventually.of_forall fun p => by simp⟩

/-- A span of a finite family is closed under holomorphic combinations. -/
theorem isInSpanAt_range_sum {N : ℕ} {S : Fin N → M → ℂ} {y : M} {ι : Type*} [Fintype ι]
    {b g : ι → M → ℂ} (hb : ∀ k, HolomorphicAt n (b k) y)
    (hg : ∀ k, IsInSpanAt (n := n) (· ∈ range S) y (g k)) :
    IsInSpanAt (n := n) (· ∈ range S) y (fun p => ∑ k, b k p * g k p) := by
  have hg' := fun k => (isInSpanAt_range_iff (n := n)).1 (hg k)
  rw [isInSpanAt_range_iff]
  choose hgh c hc hgc using hg'
  refine ⟨HolomorphicAt.sum _ fun k _ => (hb k).mul (hgh k),
    fun i p => ∑ k, b k p * c k i p, fun i => HolomorphicAt.sum _ fun k _ => (hb k).mul (hc k i),
    ?_⟩
  have hall : ∀ᶠ p in 𝓝 y, ∀ k, g k p = ∑ i, c k i p * S i p := eventually_all.2 hgc
  filter_upwards [hall] with p hp
  simp only [hp, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- Spans read in the chart `e = chartAt x`: for generators `s_i ∘ e`, membership at `y` is
membership of `f ∘ e⁻¹` at `e y` in the span of the `s_i`. -/
theorem isInSpanAt_range_comp_chart_iff {x y : M} (hy : y ∈ (chartAt (ComplexModel n) x).source)
    {N : ℕ} (s : Fin N → ComplexModel n → ℂ) (f : M → ℂ) :
    IsInSpanAt (n := n) (· ∈ range fun i p => s i (chartAt (ComplexModel n) x p)) y f ↔
      InSpanAt s (chartAt (ComplexModel n) x y)
        (fun z => f ((chartAt (ComplexModel n) x).symm z)) := by
  set e := chartAt (ComplexModel n) x with hedef
  have hT : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    have := e.continuousAt_symm (e.map_source hy)
    rw [ContinuousAt, e.left_inv hy] at this
    exact this
  rw [isInSpanAt_range_iff]
  constructor
  · rintro ⟨hf, c, hc, hfc⟩
    refine ⟨holAt_comp_chart_symm hy hf, fun i z => c i (e.symm z),
      fun i => holAt_comp_chart_symm hy (hc i), ?_⟩
    filter_upwards [e.open_target.mem_nhds (e.map_source hy), hT.eventually hfc] with z hz hzc
    rw [hzc]
    simp only [e.right_inv hz]
  · rintro ⟨hf, c, hc, hfc⟩
    have hfe : HolomorphicAt n (fun p => (fun z => f (e.symm z)) (e p)) y :=
      holomorphicAt_comp_chart hy hf
    have hcongr : (fun p => f (e.symm (e p))) =ᶠ[𝓝 y] f := by
      filter_upwards [e.open_source.mem_nhds hy] with p hp
      rw [e.left_inv hp]
    refine ⟨hfe.congr hcongr, fun i p => c i (e p), fun i => holomorphicAt_comp_chart hy (hc i), ?_⟩
    filter_upwards [e.open_source.mem_nhds hy, (e.continuousAt hy).eventually hfc] with p hp hpc
    rw [← hpc, e.left_inv hp]


theorem holomorphicAt_of_mdifferentiableOn {h : M → ℂ} {U : Set M} (hU : IsOpen U)
    (hd : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) h U) {y : M} (hy : y ∈ U) :
    HolomorphicAt n h y :=
  eventually_of_mem (hU.mem_nhds hy) fun z hz => (hd z hz).mdifferentiableAt (hU.mem_nhds hz)

theorem holomorphicAt_iff_holAt_chart {x y : M} (hy : y ∈ (chartAt (ComplexModel n) x).source)
    {f : M → ℂ} : HolomorphicAt n f y ↔
      HolAt (fun z => f ((chartAt (ComplexModel n) x).symm z)) (chartAt (ComplexModel n) x y) := by
  set e := chartAt (ComplexModel n) x
  refine ⟨holAt_comp_chart_symm hy, fun h => ?_⟩
  have hfe : HolomorphicAt n (fun p => (fun z => f (e.symm z)) (e p)) y :=
    holomorphicAt_comp_chart hy h
  refine hfe.congr ?_
  filter_upwards [e.open_source.mem_nhds hy] with p hp
  rw [e.left_inv hp]

/-- Membership in a span only depends on the germs of the generators and of the function. -/
theorem isInSpanAt_range_congr {N : ℕ} {S S' : Fin N → M → ℂ} {y : M} {f f' : M → ℂ}
    (hS : ∀ i, S i =ᶠ[𝓝 y] S' i) (hf : f =ᶠ[𝓝 y] f') :
    IsInSpanAt (n := n) (· ∈ range S) y f → IsInSpanAt (n := n) (· ∈ range S') y f' := by
  rw [isInSpanAt_range_iff, isInSpanAt_range_iff]
  rintro ⟨hfh, c, hc, hfc⟩
  refine ⟨hfh.congr hf, c, hc, ?_⟩
  have hall : ∀ᶠ p in 𝓝 y, ∀ i, S i p = S' i p := eventually_all.2 hS
  filter_upwards [hf, hfc, hall] with p h1 h2 h3
  rw [← h1, h2]
  simp only [h3]

/-- Reindexing the generators of a function-level span. -/
theorem inSpanAt_comp_equiv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {μ ν : Type*}
    [Fintype μ] [Fintype ν] (E : ν ≃ μ) (s : μ → X → ℂ) (z : X) (g : X → ℂ) :
    InSpanAt (fun i => s (E i)) z g ↔ InSpanAt s z g := by
  constructor
  · rintro ⟨hg, c, hc, hgc⟩
    refine ⟨hg, fun k => c (E.symm k), fun k => hc _, ?_⟩
    filter_upwards [hgc] with w hw
    rw [hw]
    exact (E.symm.sum_comp fun i => c i w * s (E i) w).symm.trans (by simp)
  · rintro ⟨hg, c, hc, hgc⟩
    refine ⟨hg, fun i => c (E i), fun i => hc _, ?_⟩
    filter_upwards [hgc] with w hw
    rw [hw]
    exact (E.sum_comp fun k => c k w * s k w).symm

/-! ### The theorem -/

/-- **The colon of two coherent ideal sheaves is coherent** (Oka). -/
theorem isCoherent_colon_of_isCoherent {𝔞 𝔩 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent)
    (h𝔩 : 𝔩.IsCoherent) : (colon 𝔞 𝔩).IsCoherent := by
  classical
  intro x
  obtain ⟨Ua, hUa, hxa, K, a, had, hai⟩ := h𝔞 x
  obtain ⟨Ul, hUl, hxl, L, l, hld, hli⟩ := h𝔩 x
  set e := chartAt (ComplexModel n) x with hedef
  have hxe : x ∈ e.source := mem_chart_source _ x
  set D : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' (Ua ∩ Ul) with hDdef
  have hD : IsOpen D := e.isOpen_inter_preimage_symm (hUa.inter hUl)
  have hxD : e x ∈ D := ⟨e.map_source hxe, by
    simp only [mem_preimage, e.left_inv hxe]; exact ⟨hxa, hxl⟩⟩
  -- holomorphy in the chart
  have hchart : ∀ (U : Set M) (h : M → ℂ), IsOpen U →
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) h U →
      ∀ z ∈ e.target, e.symm z ∈ U → HolAt (fun w => h (e.symm w)) z := by
    intro U h hU hd z hz hzU
    have := holAt_comp_chart_symm (x := x) (e.map_target hz)
      (holomorphicAt_of_mdifferentiableOn hU hd hzU)
    rwa [e.right_inv hz] at this
  have haD : ∀ i, DifferentiableOn ℂ (fun w => a i (e.symm w)) D := fun i z hz =>
    (hchart Ua (a i) hUa (had i) z hz.1 hz.2.1).differentiableAt.differentiableWithinAt
  -- the ideal of the `a_i ∘ e⁻¹`, its colon ideals and their intersection
  set A : ComplexModel n → (ComplexModel n → ℂ) → Prop :=
    fun z g => InSpanAt (fun i w => a i (e.symm w)) z g with hAdef
  have hA : IdealFGAt A (e x) :=
    ⟨D, hD, hxD, Fin K, inferInstance, fun i w => a i (e.symm w), haD, fun _ _ _ => Iff.rfl⟩
  have hC : ∀ j, IdealFGAt (colonIdeal A fun w => l j (e.symm w)) (e x) := fun j =>
    hA.colon (OkaCoherence.okaProperty_euclidean n)
      (hchart Ul (l j) hUl (hld j) (e x) hxD.1 (by rw [e.left_inv hxe]; exact hxl))
  obtain ⟨U', hU', hxU', μ, _, s, hsd, hsI⟩ :=
    idealFGAt_iInter (OkaCoherence.okaProperty_euclidean n) L _ hC
  set E := Fintype.equivFin μ
  set s' : Fin (Fintype.card μ) → ComplexModel n → ℂ := fun i => s (E.symm i) with hs'def
  refine ⟨e.source ∩ e ⁻¹' (U' ∩ D), e.isOpen_inter_preimage (hU'.inter hD),
    ⟨hxe, hxU', hxD⟩, Fintype.card μ, fun i p => s' i (e p), fun i p hp => ?_,
    fun y hy f => ?_⟩
  · have hd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s' i) (e p) := by
      rw [mdifferentiableAt_iff_differentiableAt]
      exact (hsd _).differentiableAt (hU'.mem_nhds hp.2.1)
    exact (hd.comp p (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt hp.1)).mdifferentiableWithinAt
  obtain ⟨hye, hyU', hyD⟩ := hy
  have hyUa : y ∈ Ua := by simpa only [mem_preimage, e.left_inv hye] using hyD.2.1
  have hyUl : y ∈ Ul := by simpa only [mem_preimage, e.left_inv hye] using hyD.2.2
  have hlhol : ∀ j, HolomorphicAt n (l j) y := fun j =>
    holomorphicAt_of_mdifferentiableOn hUl (hld j) hyUl
  -- the `a_i ∘ e⁻¹ ∘ e` agree with the `a_i` near `y`
  have haee : ∀ i, (fun p => a i (e.symm (e p))) =ᶠ[𝓝 y] a i := fun i => by
    filter_upwards [e.open_source.mem_nhds hye] with p hp
    rw [e.left_inv hp]
  -- `𝔞`-membership at `y` read in the chart
  have h𝔞chart : ∀ h : M → ℂ, 𝔞.mem y h ↔ A (e y) fun w => h (e.symm w) := by
    intro h
    rw [hai y hyUa, hAdef]
    simp only
    rw [← isInSpanAt_range_comp_chart_iff hye (fun i w => a i (e.symm w)) h]
    exact ⟨isInSpanAt_range_congr (fun i => (haee i).symm) EventuallyEq.rfl,
      isInSpanAt_range_congr haee EventuallyEq.rfl⟩
  rw [isInSpanAt_range_comp_chart_iff hye s' f, hs'def,
    inSpanAt_comp_equiv E.symm s (e y), ← hsI (e y) hyU']
  constructor
  · rintro ⟨hf, hfl⟩
    refine ⟨(holomorphicAt_iff_holAt_chart hye).1 hf, fun j => ⟨(holomorphicAt_iff_holAt_chart hye).1 hf, ?_⟩⟩
    have hmem := hfl (l j) ((hli y hyUl _).2 (isInSpanAt_range_self hlhol j))
    have := (h𝔞chart _).1 hmem
    simpa only [mul_comm] using this
  · rintro ⟨hf, hfC⟩
    have hfM := (holomorphicAt_iff_holAt_chart hye).2 hf
    have hj : ∀ j, IsInSpanAt (n := n) (· ∈ range a) y (fun p => l j p * f p) := by
      intro j
      have h1 := (hfC j).2
      have h2 : 𝔞.mem y (fun p => l j p * f p) := by
        rw [h𝔞chart]
        simpa only [mul_comm] using h1
      exact (hai y hyUa _).1 h2
    refine ⟨hfM, fun g hg => (hai y hyUa _).2 ?_⟩
    obtain ⟨hgh, c, hc, hgc⟩ := (isInSpanAt_range_iff (n := n)).1 ((hli y hyUl g).1 hg)
    refine isInSpanAt_range_congr (fun i => EventuallyEq.rfl) ?_ (isInSpanAt_range_sum hc hj)
    filter_upwards [hgc] with p hp
    rw [hp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring

end Hironaka.CoherentIdealColon
