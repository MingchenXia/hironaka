/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupSpaceRatio
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.BlowupSpace
import Hironaka.Blowup.BlowupSpaceTangent
import Hironaka.Analytic.HolomorphicGermAlgebra
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The coordinate changes of the blowup are holomorphic

Source: Demailly, *Complex analytic and differential geometry*, VII.12.2 (`agbook.tex` lines 20306--20326).

Fourth module of the construction of the blowup. The atlas `blowupAtlas n C` consists of Demailly's monomial charts
`τ̃ⱼ` over all flattening charts (`FlatChart.toPartialEquiv`) and the charts of `X` restricted to `X \ C`
(`OffChart.toPartialEquiv`). For two charts `a, b` of the atlas the coordinate change `b ∘ a⁻¹` has an open domain
`a.target ∩ a⁻¹(b.source)` and is holomorphic there (`isOpen_transition`, `differentiableOn_transition`). Between
two monomial charts this is Demailly's lemma (`FlatChart.differentiableAt_ratio`): the coordinates of `τ̃'ⱼ'` are
`(τ'ᵢ/τ'ⱼ')~ = (τ'ᵢ/τⱼ)~ / (τ'ⱼ'/τⱼ)~`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupConstruction

open Hironaka.HolomorphicIdealSheaves BlowupFlatCoordinates BlowupMonomialCharts BlowupSpaceTangent BlowupSpace

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {C : Set X}

variable (n C) in
/-- The atlas of the blowup: Demailly's monomial charts and the charts of `X \ C`. -/
def blowupAtlas : Set (PartialEquiv (BlowupSpace n C) (ComplexModel n)) :=
  range (FlatChart.toPartialEquiv (n := n) (C := C)) ∪
    range (OffChart.toPartialEquiv (n := n) (C := C))

/-! ### Elementary facts about the charts -/

namespace FlatChart

variable (c : FlatChart n C)

@[simp] theorem toPartialEquiv_source : c.toPartialEquiv.source = c.source := rfl
@[simp] theorem toPartialEquiv_target : c.toPartialEquiv.target = c.target := rfl
@[simp] theorem toPartialEquiv_apply (p : BlowupSpace n C) : c.toPartialEquiv p = c.toFun p := rfl
@[simp] theorem toPartialEquiv_symm_apply (w : ComplexModel n) :
    c.toPartialEquiv.symm w = c.invFun w := rfl

theorem continuousOn_pt : ContinuousOn c.pt c.target := fun _ hw =>
  (show ContinuousAt c.pt _ from c.continuousAt_pt hw).continuousWithinAt

theorem isOpen_target_inter_pt (V : Set X) (hV : IsOpen V) : IsOpen (c.target ∩ c.pt ⁻¹' V) :=
  c.continuousOn_pt.isOpen_inter_preimage c.isOpen_target hV

theorem isOpen_dom : IsOpen c.dom := isOpen_flatDomain c.Φ

theorem holomorphicAt_τ (i : Fin n) {x : X} (hx : x ∈ c.dom) : HolomorphicAt n (c.τ i) x :=
  holomorphicAt_flatCoord c.Φ i hx

theorem mem_source_iff {p : BlowupSpace n C} :
    p ∈ c.source ↔ p.base ∈ c.dom ∧ extVal (c.τ c.j) p ≠ 0 := Iff.rfl

theorem extVal_invFun_ne {w : ComplexModel n} (hw : w ∈ c.target) :
    extVal (c.τ c.j) (c.invFun w) ≠ 0 := (c.map_target hw).2

/-- `(f/τⱼ)~` is holomorphic at `w₀` for every `f` vanishing on `C` near the points of an open
set containing the base of `w₀`; here for the flat coordinates of another chart. -/
theorem differentiableAt_ratio_τ (c' : FlatChart n C) {i : Fin n} (hi : c'.k ≤ i.1)
    {w : ComplexModel n} (hw : w ∈ c.target) (hdom : c.pt w ∈ c'.dom) :
    DifferentiableAt ℂ (c.ratio (c'.τ i)) w :=
  c.differentiableAt_ratio (V := c'.dom) (fun _ hx => c'.τ_mem_vanishingIdeal hx hi)
    c'.isOpen_dom hw hdom

theorem continuousOn_ratio_τ (c' : FlatChart n C) {i : Fin n} (hi : c'.k ≤ i.1) :
    ContinuousOn (c.ratio (c'.τ i)) (c.target ∩ c.pt ⁻¹' c'.dom) := fun _ hw =>
  (c.differentiableAt_ratio_τ c' hi hw.1 hw.2).continuousAt.continuousWithinAt

end FlatChart

namespace OffChart

variable (o : OffChart n C)

@[simp] theorem toPartialEquiv_symm_apply_of_not_mem {z : ComplexModel n} (h : o.e.symm z ∉ C) :
    o.toPartialEquiv.symm z = offPoint (o.e.symm z) h :=
  o.symm_apply_of_not_mem h

end OffChart

/-! ### The four kinds of coordinate changes -/

section Transitions

/-- The domain of a coordinate change. -/
abbrev transSource (a b : PartialEquiv (BlowupSpace n C) (ComplexModel n)) : Set (ComplexModel n) :=
  a.target ∩ a.symm ⁻¹' b.source

theorem transSource_flat_flat (c c' : FlatChart n C) :
    transSource c.toPartialEquiv c'.toPartialEquiv =
      {w | w ∈ c.target ∧ c.pt w ∈ c'.dom ∧ c.ratio (c'.τ c'.j) w ≠ 0} := by
  ext w
  simp only [transSource, mem_inter_iff, mem_preimage, FlatChart.toPartialEquiv_target,
    FlatChart.toPartialEquiv_symm_apply, FlatChart.toPartialEquiv_source, mem_ofPred_eq]
  constructor
  · rintro ⟨hw, hdom, hne⟩
    rw [c.base_invFun hw] at hdom
    exact ⟨hw, hdom, div_ne_zero hne (c.extVal_invFun_ne hw)⟩
  · rintro ⟨hw, hdom, hne⟩
    refine ⟨hw, by rw [c.base_invFun hw]; exact hdom, fun h => hne ?_⟩
    rw [FlatChart.ratio, h, zero_div]

theorem isOpen_transSource_flat_flat (c c' : FlatChart n C) :
    IsOpen (transSource c.toPartialEquiv c'.toPartialEquiv) := by
  rw [transSource_flat_flat]
  have h := (c.continuousOn_ratio_τ c' c'.hj).isOpen_inter_preimage
    (c.isOpen_target_inter_pt _ c'.isOpen_dom) (isOpen_compl_singleton (x := (0 : ℂ)))
  convert h using 1
  ext w
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff]
  tauto

theorem differentiableOn_flat_flat (c c' : FlatChart n C) :
    DifferentiableOn ℂ (c'.toPartialEquiv ∘ c.toPartialEquiv.symm)
      (transSource c.toPartialEquiv c'.toPartialEquiv) := by
  intro w hw
  have hS := isOpen_transSource_flat_flat c c'
  rw [transSource_flat_flat] at hS hw
  obtain ⟨hwT, hdom, hne⟩ := hw
  set G : ComplexModel n → ComplexModel n := fun w' => WithLp.toLp 2 fun i =>
    if c'.k ≤ i.1 ∧ i ≠ c'.j then c.ratio (c'.τ i) w' / c.ratio (c'.τ c'.j) w'
    else c'.τ i (c.pt w') with hG
  have hev : (c'.toPartialEquiv ∘ c.toPartialEquiv.symm) =ᶠ[𝓝 w] G := by
    filter_upwards [hS.mem_nhds ⟨hwT, hdom, hne⟩] with w' hw'
    obtain ⟨hw'T, -, -⟩ := hw'
    ext i
    simp only [Function.comp_apply, FlatChart.toPartialEquiv_apply,
      FlatChart.toPartialEquiv_symm_apply, hG, PiLp.toLp_apply]
    by_cases hi : c'.k ≤ i.1 ∧ i ≠ c'.j
    · rw [c'.toFun_apply_normal _ hi.1 hi.2, if_pos hi, FlatChart.ratio, FlatChart.ratio,
        div_div_div_cancel_right₀ (c.extVal_invFun_ne hw'T)]
    · rw [c'.toFun_apply_of_not _ hi, if_neg hi, c.base_invFun hw'T]
  have hGd : DifferentiableAt ℂ G w := by
    refine (differentiableAt_piLp 2).mpr fun i => ?_
    simp only [hG, PiLp.toLp_apply]
    by_cases hi : c'.k ≤ i.1 ∧ i ≠ c'.j
    · simp only [if_pos hi, div_eq_mul_inv]
      exact (c.differentiableAt_ratio_τ c' hi.1 hwT hdom).fun_mul
        ((c.differentiableAt_ratio_τ c' c'.hj hwT hdom).inv hne)
    · simp only [if_neg hi]
      exact c.differentiableAt_comp_pt hwT (c'.holomorphicAt_τ i hdom)
  exact (hGd.congr_of_eventuallyEq hev).differentiableWithinAt

theorem transSource_flat_off (c : FlatChart n C) (o : OffChart n C) :
    transSource c.toPartialEquiv o.toPartialEquiv =
      {w | w ∈ c.target ∧ w c.j ≠ 0 ∧ c.pt w ∈ o.e.source} := by
  ext w
  simp only [transSource, mem_inter_iff, mem_preimage, FlatChart.toPartialEquiv_target,
    FlatChart.toPartialEquiv_symm_apply, o.source_eq, mem_ofPred_eq]
  constructor
  · rintro ⟨hw, hsrc, hC⟩
    rw [c.base_invFun hw] at hsrc hC
    exact ⟨hw, fun h => hC ((c.pt_mem_iff hw).mpr h), hsrc⟩
  · rintro ⟨hw, hj, hsrc⟩
    rw [c.base_invFun hw]
    exact ⟨hw, hsrc, fun h => hj ((c.pt_mem_iff hw).mp h)⟩

theorem isOpen_transSource_flat_off (c : FlatChart n C) (o : OffChart n C) :
    IsOpen (transSource c.toPartialEquiv o.toPartialEquiv) := by
  rw [transSource_flat_off]
  have h1 := c.isOpen_target_inter_pt _ o.e.open_source
  have h2 : IsOpen {w : ComplexModel n | w c.j ≠ 0} :=
    isOpen_ne_fun (EuclideanSpace.proj c.j : ComplexModel n →L[ℂ] ℂ).continuous continuous_const
  convert h1.inter h2 using 1
  ext w
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  tauto

theorem differentiableAt_chart_pt (c : FlatChart n C) (y : X) {w : ComplexModel n}
    (hw : w ∈ c.target) (hy : c.pt w ∈ (chartAt (ComplexModel n) y).source) :
    DifferentiableAt ℂ (fun w' => chartAt (ComplexModel n) y (c.pt w')) w := by
  have hz : c.Φ.invFun (monomial c.k c.j w) ∈ (chartAt (ComplexModel n) c.y₀).target :=
    c.hsrc (c.Φ.mapsTo_invFun hw)
  have h1 := differentiableAt_chart_comp_chart_symm (y₀ := y) hz hy
  exact (h1.comp _ (c.Φ.invFun_holomorphic.differentiableAt (c.Φ.isOpen_target.mem_nhds hw))).comp w
    ((contDiff_monomial c.k c.j).differentiable (by simp) w)

theorem differentiableOn_flat_off (c : FlatChart n C) (o : OffChart n C) :
    DifferentiableOn ℂ (o.toPartialEquiv ∘ c.toPartialEquiv.symm)
      (transSource c.toPartialEquiv o.toPartialEquiv) := by
  intro w hw
  have hS := isOpen_transSource_flat_off c o
  have hw' := hw
  rw [transSource_flat_off] at hw'
  obtain ⟨hwT, -, hsrc⟩ := hw'
  have hev : (o.toPartialEquiv ∘ c.toPartialEquiv.symm) =ᶠ[𝓝 w] fun w' => o.e (c.pt w') := by
    filter_upwards [hS.mem_nhds hw] with w' hw''
    rw [transSource_flat_off] at hw''
    simp only [Function.comp_apply, FlatChart.toPartialEquiv_symm_apply, o.apply_eq,
      c.base_invFun hw''.1]
  exact ((differentiableAt_chart_pt c o.x₀ hwT hsrc).congr_of_eventuallyEq hev).differentiableWithinAt

theorem transSource_off_flat (o : OffChart n C) (c : FlatChart n C) :
    transSource o.toPartialEquiv c.toPartialEquiv =
      {z | z ∈ o.e.target ∧ o.e.symm z ∉ C ∧ o.e.symm z ∈ c.dom ∧ c.τ c.j (o.e.symm z) ≠ 0} := by
  ext z
  simp only [transSource, mem_inter_iff, mem_preimage, o.target_eq, mem_compl_iff,
    FlatChart.toPartialEquiv_source, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hz, hC⟩, hsrc⟩
    rw [o.toPartialEquiv_symm_apply_of_not_mem hC, c.mem_source_iff, extVal_of_not_mem hC] at hsrc
    exact ⟨hz, hC, hsrc⟩
  · rintro ⟨hz, hC, hsrc⟩
    refine ⟨⟨hz, hC⟩, ?_⟩
    rw [o.toPartialEquiv_symm_apply_of_not_mem hC, c.mem_source_iff, extVal_of_not_mem hC]
    exact hsrc

theorem isOpen_transSource_off_flat (hC : IsClosed C) (o : OffChart n C) (c : FlatChart n C) :
    IsOpen (transSource o.toPartialEquiv c.toPartialEquiv) := by
  rw [transSource_off_flat]
  have hcont : ContinuousOn (c.τ c.j) (c.dom ∩ Cᶜ) := fun x hx =>
    (c.holomorphicAt_τ c.j hx.1).continuousAt.continuousWithinAt
  have hV := hcont.isOpen_inter_preimage (c.isOpen_dom.inter hC.isOpen_compl)
    (isOpen_compl_singleton (x := (0 : ℂ)))
  convert o.e.isOpen_inter_preimage_symm hV using 1
  ext z
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff]
  tauto

theorem differentiableOn_off_flat (hC : IsClosed C) (o : OffChart n C) (c : FlatChart n C) :
    DifferentiableOn ℂ (c.toPartialEquiv ∘ o.toPartialEquiv.symm)
      (transSource o.toPartialEquiv c.toPartialEquiv) := by
  intro z hz
  have hS := isOpen_transSource_off_flat hC o c
  have hz' := hz
  rw [transSource_off_flat] at hz'
  obtain ⟨hzT, -, hdom, -⟩ := hz'
  set G : ComplexModel n → ComplexModel n := fun z' => WithLp.toLp 2 fun i =>
    if c.k ≤ i.1 ∧ i ≠ c.j then c.τ i (o.e.symm z') / c.τ c.j (o.e.symm z') else c.τ i (o.e.symm z')
    with hG
  have hev : (c.toPartialEquiv ∘ o.toPartialEquiv.symm) =ᶠ[𝓝 z] G := by
    filter_upwards [hS.mem_nhds hz] with z' hz''
    rw [transSource_off_flat] at hz''
    obtain ⟨-, hC', -, -⟩ := hz''
    ext i
    simp only [Function.comp_apply, FlatChart.toPartialEquiv_apply,
      o.toPartialEquiv_symm_apply_of_not_mem hC', hG, PiLp.toLp_apply]
    by_cases hi : c.k ≤ i.1 ∧ i ≠ c.j
    · rw [c.toFun_apply_normal _ hi.1 hi.2, if_pos hi, extVal_of_not_mem hC',
        extVal_of_not_mem hC']
      rfl
    · rw [c.toFun_apply_of_not _ hi, if_neg hi]
      rfl
  have hd : ∀ i, DifferentiableAt ℂ (fun z' => c.τ i (o.e.symm z')) z := fun i =>
    differentiableAt_comp_chart_symm hzT (c.holomorphicAt_τ i hdom).mdifferentiableAt
  have hne : c.τ c.j (o.e.symm z) ≠ 0 := by
    rw [transSource_off_flat] at hz; exact hz.2.2.2
  have hGd : DifferentiableAt ℂ G z := by
    refine (differentiableAt_piLp 2).mpr fun i => ?_
    simp only [hG, PiLp.toLp_apply]
    by_cases hi : c.k ≤ i.1 ∧ i ≠ c.j
    · simp only [if_pos hi, div_eq_mul_inv]
      exact (hd i).fun_mul ((hd c.j).inv hne)
    · simp only [if_neg hi]
      exact hd i
  exact (hGd.congr_of_eventuallyEq hev).differentiableWithinAt

theorem transSource_off_off (o o' : OffChart n C) :
    transSource o.toPartialEquiv o'.toPartialEquiv =
      {z | z ∈ o.e.target ∧ o.e.symm z ∉ C ∧ o.e.symm z ∈ o'.e.source} := by
  ext z
  simp only [transSource, mem_inter_iff, mem_preimage, o.target_eq, mem_compl_iff, o'.source_eq,
    mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hz, hC⟩, hsrc, -⟩
    rw [o.toPartialEquiv_symm_apply_of_not_mem hC] at hsrc
    exact ⟨hz, hC, hsrc⟩
  · rintro ⟨hz, hC, hsrc⟩
    rw [o.toPartialEquiv_symm_apply_of_not_mem hC]
    exact ⟨⟨hz, hC⟩, hsrc, hC⟩

theorem isOpen_transSource_off_off (hC : IsClosed C) (o o' : OffChart n C) :
    IsOpen (transSource o.toPartialEquiv o'.toPartialEquiv) := by
  rw [transSource_off_off]
  convert o.e.isOpen_inter_preimage_symm (hC.isOpen_compl.inter o'.e.open_source) using 1
  ext z
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff]

theorem differentiableOn_off_off (hC : IsClosed C) (o o' : OffChart n C) :
    DifferentiableOn ℂ (o'.toPartialEquiv ∘ o.toPartialEquiv.symm)
      (transSource o.toPartialEquiv o'.toPartialEquiv) := by
  intro z hz
  have hS := isOpen_transSource_off_off hC o o'
  have hz' := hz
  rw [transSource_off_off] at hz'
  obtain ⟨hzT, -, hsrc⟩ := hz'
  have hev : (o'.toPartialEquiv ∘ o.toPartialEquiv.symm) =ᶠ[𝓝 z] fun z' => o'.e (o.e.symm z') := by
    filter_upwards [hS.mem_nhds hz] with z' hz''
    rw [transSource_off_off] at hz''
    simp only [Function.comp_apply, o.toPartialEquiv_symm_apply_of_not_mem hz''.2.1, o'.apply_eq,
      base_offPoint]
  exact ((differentiableAt_chart_comp_chart_symm hzT hsrc).congr_of_eventuallyEq hev).differentiableWithinAt

/-- **The coordinate changes of the blowup are holomorphic on open domains.** -/
theorem isOpen_transSource_and_differentiableOn (hC : IsClosed C)
    {a b : PartialEquiv (BlowupSpace n C) (ComplexModel n)} (ha : a ∈ blowupAtlas n C)
    (hb : b ∈ blowupAtlas n C) :
    IsOpen (transSource a b) ∧ DifferentiableOn ℂ (b ∘ a.symm) (transSource a b) := by
  rcases ha with ⟨c, rfl⟩ | ⟨o, rfl⟩ <;> rcases hb with ⟨c', rfl⟩ | ⟨o', rfl⟩
  · exact ⟨isOpen_transSource_flat_flat c c', differentiableOn_flat_flat c c'⟩
  · exact ⟨isOpen_transSource_flat_off c o', differentiableOn_flat_off c o'⟩
  · exact ⟨isOpen_transSource_off_flat hC o c', differentiableOn_off_flat hC o c'⟩
  · exact ⟨isOpen_transSource_off_off hC o o', differentiableOn_off_off hC o o'⟩

end Transitions

end

end Hironaka.BlowupConstruction
