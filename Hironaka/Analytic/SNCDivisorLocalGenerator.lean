/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.HolomorphicCoordinateFactorization
import Hironaka.Blowup.NormalCrossings
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Manifold.ChartDifferentiable

set_option autoImplicit false

/-! # Genuine local SNC divisor generators from the actual support and adapted coordinates -/

open Set Filter
open scoped Topology Manifold

namespace Hironaka.SNCDivisorLocalGenerator

open Hironaka.HolomorphicIdealSheaves NormalCrossings
  InvertibleIdealQuotient

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- A genuine principal stalk presentation identifies the support with the generator zero. -/
theorem mem_support_iff_generator_eq_zero
    (D : EffectiveDivisor n M) {y : M} {g : M → ℂ} (hg : HolomorphicAt n g y)
    (hgen : ∀ f : M → ℂ, D.ideal.mem y f ↔ IsInSpanAt (n := n) (· = g) y f) :
    y ∈ D.support ↔ g y = 0 := by
  constructor
  · intro hy
    exact hy g ((hgen g).mpr (isInSpanAt_self rfl hg))
  · intro hzero f hf
    obtain ⟨_, a, _, heq⟩ := isInSpanAt_eq_iff.mp ((hgen f).mp hf)
    calc
      f y = a y * g y := heq.self_of_nhds
      _ = 0 := by rw [hzero, mul_zero]

/-- Genuine invertibility and SNC geometry supply the full local generator and its monomial. -/
theorem exists_adapted_unit_monomial_generator
    (D : EffectiveDivisor n M) (E : List (Set M)) (hE : IsSNCDivisor n E)
    (hsupport : D.support = ⋃ H ∈ E, H) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ g : M → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g U ∧
      (∀ W : Set M, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0) ∧
      (∀ y ∈ U, ∀ f : M → ℂ, D.ideal.mem y f ↔ IsInSpanAt (n := n) (· = g) y f) ∧
      ∃ (S : Fin E.length → Finset (Fin n))
        (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x)),
        Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
        Φ.toFun ((complexChartAt (n := n) x).val x) = 0 ∧
        (∀ i, x ∈ E.get i → (S i).card = 1) ∧ Set.InjOn S {i | x ∈ E.get i} ∧
        (∀ i, x ∈ E.get i → ∀ {y : M}, y ∈ (complexChartAt (n := n) x).val.source →
          (complexChartAt (n := n) x).val y ∈ Φ.source →
          (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S i))) ∧
        ∃ (a : Fin n → ℕ) (H : ComplexModel n → ℂ),
          (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z) ∧ H 0 ≠ 0 ∧
          (fun z => g ((complexChartAt (n := n) x).val.symm (Φ.invFun z))) =ᶠ[𝓝 0]
            fun z => H z * ∏ j : Fin n, z j ^ a j := by
  classical
  obtain ⟨U, hU, hxU, g, hg, hnon, hgen⟩ := D.isInvertible x
  obtain ⟨S, ⟨Φ, hsrc, h0, hflat⟩, hcard, hinj⟩ := hE.2 x
  let e := complexChartAt (n := n) x
  have h0t : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← h0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = e.val x := by
    rw [← h0]
    exact Φ.left_inv _ Φ.center_mem_source
  let T : ComplexModel n → M := fun z => e.val.symm (Φ.invFun z)
  have hT0 : T 0 = x := by
    dsimp only [T]
    rw [hinv0, e.val.left_inv (mem_chart_source (ComplexModel n) x)]
  have hTc : ContinuousAt T 0 :=
    (e.val.continuousAt_symm (hsrc (Φ.mapsTo_invFun h0t))).comp
      ((Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds h0t)).continuousAt)
  have hT : Tendsto T (𝓝 0) (𝓝 x) := by
    simpa only [hT0] using hTc.tendsto
  have havoid : ∀ᶠ y in 𝓝 x, ∀ i : Fin E.length, x ∉ E.get i → y ∉ E.get i := by
    apply eventually_all.mpr
    intro i
    by_cases hxi : x ∈ E.get i
    · exact Eventually.of_forall fun _ h => (h hxi).elim
    · have hi : ∀ᶠ y in 𝓝 x, y ∉ E.get i :=
        (hE.1 _ (List.get_mem _ _)).isOpen_compl.mem_nhds hxi
      exact hi.mono fun _ hy _ => hy
  let G : ComplexModel n → ℂ := fun z => g (T z)
  have hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z := by
    have hchart := differentiableOn_comp_chartSymm x hg
    have hopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) :=
      e.val.isOpen_inter_preimage_symm hU
    filter_upwards [Φ.isOpen_target.mem_nhds h0t, hT.eventually (hU.mem_nhds hxU)] with z hz hzU
    have hcoord : DifferentiableAt ℂ (fun w => g (e.val.symm w)) (Φ.invFun z) :=
      hchart.differentiableAt (hopen.mem_nhds ⟨hsrc (Φ.mapsTo_invFun hz), hzU⟩)
    exact hcoord.comp z
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz))
  have hzero : ∀ᶠ z in 𝓝 0, G z = 0 → ∃ j : Fin n, z j = 0 := by
    filter_upwards [Φ.isOpen_target.mem_nhds h0t,
      hT.eventually (hU.mem_nhds hxU), hT.eventually havoid] with z hz hzU hzavoid hGz
    have hsup : T z ∈ D.support :=
      (mem_support_iff_generator_eq_zero D
        (holomorphicAt_of_mdifferentiableOn hU hg hzU) (hgen (T z) hzU)).mpr hGz
    have hmem : ∃ H ∈ E, T z ∈ H := by
      rw [hsupport] at hsup
      obtain ⟨F, hF⟩ := mem_iUnion.mp hsup
      obtain ⟨hFE, hzF⟩ := mem_iUnion.mp hF
      exact ⟨F, hFE, hzF⟩
    obtain ⟨i, hi⟩ := List.exists_mem_iff_get.mp hmem
    have hxi : x ∈ E.get i := by
      by_contra h
      exact hzavoid i h hi
    have htarget : Φ.invFun z ∈ e.val.target := hsrc (Φ.mapsTo_invFun hz)
    have hy : T z ∈ e.val.source := e.val.map_target htarget
    have hphi : e.val (T z) ∈ Φ.source := by
      dsimp only [T]
      rw [e.val.right_inv htarget]
      exact Φ.mapsTo_invFun hz
    have heq : Φ.toFun (e.val (T z)) = z := by
      dsimp only [T]
      rw [e.val.right_inv htarget, Φ.right_inv z hz]
    have hsub : z ∈ coordSubspace (S i) := by
      rw [← heq]
      exact (hflat i hxi hy hphi).mp hi
    have hpos : 0 < (S i).card := by rw [hcard i hxi]; norm_num
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    exact ⟨j, hsub j hj⟩
  obtain ⟨a, H, hH, hH0, hfactor⟩ :=
    HolomorphicCoordinateFactorization.exists_unit_mul_coordinate_monomial_of_zero_locus hG hzero
  exact ⟨U, hU, hxU, g, hg, hnon, hgen, S, Φ, hsrc, h0, hcard, hinj, hflat,
    a, H, hH, hH0, hfactor⟩

end
end Hironaka.SNCDivisorLocalGenerator
