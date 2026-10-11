/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.EuclideanHolomorphicGermSpan
import Hironaka.Analytic.ComplexAnalyticSubvarieties

set_option autoImplicit false

/-! # Complete finite germ spans under genuine local holomorphic coordinate equivalences -/

open Set Filter
open scoped Topology Manifold

namespace Hironaka.LocalHolomorphicFiniteSpanTransport

open Hironaka.HolomorphicIdealSheaves

open Hironaka
noncomputable section

private theorem tendsto_inv {n : ℕ} {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) :
    Tendsto Φ.invFun (𝓝 (Φ.toFun p)) (𝓝 p) := by
  have hp : Φ.toFun p ∈ Φ.target := Φ.mapsTo_toFun Φ.center_mem_source
  have h := (Φ.invFun_holomorphic.differentiableAt
    (Φ.isOpen_target.mem_nhds hp)).continuousAt.tendsto
  simpa only [Φ.left_inv p Φ.center_mem_source] using h

/-- Holomorphy returns from the actual inverse coordinate chart to the literal function. -/
theorem holomorphicAt_comp_inv_iff {n : ℕ} {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) {f : ComplexModel n → ℂ} :
    HolomorphicAt n (fun z => f (Φ.invFun z)) (Φ.toFun p) ↔ HolomorphicAt n f p := by
  have hp : Φ.toFun p ∈ Φ.target := Φ.mapsTo_toFun Φ.center_mem_source
  have hto : Tendsto Φ.toFun (𝓝 p) (𝓝 (Φ.toFun p)) :=
    (Φ.toFun_holomorphic.differentiableAt
      (Φ.isOpen_source.mem_nhds Φ.center_mem_source)).continuousAt.tendsto
  constructor
  · intro hf
    have hcomp : HolomorphicAt n (fun y => f (Φ.invFun (Φ.toFun y))) p := by
      filter_upwards [hto.eventually hf, Φ.isOpen_source.mem_nhds Φ.center_mem_source]
        with y hy hys
      exact (hy.differentiableAt.comp y
        (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hys))).mdifferentiableAt
    exact hcomp.congr ((show ∀ᶠ y in 𝓝 p, y ∈ Φ.source from
      Φ.isOpen_source.mem_nhds Φ.center_mem_source).mono fun y hy =>
      congrArg f (Φ.left_inv y hy))
  · intro hf
    filter_upwards [(tendsto_inv Φ).eventually hf, Φ.isOpen_target.mem_nhds hp]
      with z hz hzt
    exact (hz.differentiableAt.comp z
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hzt))).mdifferentiableAt

/-- Full finite-span membership, with the same actual generators, is covariant. -/
theorem isInSpanAt_comp_inv_iff {n s : ℕ} {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p)
    (G : Fin s → ComplexModel n → ℂ) (F : ComplexModel n → ℂ) :
    IsInSpanAt (n := n) (· ∈ Set.range G) p F ↔
      IsInSpanAt (n := n) (· ∈ Set.range fun i z => G i (Φ.invFun z))
        (Φ.toFun p) (fun z => F (Φ.invFun z)) := by
  classical
  have hp : Φ.toFun p ∈ Φ.target := Φ.mapsTo_toFun Φ.center_mem_source
  have hto : Tendsto Φ.toFun (𝓝 p) (𝓝 (Φ.toFun p)) :=
    (Φ.toFun_holomorphic.differentiableAt
      (Φ.isOpen_source.mem_nhds Φ.center_mem_source)).continuousAt.tendsto
  constructor
  · intro hspan
    obtain ⟨hF, a, ha, heq⟩ := CoherentIdealColon.isInSpanAt_range_iff.mp hspan
    apply CoherentIdealColon.isInSpanAt_range_iff.mpr
    refine ⟨(holomorphicAt_comp_inv_iff Φ).mpr hF, fun i z => a i (Φ.invFun z),
      fun i => (holomorphicAt_comp_inv_iff Φ).mpr (ha i), ?_⟩
    exact (tendsto_inv Φ).eventually heq
  · intro hspan
    obtain ⟨hF, a, ha, heq⟩ := CoherentIdealColon.isInSpanAt_range_iff.mp hspan
    have hac (i : Fin s) : HolomorphicAt n (fun y => a i (Φ.toFun y)) p := by
      apply (holomorphicAt_comp_inv_iff Φ).mp
      exact (ha i).congr ((show ∀ᶠ z in 𝓝 (Φ.toFun p), z ∈ Φ.target from
        Φ.isOpen_target.mem_nhds hp).mono fun z hz =>
        (congrArg (a i) (Φ.right_inv z hz)).symm)
    apply CoherentIdealColon.isInSpanAt_range_iff.mpr
    refine ⟨(holomorphicAt_comp_inv_iff Φ).mp hF, fun i y => a i (Φ.toFun y), hac, ?_⟩
    filter_upwards [hto.eventually heq, Φ.isOpen_source.mem_nhds Φ.center_mem_source]
      with y hy hys
    simpa only [Φ.left_inv y hys] using hy

end
end Hironaka.LocalHolomorphicFiniteSpanTransport
