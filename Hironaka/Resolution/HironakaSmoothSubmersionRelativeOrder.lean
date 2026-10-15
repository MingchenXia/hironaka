/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOrder

set_option autoImplicit false

/-! # Whole original relative orders under genuine smooth submersions

The actual local section preserves the whole relative point-ideal dictionary
for arbitrary original sets, without a caller order or section certificate.
All natural thresholds, extended orders and entire relative cosupports are
produced internally. General higher invariant and blowup functoriality remain open.
-/

open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothSubmersionRelativeOrder
open Hironaka.HolomorphicIdealSheaves
open HadamardBridge OrderTaylor GermIdealOrder IdealWeightPowers RelativePrincipalizationSpan IdealOrderArithmetic
  OrderInvariance HironakaSmoothSubmersionOrder
noncomputable section

variable {n m : ℕ} {X Y : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

/-- Every actual relative function-order threshold is preserved along the entire preimage set. -/
theorem vanishesToOrderOn_preimage_iff {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
    {N : Set X} {a : X → ℂ} (q : ℕ) :
    VanishesToOrderOn m (f ⁻¹' N) y q (a ∘ f) ↔
      VanishesToOrderOn n N (f y) q a := by
  have hfh : ∀ᶠ w in 𝓝 y, MDifferentiableAt
      𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f w := by
    filter_upwards [hf.domChart.open_source.mem_nhds hf.mem_domChart_source] with w hw
    exact (hf.contMDiffOn.contMDiffAt (hf.domChart.open_source.mem_nhds hw)).mdifferentiableAt
      (by simp)
  obtain ⟨s, hsbase, hsh, hsection⟩ := exists_holomorphic_localSection hf
  constructor
  · rintro ⟨b, hb, heq⟩
    have hb' : (idealPow (pointIdeal m (s (f y))) q).mem (s (f y)) b := by
      simpa only [hsbase] using hb
    refine ⟨b ∘ s, comp_mem_idealPow_pointIdeal hsh q hb', ?_⟩
    have hscont := hsh.self_of_nhds.continuousAt
    have heq' : ∀ᶠ w in 𝓝 (s (f y)), w ∈ f ⁻¹' N → (a ∘ f) w = b w := by
      simpa only [hsbase] using heq
    filter_upwards [hsection, hscont.eventually heq'] with x hx hxeq hxN
    have hsN : s x ∈ f ⁻¹' N := by
      change f (s x) ∈ N
      simpa only [Function.id_def, hx] using hxN
    simpa only [Function.comp_apply, Function.id_def, hx] using hxeq hsN
  · rintro ⟨b, hb, heq⟩
    refine ⟨b ∘ f, comp_mem_idealPow_pointIdeal hfh q hb, ?_⟩
    filter_upwards [hfh.self_of_nhds.continuousAt.eventually heq] with w hw hwN
    exact hw hwN

/-- The original whole relative ideal, with every actual germ member, has exactly the same thresholds. -/
theorem orderGE_preimage_iff {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
    {I : GermIdeal n X} (hI : ∀ a, I.mem (f y) a → HolomorphicAt n a (f y))
    (N : Set X) (q : ℕ) :
    OrderGE m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) y q ↔
      OrderGE n N I (f y) q := by
  have hfh : ∀ᶠ w in 𝓝 y, MDifferentiableAt
      𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f w := by
    filter_upwards [hf.domChart.open_source.mem_nhds hf.mem_domChart_source] with w hw
    exact (hf.contMDiffOn.contMDiffAt (hf.domChart.open_source.mem_nhds hw)).mdifferentiableAt
      (by simp)
  constructor
  · intro h a ha
    have haf : (GermIdeal.pullback (m := m) f I).mem y (a ∘ f) :=
      GermIdeal.mem_pullback_iff.mpr <| isInSpanAt_of_eq_mul ⟨a, ha, rfl⟩
        (holomorphicAt_comp_map hfh (hI a ha)) (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => by simp)
    exact (vanishesToOrderOn_preimage_iff hf q).mp (h (a ∘ f) haf)
  · intro h g hg
    refine IsInSpanAt.vanishesToOrderOn (GermIdeal.mem_pullback_iff.mp hg) ?_
    rintro a ⟨u, hu, rfl⟩
    exact (vanishesToOrderOn_preimage_iff hf q).mpr (h u hu)

/-- Equality of the original extended-natural relative order includes infinite order and arbitrary original sets. -/
theorem order_preimage_eq {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
    {I : GermIdeal n X} (hI : ∀ a, I.mem (f y) a → HolomorphicAt n a (f y)) (N : Set X) :
    order m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) y = order n N I (f y) := by
  have hiff := orderGE_preimage_iff hf hI N
  simp only [order, hiff]

/-- The entire genuine relative marked cosupport is exactly pulled back, without surjectivity. -/
theorem cosupport_preimage_eq {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I : GermIdeal n X} (hI : I.IsCoherent) (N : Set X) (q : ℕ) :
    cosupport m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) q =
      f ⁻¹' cosupport n N I q := by
  ext y
  simp only [cosupport, mem_ofPred_eq, mem_preimage]
  exact and_congr_right fun _ => orderGE_preimage_iff (hf.isSubmersionAt y)
    (fun a ha => GermIdeal.IsCoherent.holomorphicAt_mem hI ha) N q

end
end Hironaka.HironakaSmoothSubmersionRelativeOrder
