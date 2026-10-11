/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Geometry.Manifold.Submersion
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Hironaka.Analytic.OrderInvariance

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSmoothSubmersionOrder

open Hironaka.HolomorphicIdealSheaves
open HadamardBridge GermIdealOrder OrderTaylor IdealWeightPowers
  RelativePrincipalizationSpan IdealOrderArithmetic

open Hironaka

noncomputable section

variable {n m : ℕ} {X Y : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

omit [IsComplexManifold n X] [IsComplexManifold m Y] in
/-- The genuine submersion charts produce a local holomorphic right inverse through the original point. -/
theorem exists_holomorphic_localSection {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y) :
    ∃ s : X → Y, s (f y) = y ∧
      (∀ᶠ z in 𝓝 (f y), MDifferentiableAt
        𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) s z) ∧
      (fun z => f (s z)) =ᶠ[𝓝 (f y)] id := by
  let φ := hf.domChart
  let ψ := hf.codChart
  let L := hf.equiv
  have hy : y ∈ φ.source := hf.mem_domChart_source
  have hfy : f y ∈ ψ.source := hf.mem_codChart_source
  have hchart : ∀ z ∈ φ.target, ψ (f (φ.symm z)) = (L z).1 := by
    simpa [Set.EqOn, φ, ψ, L, Function.comp_def] using hf.writtenInCharts
  let v := (L (φ y)).2
  let b : X → ComplexModel m := fun z => L.symm (ψ z, v)
  let s : X → Y := fun z => φ.symm (b z)
  have hbase : ψ (f y) = (L (φ y)).1 := by
    simpa only [φ.left_inv hy] using hchart (φ y) (φ.map_source hy)
  have hby : b (f y) = φ y := by
    apply L.injective
    change L (L.symm (ψ (f y), v)) = L (φ y)
    rw [L.apply_symm_apply]
    exact Prod.ext hbase rfl
  have hsbase : s (f y) = y := by
    change φ.symm (b (f y)) = y
    rw [hby, φ.left_inv hy]
  have hψ : ContinuousAt ψ (f y) := ψ.continuousAt hfy
  have hb : ContinuousAt b (f y) :=
    L.symm.continuous.continuousAt.comp (hψ.prodMk continuousAt_const)
  have hψnear : ∀ᶠ z in 𝓝 (f y), z ∈ ψ.source := ψ.open_source.mem_nhds hfy
  have hnear : ∀ᶠ z in 𝓝 (f y), z ∈ ψ.source ∧ b z ∈ φ.target :=
    hψnear.and
      (hb.eventually (φ.open_target.mem_nhds (hby ▸ φ.map_source hy)))
  refine ⟨s, hsbase, ?_, ?_⟩
  · filter_upwards [hnear] with z hz
    have hψhol :=
      (contMDiffAt_of_mem_maximalAtlas hf.codChart_mem_maximalAtlas hz.1).mdifferentiableAt
        (by simp)
    have hslice : Differentiable ℂ
        (fun u : ComplexModel n => L.symm (u, v)) :=
      L.symm.differentiable.comp (differentiable_id.prodMk (differentiable_const v))
    have hbhol : MDifferentiableAt 𝓘(ℂ, ComplexModel n)
        𝓘(ℂ, ComplexModel m) b z := hslice.comp_mdifferentiableAt hψhol
    have hφhol :=
      (contMDiffAt_symm_of_mem_maximalAtlas hf.domChart_mem_maximalAtlas hz.2).mdifferentiableAt
        (by simp)
    exact hφhol.comp z hbhol
  · filter_upwards [hnear] with z hz
    have hsφ : s z ∈ φ.source := φ.map_target hz.2
    have hfsψ : f (s z) ∈ ψ.source := hf.source_subset_preimage_source hsφ
    apply ψ.injOn hfsψ hz.1
    have heq := hchart (b z) hz.2
    simpa [s, b] using heq

/-- Every natural point-ideal order threshold of the original full germ ideal is preserved by a holomorphic submersion. -/
theorem orderGE_pullback_iff {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
    {I : GermIdeal n X} (hI : ∀ a, I.mem (f y) a → HolomorphicAt n a (f y)) (q : ℕ) :
    OrderGE m univ (GermIdeal.pullback (m := m) f I) y q ↔
      OrderGE n univ I (f y) q := by
  have hfh : ∀ᶠ w in 𝓝 y, MDifferentiableAt
      𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f w := by
    filter_upwards [hf.domChart.open_source.mem_nhds hf.mem_domChart_source] with w hw
    exact (hf.contMDiffOn.contMDiffAt (hf.domChart.open_source.mem_nhds hw)).mdifferentiableAt
      (by simp)
  obtain ⟨s, hsbase, hsh, hsection⟩ := exists_holomorphic_localSection hf
  constructor
  · intro h a ha
    have haf : (GermIdeal.pullback (m := m) f I).mem y (a ∘ f) :=
      GermIdeal.mem_pullback_iff.mpr <| isInSpanAt_of_eq_mul ⟨a, ha, rfl⟩
        (holomorphicAt_comp_map hfh (hI a ha)) (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => by simp)
    have hpow := mem_idealPow_of_vanishesToOrderOn_univ (h (a ∘ f) haf)
    have hpow' : (idealPow (pointIdeal m (s (f y))) q).mem (s (f y)) (a ∘ f) := by
      simpa only [hsbase] using hpow
    have hback := comp_mem_idealPow_pointIdeal (φ := s) (u := f y) hsh q hpow'
    refine ⟨a, mem_idealPow_congr hback ?_, Eventually.of_forall fun _ _ => rfl⟩
    exact hsection.mono fun z hz => congrArg a hz
  · intro h g hg
    refine IsInSpanAt.vanishesToOrderOn (GermIdeal.mem_pullback_iff.mp hg) ?_
    rintro a ⟨u, hu, rfl⟩
    exact ⟨u ∘ f, comp_mem_idealPow_pointIdeal hfh q
      (mem_idealPow_of_vanishesToOrderOn_univ (h u hu)),
      Eventually.of_forall fun _ _ => rfl⟩

/-- The actual extended-natural ideal order is invariant under a holomorphic submersion, including infinite order. -/
theorem order_pullback_eq {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
    {I : GermIdeal n X} (hI : ∀ a, I.mem (f y) a → HolomorphicAt n a (f y)) :
    order m univ (GermIdeal.pullback (m := m) f I) y = order n univ I (f y) := by
  have hiff := orderGE_pullback_iff hf hI
  simp only [order, hiff]

/-- The actual marked cosupport pulls back exactly under a holomorphic submersion. -/
theorem cosupport_pullback_eq {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I : GermIdeal n X} (hI : I.IsCoherent) (q : ℕ) :
    cosupport m univ (GermIdeal.pullback (m := m) f I) q =
      f ⁻¹' cosupport n univ I q := by
  ext y
  simpa only [cosupport, mem_ofPred_eq, mem_univ, true_and, mem_preimage] using
    orderGE_pullback_iff (hf.isSubmersionAt y)
      (fun a ha => GermIdeal.IsCoherent.holomorphicAt_mem hI ha) q

end
end Hironaka.HironakaSmoothSubmersionOrder
