import Hironaka.Coherence.CoherentIdealFiniteSpan
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Coherence.CoherentIdealColon
import Hironaka.Analytic.HolomorphicGermRing
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false

/-! # Literal finite holomorphic spans and the actual Euclidean holomorphic-germ ring -/

open Set Filter
open scoped Topology Manifold

namespace Hironaka.EuclideanHolomorphicGermSpan

open Hironaka.HolomorphicIdealSheaves

open Hironaka

noncomputable section

private theorem mk_sum_mul {n s : ℕ}
    (a G : Fin s → ComplexModel n → ℂ)
    (ha : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (a i) z)
    (hG : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G i) z) :
    HolGerm.mk (fun z => ∑ i : Fin s, a i z * G i z)
        (eventually_differentiableAt_sum Finset.univ
          (fun i => eventually_differentiableAt_mul (ha i) (hG i))) =
      ∑ i : Fin s, HolGerm.mk (a i) (ha i) * HolGerm.mk (G i) (hG i) := by
  rw [HolGerm.mk_sum Finset.univ (fun i z => a i z * G i z)
    (fun i => eventually_differentiableAt_mul (ha i) (hG i))]
  exact Finset.sum_congr rfl fun i _ => HolGerm.mk_mul (a i) (G i) (ha i) (hG i)

/-- The two full finite-span encodings agree for the literal Euclidean functions. -/
theorem isInSpanAt_iff_holGerm_mem_span {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G i) z)
    {F : ComplexModel n → ℂ} (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) :
    IsInSpanAt (n := n) (· ∈ Set.range G) (0 : ComplexModel n) F ↔
      HolGerm.mk F hF ∈ Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) := by
  classical
  have hFm : HolomorphicAt n F 0 := hF.mono fun _ hz => hz.mdifferentiableAt
  constructor
  · intro hspan
    obtain ⟨_, a, ha, heq⟩ := CoherentIdealColon.isInSpanAt_range_iff.mp hspan
    have hac (i : Fin s) : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (a i) z :=
      (ha i).mono fun _ hz => hz.differentiableAt
    have hsum := eventually_differentiableAt_sum Finset.univ
      (fun i => eventually_differentiableAt_mul (hac i) (hG i))
    have hmk : HolGerm.mk F hF = ∑ i, HolGerm.mk (a i) (hac i) *
        HolGerm.mk (G i) (hG i) := by
      calc
        HolGerm.mk F hF = HolGerm.mk (fun z => ∑ i, a i z * G i z) hsum :=
          HolGerm.mk_eq_mk_iff.mpr heq
        _ = _ := mk_sum_mul a G hac hG
    rw [hmk]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _
      (Ideal.subset_span ⟨i, rfl⟩)
  · intro hmem
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
    choose a ha hca using fun i : Fin s => HolGerm.exists_eq_mk (c i)
    have hc' : (∑ i : Fin s, c i * HolGerm.mk (G i) (hG i)) = HolGerm.mk F hF := by
      rw [c.sum_fintype (fun i b => b • HolGerm.mk (G i) (hG i))
        (fun _ => zero_smul _ _)] at hc
      simpa only [smul_eq_mul] using hc
    have hsum := eventually_differentiableAt_sum Finset.univ
      (fun i => eventually_differentiableAt_mul (ha i) (hG i))
    have heq : F =ᶠ[𝓝 (0 : ComplexModel n)] fun z => ∑ i, a i z * G i z := by
      apply HolGerm.mk_eq_mk_iff.mp (show HolGerm.mk F hF =
        HolGerm.mk (fun z => ∑ i, a i z * G i z) hsum from ?_)
      rw [mk_sum_mul a G ha hG]
      simpa only [hca] using hc'.symm
    apply CoherentIdealColon.isInSpanAt_range_iff.mpr
    exact ⟨hFm, a, fun i => (ha i).mono fun _ hz => hz.mdifferentiableAt, heq⟩

end
end Hironaka.EuclideanHolomorphicGermSpan
