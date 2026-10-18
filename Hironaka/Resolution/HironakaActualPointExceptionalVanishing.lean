/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPointNormalizedBennett
import Hironaka.Resolution.HironakaRelativeNormalDeformationInitialRelations
import Hironaka.Coherence.CartanIrreducible

/-! Actual normalized analytic members vanish on the true exceptional-complement closure. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualPointExceptionalVanishing
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalDeformationInitialRelations HironakaActualAnalyticBlowupTaylor
  HironakaActualAnalyticStrictGenerators HironakaActualPointInitialIdealInclusion HironakaActualPointNormalizedBennett
variable {n : ℕ}

/-- Actual local continuity carries vanishing on a set to vanishing on its entire closure germ. -/
theorem eventually_zero_on_closure_of_eventually_continuous (f : ComplexModel n → ℂ)
    (S : Set (ComplexModel n)) (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ContinuousAt f z)
    (hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ S → f z=0) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ closure S → f z=0 := by
  obtain ⟨U,hUS,hU,h0U⟩ := eventually_nhds_iff.mp (hf.and hzero)
  filter_upwards [hU.mem_nhds h0U] with z hz hcl
  by_contra hne
  have hUz : ∀ᶠ w in 𝓝 z, w ∈ U := hU.mem_nhds hz
  obtain ⟨w,hw⟩ := ((mem_closure_iff_frequently.mp hcl).and_eventually
    (hUz.and ((hUS z hz).1.eventually_ne hne))).exists
  exact hw.2.2 ((hUS w hw.2.1).2 hw.1)

/-- The true analytic exceptional product forces original quotient vanishing on the genuine closure. -/
theorem actual_point_quotient_zero_on_exceptional_complement_closure
    (A : Set (ComplexModel n)) (e : Fin n) (b : Fin n → ℂ) (d : ℕ)
    (g H : ComplexModel n → ℂ) (hg : HolAt g 0) (hH : HolAt H 0)
    (hgA : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ A → g z=0)
    (hprod : (coordinateGerm e)^d*HolGerm.mk H hH=
      actualAnalyticBlowupPullback Set.univ e b (HolGerm.mk g hg)) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      z ∈ closure ((actualAnalyticBlowupMap Set.univ e b) ⁻¹' A \ {z | z e=0}) → H z=0 := by
  let π := actualAnalyticBlowupMap Set.univ e b
  have hp : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ π z :=
    Eventually.of_forall fun _ => (differentiable_actualAnalyticBlowupMap Set.univ e b).differentiableAt
  have hπ0 : π 0=0 := actualAnalyticBlowupMap_zero Set.univ e b
  have he : HolAt (fun z : ComplexModel n => z e) 0 :=
    Eventually.of_forall fun _ => (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).differentiableAt
  have hmk : HolGerm.mk (fun z => z e^d*H z)
      (eventually_differentiableAt_mul (eventually_differentiableAt_pow he d) hH)=
        HolGerm.mk (g ∘ π) (holomorphic_comp π hp hπ0 hg) := by
    rw [HolGerm.mk_mul _ _ (eventually_differentiableAt_pow he d) hH,HolGerm.mk_pow _ he d]
    exact hprod
  have ht : Tendsto π (𝓝 (0 : ComplexModel n)) (𝓝 (0 : ComplexModel n)) := by
    have hc : Continuous π := (differentiable_actualAnalyticBlowupMap Set.univ e b).continuous
    simpa only [hπ0] using hc.tendsto (0 : ComplexModel n)
  have hz : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      z ∈ π ⁻¹' A \ {z | z e=0} → H z=0 := by
    filter_upwards [HolGerm.mk_eq_mk_iff.mp hmk,ht.eventually hgA] with z hfactor hgz hS
    have hne : z e ≠ 0 := hS.2
    have hmul : z e^d*H z=0 := hfactor.trans (hgz hS.1)
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero d hne)
  exact eventually_zero_on_closure_of_eventually_continuous H _
    (hH.mono fun _ h => h.continuousAt) hz

/-- Every defining actual normalized germ belongs to the original whole target closure vanishing ideal. -/
theorem actual_point_normalized_ideal_le_exceptional_complement_closure_vanishing
    (A : Set (ComplexModel n)) (hA : IsComplexAnalyticSubset (n := n) A) (e : Fin n) (b : Fin n → ℂ) :
    actualAnalyticNormalizedMemberIdeal (originalCoherentOriginIdeal (vanishingIdeal (n := n) A)) Set.univ e b ≤
      originalCoherentOriginIdeal (vanishingIdeal (n := n)
        (closure ((actualAnalyticBlowupMap Set.univ e b) ⁻¹' A \ {z | z e=0}))) := by
  apply Ideal.span_le.mpr
  rintro h ⟨d,g,hgI,_hgp,hprod⟩
  obtain ⟨G,hG,rfl⟩ := HolGerm.exists_eq_mk g
  obtain ⟨H,hH,rfl⟩ := HolGerm.exists_eq_mk h
  have hGA := (mk_mem_originalCoherentOriginIdeal_iff (vanishingIdeal (n := n) A)
    (CartanIrreducible.cartanCoherence A hA) hG).mp hgI
  apply Ideal.subset_span
  exact ⟨H,hH,⟨hH.mono fun _ h => h.mdifferentiableAt,
    actual_point_quotient_zero_on_exceptional_complement_closure A e b d G H hG hH hGA.2 hprod⟩,rfl⟩

/-- Every actual closure value is bounded by the original analytic vanishing origin-ideal value. -/
theorem hilbertSamuelValue_actual_point_exceptional_complement_closure_le
    (A : Set (ComplexModel n)) (hA : IsComplexAnalyticSubset (n := n) A)
    (e : Fin n) (b : Fin n → ℂ) (ℓ : ℕ) :
    hilbertSamuelValue (originalCoherentOriginIdeal (vanishingIdeal (n := n)
        (closure ((actualAnalyticBlowupMap Set.univ e b) ⁻¹' A \ {z | z e=0})))) ℓ ≤
      hilbertSamuelValue (originalCoherentOriginIdeal (vanishingIdeal (n := n) A)) ℓ :=
  (hilbertSamuelValue_antitone_original_ideal _ _
    (actual_point_normalized_ideal_le_exceptional_complement_closure_vanishing A hA e b) ℓ).trans
      (hilbertSamuelValue_actual_point_normalized_le_original n _ e b ℓ)

end
end Hironaka.HironakaActualPointExceptionalVanishing
