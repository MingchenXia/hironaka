/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualStrictExceptionalRegularity
import Hironaka.Analytic.RueckertNullstellensatz
import Hironaka.Analytic.AnalyticDescendingChain
/-!
# The whole geometric strict ideal is the radical exceptional saturation

The genuine actual coordinate differential is invertible off the exceptional
hyperplane, giving the exact original differential exceptional locus. Genuine
analytic Nullstellensatz then identifies the WHOLE original strict vanishing
germ ideal with the radical-colon of the WHOLE actual total pullback ideal.
For an arbitrary original analytic subset its finite local presentation is
constructed internally; no presentation, radicality or strict-ideal certificate
is supplied. The radical is retained, and neither normalized-ideal equality nor
Hilbert--Samuel persistence is inferred.

Blueprint: `hironaka-actual-strict-radical-pullback-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualStrictRadicalPullback
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm OkaRelationSheaf
  HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalDeformationInitialRelations
  HironakaActualPointGeometricBennett HironakaActualPointExceptionalVanishing
  HironakaActualNormalBlowupExceptionalLocus HironakaActualAnalyticBlowupTaylor
  HironakaActualCoefficientPresentationCentrePower HironakaHolomorphicJetChartInvariance
variable {n : ℕ}

/-- The genuine differential has an explicit row inverse at every point off the exceptional coordinate. -/
theorem mfderiv_actual_selected_blowup_bijective_of_coordinate_ne_zero
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (z : ComplexModel n) (hz : z e≠0) :
    Function.Bijective (mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n)
      (actualAnalyticBlowupMap A e b) z) := by
  rw [mfderiv_eq_fderiv]
  change Function.Bijective (fun v : ComplexModel n => fderiv ℂ (actualAnalyticBlowupMap A e b) z v)
  let L := fderiv ℂ (actualAnalyticBlowupMap A e b) z
  have row (v : ComplexModel n) (i : Fin n) :
      L v i = if i∈A then if i=e then v e else v e*(b i+z i)+z e*v i else v i :=
    by
      have h := mfderiv_actual_selected_blowup_apply A e b z v i
      rw [mfderiv_eq_fderiv] at h
      exact h
  have rowe (v : ComplexModel n) : L v e=v e := by simp [row]
  constructor
  · intro u v huv
    change L u=L v at huv
    have he : u e=v e := by simpa only [rowe] using congrArg (fun w : ComplexModel n => w e) huv
    ext i
    have hi := congrArg (fun w : ComplexModel n => w i) huv
    rw [row,row] at hi
    by_cases hiA : i∈A
    · by_cases hie : i=e
      · exact hie ▸ he
      · simp only [if_pos hiA,if_neg hie,he] at hi
        exact mul_left_cancel₀ hz (add_left_cancel hi)
    · simpa only [if_neg hiA] using hi
  · intro w
    let v : ComplexModel n := WithLp.toLp 2 (fun i => if i=e then w e else
      if i∈A then (w i-w e*(b i+z i))/(z e) else w i)
    refine ⟨v,?_⟩
    ext i
    rw [row]
    have ve : v e=w e := by simp [v]
    by_cases hiA : i∈A
    · by_cases hie : i=e
      · simp only [if_pos hiA,if_pos hie,ve]
        exact congrArg w hie.symm
      · simp only [if_pos hiA,if_neg hie,ve]
        have vi : v i=(w i-w e*(b i+z i))/(z e) := by simp [v,hie,hiA]
        rw [vi]
        field_simp
        ring
    · simp only [if_neg hiA]
      by_cases hie : i=e
      · simpa only [hie] using ve
      · simp [v,hie,hiA]

/-- The ENTIRE actual differential exceptional locus equals the actual coordinate hyperplane. -/
theorem exceptionalLocus_actual_normal_blowup_eq (d t : ℕ) (ht : 2≤t)
    (j : Fin t) (b : Fin (d+t) → ℂ) :
    exceptionalLocus (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)=
      {z : ComplexModel (d+t) | z (j.natAdd d)=0} := by
  ext z
  constructor
  · intro hz
    by_contra hne
    exact hz (mfderiv_actual_selected_blowup_bijective_of_coordinate_ne_zero _ _ _ z hne)
  · exact mem_exceptionalLocus_actual_normal_blowup_of_coordinate_eq_zero d t ht j b z

/-- Actual finite equations and genuine analytic Nullstellensatz identify the WHOLE strict zero-locus ideal. -/
theorem original_closure_zero_locus_diff_ideal_eq_radical_colon {s : ℕ}
    (F : Fin s → ComplexModel n → ℂ) (hF : ∀ i,HolAt (F i) 0) (e : Fin n) :
    originalCoherentOriginIdeal (vanishingIdeal (n := n)
      (closure ({z | ∀ i,F i z=0} \ {z : ComplexModel n | z e=0})))=
      (Ideal.span (range fun i => HolGerm.mk (F i) (hF i))).radical.colon {coordinateGerm e} := by
  let Z : Set (ComplexModel n) := {z | ∀ i,F i z=0}
  let K := Ideal.span (range fun i => HolGerm.mk (F i) (hF i))
  have hK : K≤AnalyticGermDecomposition.vanishingIdeal Z := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr (Eventually.of_forall fun z hz => hz i)
  ext g
  obtain ⟨G,hG,rfl⟩ := HolGerm.exists_eq_mk g
  have he : HolAt (fun z : ComplexModel n => z e) 0 :=
    Eventually.of_forall fun _ => (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).differentiableAt
  have hp := eventually_differentiableAt_mul he hG
  have hmk : HolGerm.mk (fun z : ComplexModel n => z e*G z) hp=
      coordinateGerm e*HolGerm.mk G hG := by
    rw [HolGerm.mk_mul _ _ he hG]
    rfl
  rw [Submodule.mem_colon_singleton,smul_eq_mul,mul_comm]
  constructor
  · intro hg
    apply RueckertNullstellensatz.vanishingIdeal_le_radical K F
      (fun i => ⟨hF i,Ideal.subset_span ⟨i,rfl⟩⟩)
    rw [← hmk]
    apply AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
    have hz := (mk_mem_original_vanishing_origin_ideal_iff _ G hG).mp hg
    filter_upwards [hz] with z hz hzF
    by_cases hze : z e=0
    · rw [hze,zero_mul]
    · rw [hz (subset_closure ⟨hzF,hze⟩),mul_zero]
  · intro hg
    obtain ⟨N,hN⟩ := Ideal.mem_radical_iff.mp hg
    have hpow : HolGerm.mk (fun z : ComplexModel n => (z e*G z)^N)
        (eventually_differentiableAt_pow hp N)∈AnalyticGermDecomposition.vanishingIdeal Z := by
      rw [HolGerm.mk_pow _ hp N,hmk]
      exact hK hN
    have hz := AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp hpow
    have hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel n),z∈Z\{z : ComplexModel n | z e=0}→G z=0 := by
      filter_upwards [hz] with z hz hzS
      exact (mul_eq_zero.mp (pow_eq_zero_iff'.mp (hz hzS.1)).1).resolve_left hzS.2
    exact (mk_mem_original_vanishing_origin_ideal_iff _ G hG).mpr
      (eventually_zero_on_closure_of_eventually_continuous G _ (hG.mono fun _ h => h.continuousAt) hzero)

/-- The whole genuine geometric strict ideal is the radical-colon of the literal actual pullback ideal. -/
theorem original_strict_zero_locus_ideal_eq_radical_pullback_colon (d t : ℕ) (ht : 2≤t)
    (j : Fin t) (b : Fin (d+t) → ℂ) {s : ℕ}
    (F : Fin s → ComplexModel (d+t) → ℂ) (hF : ∀ i,HolAt (F i) 0) :
    originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)
        {z | ∀ i,F i z=0}))=
      (Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b).toRingHom
        (Ideal.span (range fun i => HolGerm.mk (F i) (hF i)))).radical.colon {coordinateGerm (j.natAdd d)} := by
  let π := actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b
  have hπ : ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)),DifferentiableAt ℂ π z :=
    Eventually.of_forall fun z => (differentiable_actualAnalyticBlowupMap _ _ _ z)
  have hπ0 : π 0=0 := actualAnalyticBlowupMap_zero _ _ _
  have hc (i : Fin s) : HolAt (F i ∘ π) 0 := holomorphic_comp π hπ hπ0 (hF i)
  have h := original_closure_zero_locus_diff_ideal_eq_radical_colon (fun i => F i ∘ π) hc (j.natAdd d)
  rw [strictTransform,exceptionalLocus_actual_normal_blowup_eq d t ht j b]
  change originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
    (closure ({z | ∀ i,(F i ∘ π) z=0}\{z : ComplexModel (d+t) | z (j.natAdd d)=0})))=_
  rw [h,Ideal.map_span,← Set.range_comp]
  congr 3

private theorem original_vanishing_eq_germ_vanishing (W : Set (ComplexModel n)) :
    originalCoherentOriginIdeal (vanishingIdeal (n := n) W)=AnalyticGermDecomposition.vanishingIdeal W := by
  ext g
  obtain ⟨G,hG,rfl⟩ := HolGerm.exists_eq_mk g
  rw [mk_mem_original_vanishing_origin_ideal_iff,AnalyticGermDecomposition.mem_vanishingIdeal_mk]

private theorem original_zero_locus_ideal_eq_radical_span {s : ℕ}
    (F : Fin s → ComplexModel n → ℂ) (hF : ∀ i,HolAt (F i) 0) :
    originalCoherentOriginIdeal (vanishingIdeal (n := n) {z | ∀ i,F i z=0})=
      (Ideal.span (range fun i => HolGerm.mk (F i) (hF i))).radical := by
  rw [original_vanishing_eq_germ_vanishing]
  let K := Ideal.span (range fun i => HolGerm.mk (F i) (hF i))
  have hK : K≤AnalyticGermDecomposition.vanishingIdeal {z | ∀ i,F i z=0} := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr (Eventually.of_forall fun z hz => hz i)
  apply le_antisymm
  · exact RueckertNullstellensatz.vanishingIdeal_le_radical K F
      (fun i => ⟨hF i,Ideal.subset_span ⟨i,rfl⟩⟩)
  · intro g hg
    obtain ⟨N,hN⟩ := Ideal.mem_radical_iff.mp hg
    obtain ⟨G,hG,rfl⟩ := HolGerm.exists_eq_mk g
    have hpow : HolGerm.mk (fun z : ComplexModel n => G z^N)
        (eventually_differentiableAt_pow hG N)∈AnalyticGermDecomposition.vanishingIdeal {z | ∀ i,F i z=0} := by
      rw [HolGerm.mk_pow G hG N]
      exact hK hN
    apply AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
    filter_upwards [AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp hpow] with z hz hzF
    exact (pow_eq_zero_iff'.mp (hz hzF)).1

private theorem radical_map_radical {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (K : Ideal R) : (Ideal.map f K.radical).radical=(Ideal.map f K).radical := by
  apply le_antisymm
  · simpa only [Ideal.radical_idem] using Ideal.radical_mono (Ideal.map_radical_le f (I := K))
  · exact Ideal.radical_mono (Ideal.map_mono Ideal.le_radical)

/-- Original analyticity internally chooses a genuine finite local presentation of the SAME whole source ideal. -/
theorem original_analytic_strict_ideal_eq_radical_pullback_colon (d t : ℕ) (ht : 2≤t)
    (j : Fin t) (b : Fin (d+t) → ℂ) (W : Set (ComplexModel (d+t)))
    (hW : IsComplexAnalyticSubset (n := d+t) W) :
    originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W))=
      (Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b).toRingHom
        (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))).radical.colon {coordinateGerm (j.natAdd d)} := by
  have hag : AnalyticGermDecomposition.IsAnalyticGerm W := by
    simpa [AnalyticDescendingChain.chartGerm,complexChartAt,chartAt_self_eq] using
      AnalyticDescendingChain.isAnalyticGerm_chartGerm hW (0 : ComplexModel (d+t))
  obtain ⟨s,F,hF,hWF⟩ := hag
  have hsource : originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)=
      (Ideal.span (range fun i => HolGerm.mk (F i) (hF i))).radical := by
    calc
      _=AnalyticGermDecomposition.vanishingIdeal W := original_vanishing_eq_germ_vanishing W
      _=AnalyticGermDecomposition.vanishingIdeal {z | ∀ i,F i z=0} :=
        AnalyticGermDecomposition.vanishingIdeal_congr (eventuallyEq_set.mpr hWF)
      _=originalCoherentOriginIdeal (vanishingIdeal (n := d+t) {z | ∀ i,F i z=0}) :=
        (original_vanishing_eq_germ_vanishing _).symm
      _=_ := original_zero_locus_ideal_eq_radical_span F hF
  let π := actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b
  have htπ : Tendsto π (𝓝 (0 : ComplexModel (d+t))) (𝓝 (0 : ComplexModel (d+t))) := by
    simpa only [π,actualAnalyticBlowupMap_zero] using
      (differentiable_actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b).continuous.tendsto 0
  have htarget : originalCoherentOriginIdeal (vanishingIdeal (n := d+t) (strictTransform (d+t) π W))=
      originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
        (strictTransform (d+t) π {z | ∀ i,F i z=0})) := by
    rw [strictTransform,strictTransform,originalVanishingOriginIdeal_closure,
      originalVanishingOriginIdeal_closure,original_vanishing_eq_germ_vanishing,
      original_vanishing_eq_germ_vanishing]
    apply AnalyticGermDecomposition.vanishingIdeal_congr
    apply eventuallyEq_set.mpr
    filter_upwards [htπ.eventually hWF] with z hz
    exact and_congr hz Iff.rfl
  rw [htarget,original_strict_zero_locus_ideal_eq_radical_pullback_colon d t ht j b F hF,hsource,
    radical_map_radical]

end
end Hironaka.HironakaActualStrictRadicalPullback
