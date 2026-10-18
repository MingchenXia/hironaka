/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPointBlowupExceptionalLocus
import Hironaka.Resolution.HironakaActualPointGeometricBennett
import Hironaka.Resolution.HironakaActualCoefficientPresentationCentrePower

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNormalBlowupExceptionalLocus
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm OkaRelationSheaf
  HironakaActualAnalyticBlowupTaylor HironakaActualPointBlowupExceptionalLocus
  HironakaActualCoefficientPresentationCentrePower HironakaActualPointGeometricBennett
  HironakaActualPointExceptionalVanishing HironakaActualAnalyticStrictGenerators
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaActualPointInitialIdealInclusion
variable {n : ℕ}

/-- Actual selected normal rows are the true point rows; unselected tangent rows are actual identity rows. -/
theorem mfderiv_actual_selected_blowup_apply (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (z v : ComplexModel n) (i : Fin n) :
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ)
      (mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) (actualAnalyticBlowupMap A e b) z v)=
      if i ∈ A then if i=e then v e else v e*(b i+z i)+z e*v i else v i := by
  rw [mfderiv_eq_fderiv]
  have hchain : HasFDerivAt (fun w : ComplexModel n => actualAnalyticBlowupMap A e b w i)
      ((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).comp
        (fderiv ℂ (actualAnalyticBlowupMap A e b) z)) z :=
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).hasFDerivAt.comp z
      (differentiable_actualAnalyticBlowupMap A e b z).hasFDerivAt
  by_cases hiA : i ∈ A
  · have he : (fun w : ComplexModel n => actualAnalyticBlowupMap A e b w i)=
        (fun w : ComplexModel n => actualAnalyticBlowupMap univ e b w i) := by
      funext w
      simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hiA]
    rw [he] at hchain
    have hpoint : HasFDerivAt (fun w : ComplexModel n => actualAnalyticBlowupMap univ e b w i)
        ((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).comp
          (fderiv ℂ (actualAnalyticBlowupMap univ e b) z)) z :=
      (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).hasFDerivAt.comp z
        (differentiable_actualAnalyticBlowupMap univ e b z).hasFDerivAt
    have hL := hchain.unique hpoint
    have hv := congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L v) hL
    have hp := mfderiv_actual_point_blowup_apply e b z v i
    rw [mfderiv_eq_fderiv] at hp
    rw [if_pos hiA]
    exact hv.trans hp
  · have he : (fun w : ComplexModel n => actualAnalyticBlowupMap A e b w i)=
        (fun w : ComplexModel n => w i) := by
      funext w
      simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hiA]
    rw [he] at hchain
    have hL := hchain.unique (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).hasFDerivAt
    rw [if_neg hiA]
    exact congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L v) hL

/-- A genuine OTHER NORMAL basis vector is killed when the actual exceptional coordinate vanishes. -/
theorem exists_actual_normal_blowup_nonzero_kernel (d t : ℕ) (ht : 2 ≤ t)
    (j : Fin t) (b : Fin (d+t) → ℂ) (z : ComplexModel (d+t)) (hz : z (j.natAdd d)=0) :
    ∃ v : ComplexModel (d+t), v ≠ 0 ∧
      mfderiv 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t))
        (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) z v=0 := by
  let : Nontrivial (Fin t) := Fin.nontrivial_iff_two_le.mpr ht
  obtain ⟨k,hk⟩ := exists_ne j
  have hke : k.natAdd d ≠ j.natAdd d := by
    intro h
    apply hk
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hv
    omega
  let v : ComplexModel (d+t) := PiLp.single 2 (k.natAdd d) 1
  have hve : v (j.natAdd d)=0 := by simp [v,Ne.symm hke]
  have hv : v ≠ 0 := by
    intro h
    have hzero := congrArg (fun w : ComplexModel (d+t) => w (k.natAdd d)) h
    simp [v] at hzero
  refine ⟨v,hv,?_⟩
  rw [mfderiv_eq_fderiv]
  change fderiv ℂ (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) z v=0
  ext i
  have hc := mfderiv_actual_selected_blowup_apply (actualTangentCentreVariables d t)
    (j.natAdd d) b z v i
  rw [mfderiv_eq_fderiv] at hc
  by_cases hiA : i ∈ actualTangentCentreVariables d t
  · simp only [if_pos hiA,hve,hz,zero_mul,add_zero,ite_self] at hc
    exact hc
  · have hine : i ≠ k.natAdd d := by
      intro h
      apply hiA
      rw [h]
      exact ⟨k,rfl⟩
    have hvi : v i=0 := by simp [v,hine]
    simp only [if_neg hiA,hvi] at hc
    exact hc

/-- The ENTIRE actual exceptional hyperplane lies in the original differential-defined exceptional locus. -/
theorem mem_exceptionalLocus_actual_normal_blowup_of_coordinate_eq_zero (d t : ℕ) (ht : 2 ≤ t)
    (j : Fin t) (b : Fin (d+t) → ℂ) (z : ComplexModel (d+t)) (hz : z (j.natAdd d)=0) :
    z ∈ exceptionalLocus (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) := by
  obtain ⟨v,hv,hvzero⟩ := exists_actual_normal_blowup_nonzero_kernel d t ht j b z hz
  intro hbij
  apply hv
  exact hbij.1 (hvzero.trans (map_zero _).symm)

/-- Normal codimension one is the literal identity, independently of total ambient dimension. -/
theorem actual_normal_blowup_one_eq_id (d : ℕ) (j : Fin 1) (b : Fin (d+1) → ℂ) :
    actualAnalyticBlowupMap (actualTangentCentreVariables d 1) (j.natAdd d) b=id := by
  funext z
  ext i
  by_cases hiA : i ∈ actualTangentCentreVariables d 1
  · obtain ⟨k,hk⟩ := hiA
    have hie : i=j.natAdd d := hk.symm.trans (congrArg (Fin.natAdd d) (Subsingleton.elim k j))
    have himem : i ∈ actualTangentCentreVariables d 1 := ⟨k,hk⟩
    simp only [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,if_pos himem,if_pos hie]
    exact congrArg (fun r : Fin (d+1) => z r) hie.symm
  · simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hiA]

theorem exceptionalLocus_actual_normal_blowup_one (d : ℕ) (j : Fin 1) (b : Fin (d+1) → ℂ) :
    exceptionalLocus (d+1) (actualAnalyticBlowupMap (actualTangentCentreVariables d 1) (j.natAdd d) b)=∅ := by
  rw [actual_normal_blowup_one_eq_id]
  ext z
  simp [exceptionalLocus,Function.bijective_id]

/-- For ANY subset the original codimension-one strict transform is its actual closure. -/
theorem strictTransform_actual_normal_blowup_one (d : ℕ) (j : Fin 1) (b : Fin (d+1) → ℂ)
    (W : Set (ComplexModel (d+1))) :
    strictTransform (d+1) (actualAnalyticBlowupMap (actualTangentCentreVariables d 1) (j.natAdd d) b) W=closure W := by
  rw [strictTransform,exceptionalLocus_actual_normal_blowup_one,actual_normal_blowup_one_eq_id,
    sdiff_empty,preimage_id]

/-- The SAME original intrinsic HS is unchanged in actual normal codimension one, for every order. -/
theorem hilbertSamuelAt_actual_normal_blowup_one (d : ℕ) (j : Fin 1) (b : Fin (d+1) → ℂ)
    (W : Set (ComplexModel (d+1))) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := d+1)
      (strictTransform (d+1) (actualAnalyticBlowupMap (actualTangentCentreVariables d 1) (j.natAdd d) b) W)) 0 ℓ=
      hilbertSamuelAt (vanishingIdeal (n := d+1) W) 0 ℓ := by
  rw [strictTransform_actual_normal_blowup_one]
  simp only [hilbertSamuelAt_model_zero,originalVanishingOriginIdeal_closure]

/-- An actual holomorphic map fixing zero and a TRUE product force actual quotient closure vanishing. -/
theorem actual_quotient_zero_on_exceptional_complement_closure
    (W : Set (ComplexModel n)) (π : ComplexModel n → ComplexModel n)
    (hπ : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ π z) (hπ0 : π 0=0)
    (e : Fin n) (q : ℕ) (g H : ComplexModel n → ℂ) (hg : HolAt g 0) (hH : HolAt H 0)
    (hgW : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ W → g z=0)
    (hprod : (coordinateGerm e)^q*HolGerm.mk H hH=compAlgHom π hπ hπ0 (HolGerm.mk g hg)) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ closure (π ⁻¹' W \ {z | z e=0}) → H z=0 := by
  have he : HolAt (fun z : ComplexModel n => z e) 0 :=
    Eventually.of_forall fun _ => (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).differentiableAt
  have hmk : HolGerm.mk (fun z => z e^q*H z)
      (eventually_differentiableAt_mul (eventually_differentiableAt_pow he q) hH)=
        HolGerm.mk (g ∘ π) (holomorphic_comp π hπ hπ0 hg) := by
    rw [HolGerm.mk_mul _ _ (eventually_differentiableAt_pow he q) hH,HolGerm.mk_pow _ he q]
    exact hprod
  have ht : Tendsto π (𝓝 (0 : ComplexModel n)) (𝓝 (0 : ComplexModel n)) := by
    simpa only [hπ0] using hπ.self_of_nhds.continuousAt.tendsto
  have hz : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ π ⁻¹' W \ {z | z e=0} → H z=0 := by
    filter_upwards [HolGerm.mk_eq_mk_iff.mp hmk,ht.eventually hgW] with z hfactor hgz hS
    have hmul : z e^q*H z=0 := hfactor.trans (hgz hS.1)
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero q hS.2)
  exact eventually_zero_on_closure_of_eventually_continuous H _ (hH.mono fun _ h => h.continuousAt) hz

/-- For normal codimension at least two, every ORIGINAL normalized germ vanishes on the genuine geometric strict set. -/
theorem actual_normal_normalized_ideal_le_geometric_strict_vanishing
    (d t : ℕ) (ht : 2 ≤ t) (j : Fin t) (b : Fin (d+t) → ℂ) (W : Set (ComplexModel (d+t))) :
    actualAnalyticNormalizedMemberIdeal (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))
      (actualTangentCentreVariables d t) (j.natAdd d) b ≤
        originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
          (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) := by
  apply Ideal.span_le.mpr
  rintro h ⟨q,g,hgI,_hgp,hprod⟩
  obtain ⟨G,hG,rfl⟩ := HolGerm.exists_eq_mk g
  obtain ⟨H,hH,rfl⟩ := HolGerm.exists_eq_mk h
  apply (mk_mem_original_vanishing_origin_ideal_iff _ H hH).mpr
  have hπ : ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)),
      DifferentiableAt ℂ (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) z :=
    Eventually.of_forall fun _ =>
      (differentiable_actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b).differentiableAt
  have hz := actual_quotient_zero_on_exceptional_complement_closure W _ hπ
    (actualAnalyticBlowupMap_zero (actualTangentCentreVariables d t) (j.natAdd d) b)
    (j.natAdd d) q G H hG hH ((mk_mem_original_vanishing_origin_ideal_iff W G hG).mp hgI) hprod
  have hsets : ((actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) ⁻¹' W \
      exceptionalLocus (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)) ⊆
      ((actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) ⁻¹' W \ {z | z (j.natAdd d)=0}) := by
    intro y hy
    exact ⟨hy.1,fun hye => hy.2
      (mem_exceptionalLocus_actual_normal_blowup_of_coordinate_eq_zero d t ht j b y hye)⟩
  filter_upwards [hz] with z hzero hstrict
  exact hzero (closure_mono hsets hstrict)

/-- Every original intrinsic geometric HS value is bounded by the SAME original normalized-ideal value. -/
theorem hilbertSamuelAt_actual_normal_strict_le_normalized
    (d t : ℕ) (ht : 2 ≤ t) (j : Fin t) (b : Fin (d+t) → ℂ) (W : Set (ComplexModel (d+t))) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := d+t)
        (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) 0 ℓ ≤
      hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal
        (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)) (actualTangentCentreVariables d t) (j.natAdd d) b) ℓ := by
  rw [hilbertSamuelAt_model_zero]
  exact hilbertSamuelValue_antitone_original_ideal _ _
    (actual_normal_normalized_ideal_le_geometric_strict_vanishing d t ht j b W) ℓ

end
end Hironaka.HironakaActualNormalBlowupExceptionalLocus
