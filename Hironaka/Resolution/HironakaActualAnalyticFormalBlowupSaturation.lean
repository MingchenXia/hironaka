/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalColonSaturation
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor

/-! Entire analytic/formal total-ideal and saturation compatibility on the SAME genuine blowup chart. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualAnalyticFormalBlowupSaturation
noncomputable section
open HolGerm HironakaActualOriginalFormalTaylor
  HironakaActualCoefficientPresentationCentrePower HironakaActualTaylorCoordinateNaturality
  HironakaActualAnalyticBlowupTaylor HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalColonSaturation HironakaRelativeNormalCoherentSaturation
  HironakaHolomorphicJetMonomialSpan

private theorem unshiftedTaylor_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

private theorem exists_unshifted_saturation_index (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (a : HolGerm (ComplexModel n)) :
    ∃ N : ℕ,
      (∀ q,N≤q → actualOriginColonChain I a q=actualOriginColonChain I a N) ∧
      (∀ q,N≤q → actualOriginColonChain (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)
        (actualUnshiftedTaylorAlgHom n a) q=
          Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (actualOriginColonChain I a N)) ∧
      ∀ F : MvPowerSeries (Fin n) ℂ,
        (∃ q,F ∈ actualOriginColonChain (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)
          (actualUnshiftedTaylorAlgHom n a) q) ↔
        F ∈ Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (actualOriginColonChain I a N) := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ (J : Ideal (HolGerm (ComplexModel m))) (u : HolGerm (ComplexModel m)),
      ∃ N : ℕ,
        (∀ q,N≤q → actualOriginColonChain J u q=actualOriginColonChain J u N) ∧
        (∀ q,N≤q → actualOriginColonChain (Ideal.map f.toRingHom J) (f u) q=
          Ideal.map f.toRingHom (actualOriginColonChain J u N)) ∧
        ∀ F : MvPowerSeries (Fin n) ℂ,
          (∃ q,F ∈ actualOriginColonChain (Ideal.map f.toRingHom J) (f u) q) ↔
          F ∈ Ideal.map f.toRingHom (actualOriginColonChain J u N)
  have h : P (0+n) (originalTaylorAlgHom n) := exists_actual_original_formal_saturation_index n
  exact unshiftedTaylor_property n P h I a

/-- BOTH whole total-ideal directions follow from the actual entire analytic/formal Taylor square. -/
theorem map_analyticBlowup_totalIdeal (n : ℕ) (A : Set (Fin n)) (e : Fin n)
    (b : Fin n → ℂ) (I : Ideal (HolGerm (ComplexModel n))) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
      (Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom I)=
    Ideal.map (actualFormalBlowup A e b).toRingHom
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) := by
  rw [Ideal.map_map,Ideal.map_map]
  change Ideal.map ((actualUnshiftedTaylorAlgHom n).comp
      (actualAnalyticBlowupPullback A e b)).toRingHom I=
    Ideal.map ((actualFormalBlowup A e b).comp (actualUnshiftedTaylorAlgHom n)).toRingHom I
  rw [actualTaylor_analyticBlowupPullback]

/-- ONE internally chosen true analytic colon computes the ENTIRE formal blowup saturation for EVERY formal member. -/
theorem exists_actual_analytic_formal_blowup_saturation (n : ℕ)
    (A : Set (Fin n)) (e : A) (b : Fin n → ℂ) (I : Ideal (HolGerm (ComplexModel n))) :
    ∃ N : ℕ,
      (∀ q,N≤q → actualOriginColonChain (Ideal.map (actualAnalyticBlowupPullback A e.val b).toRingHom I)
        (coordinateGerm e.val) q=
          actualOriginColonChain (Ideal.map (actualAnalyticBlowupPullback A e.val b).toRingHom I)
            (coordinateGerm e.val) N) ∧
      ∀ F : MvPowerSeries (Fin n) ℂ,
        (∃ q,F ∈ actualOriginColonChain
          (Ideal.map (actualFormalBlowup A e.val b).toRingHom
            (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)) (MvPowerSeries.X e.val) q) ↔
        F ∈ Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
          (actualOriginColonChain (Ideal.map (actualAnalyticBlowupPullback A e.val b).toRingHom I)
            (coordinateGerm e.val) N) := by
  obtain ⟨N,hN,_hFormal,hSat⟩ := exists_unshifted_saturation_index n
    (Ideal.map (actualAnalyticBlowupPullback A e.val b).toRingHom I) (coordinateGerm e.val)
  refine ⟨N,hN,?_⟩
  intro F
  simpa only [map_analyticBlowup_totalIdeal,actualUnshiftedTaylor_coordinate] using hSat F

end
end Hironaka.HironakaActualAnalyticFormalBlowupSaturation
