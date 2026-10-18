/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPointDehomogenizedInitial
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor
import Hironaka.Resolution.HironakaActualFormalIdealContraction

/-! Genuine exceptional initial restrictions are retained in the WHOLE original analytic germ ring. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualAnalyticPointInitialRestriction
noncomputable section
open HolGerm HironakaHolomorphicJetMonomialSpan HironakaActualOriginalFormalTaylor
  HironakaActualFormalIdealContraction HironakaActualCoefficientPresentationCentrePower
  HironakaActualAnalyticBlowupTaylor HironakaActualFormalBlowupMemberGeneration
  HironakaActualPointExceptionalInitialForm HironakaActualPointDehomogenizedInitial

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

private theorem mem_analytic_ideal_iff_unshifted_extension (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (g : HolGerm (ComplexModel n)) :
    g ∈ I ↔ actualUnshiftedTaylorAlgHom n g ∈ I.map (actualUnshiftedTaylorAlgHom n).toRingHom := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ (I : Ideal (HolGerm (ComplexModel m))) (g : HolGerm (ComplexModel m)), g ∈ I ↔ f g ∈ I.map f.toRingHom
  exact unshiftedTaylor_property n P (mem_original_ideal_iff_formal_extension n) I g

/-- Actual finite original polynomial evaluation retains the ENTIRE same formal polynomial inclusion. -/
theorem actualTaylor_polynomial_coordinate_evaluation (n : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    actualUnshiftedTaylorAlgHom n (MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n)) P)=
      (P : MvPowerSeries (Fin n) ℂ) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [MvPolynomial.aeval_C,AlgHom.commutes,MvPolynomial.coe_C,MvPowerSeries.c_eq_algebraMap]
  | add P Q hP hQ => rw [map_add,map_add,hP,hQ,MvPolynomial.coe_add]
  | mul_X P i hP =>
      rw [map_mul,map_mul,hP,MvPolynomial.aeval_X,actualUnshiftedTaylor_coordinate,
        MvPolynomial.coe_mul,MvPolynomial.coe_X]

/-- Genuine analytic exceptional product identities retain the WHOLE original analytic initial restriction. -/
theorem actual_analytic_point_quotient_initial_restriction (n : ℕ) (e : Fin n) (b : Fin n → ℂ)
    (d : ℕ) (g H : HolGerm (ComplexModel n)) (hg : g ∈ actualAnalyticCoordinateIdeal Set.univ ^ d)
    (hH : (coordinateGerm e)^d*H=actualAnalyticBlowupPullback Set.univ e b g) :
    H-MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))
      (actualPointDehomogenization e b (actualPointHomogeneousPolynomial d (actualUnshiftedTaylorAlgHom n g))) ∈
        Ideal.span {coordinateGerm e} := by
  have hgT := actualTaylor_mem_coordinateCentre_pow Set.univ d g hg
  have hn : actualUnshiftedTaylorAlgHom n H=actualNormalizedFormalMember Set.univ e (mem_univ e) b d
      (actualUnshiftedTaylorAlgHom n g) hgT := by
    apply actualNormalizedFormalMember_unique
    have ht := congrArg (actualUnshiftedTaylorAlgHom n) hH
    rw [map_mul,map_pow,actualUnshiftedTaylor_coordinate] at ht
    exact ht.trans (DFunLike.congr_fun (actualTaylor_analyticBlowupPullback Set.univ e b) g)
  have hmap : Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
      (Ideal.span {coordinateGerm e})=Ideal.span {MvPowerSeries.X e} := by
    rw [Ideal.map_span,Set.image_singleton]
    change Ideal.span {actualUnshiftedTaylorAlgHom n (coordinateGerm e)}=Ideal.span {MvPowerSeries.X e}
    rw [actualUnshiftedTaylor_coordinate]
  apply (mem_analytic_ideal_iff_unshifted_extension n (Ideal.span {coordinateGerm e}) _).mpr
  rw [hmap,map_sub,hn,actualTaylor_polynomial_coordinate_evaluation]
  exact actual_point_normalized_member_congr_dehomogenization e b d _ hgT

/-- ONLY the original analytic member and actual point-power membership produce the same true quotient and whole restriction. -/
theorem exists_actual_analytic_point_initial_quotient (n : ℕ) (e : Fin n) (b : Fin n → ℂ)
    (d : ℕ) (g : HolGerm (ComplexModel n)) (hg : g ∈ actualAnalyticCoordinateIdeal Set.univ ^ d) :
    ∃ H : HolGerm (ComplexModel n),
      (coordinateGerm e)^d*H=actualAnalyticBlowupPullback Set.univ e b g ∧
      H-MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))
        (actualPointDehomogenization e b (actualPointHomogeneousPolynomial d (actualUnshiftedTaylorAlgHom n g))) ∈
          Ideal.span {coordinateGerm e} := by
  obtain ⟨H,hH,_hT⟩ := exists_actualAnalyticBlowup_quotient Set.univ e (mem_univ e) b d g hg
  exact ⟨H,hH,actual_analytic_point_quotient_initial_restriction n e b d g H hg hH⟩

end
end Hironaka.HironakaActualAnalyticPointInitialRestriction
