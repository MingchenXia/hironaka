/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualNormalUnitCoordinateChange
import Hironaka.Resolution.HironakaRelativeNormalMonomialBasis
import Hironaka.Resolution.HironakaActualCoefficientPresentationCentrePower

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNormalUnitAnalyticCoefficients
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualPointUnitCoordinateChange
  HironakaActualNormalUnitCoordinateChange HironakaHolomorphicJetChartInvariance

/-- The genuine normal-unit map fixes the actual entire tangent projection at every point. -/
theorem tangentProjection_actualNormalUnitForward (d t : ℕ) (j : Fin t)
    (b : Fin (d+t) → ℂ) (z : ComplexModel (d+t)) :
    tangentProjection d t
        (actualNormalUnitForward (actualTangentCentreVariables d t) (j.natAdd d) b z)=
      tangentProjection d t z := by
  ext i
  have hiA : i.castAdd t ∉ actualTangentCentreVariables d t := by
    rintro ⟨k,hk⟩
    have hv := congrArg Fin.val hk
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  have hie : i.castAdd t ≠ j.natAdd d := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  simp [tangentProjection_apply,actualNormalUnitForward_apply,hiA,hie]

/-- Every actual whole tangent germ, not merely a coordinate polynomial, is fixed. -/
theorem actualNormalUnitGermEquiv_tangentPullback (d t : ℕ) (j : Fin t)
    (b : Fin (d+t) → ℂ) (a : HolGerm (ComplexModel d)) :
    actualNormalUnitGermEquiv (actualTangentCentreVariables d t) (j.natAdd d) b
        (tangentPullback d t a)=tangentPullback d t a := by
  induction a using HolGerm.induction_on with
  | h f hf =>
    have ht := holomorphic_comp (tangentProjection d t)
      (Eventually.of_forall fun _ => (tangentProjection d t).differentiableAt) (map_zero _) hf
    have hF := holomorphic_comp
      (actualNormalUnitForward (actualTangentCentreVariables d t) (j.natAdd d) b)
      (local_toFun_holomorphic
        (actualNormalUnitLocalEquiv (actualTangentCentreVariables d t) (j.natAdd d) b))
      (actualNormalUnitForward_zero (actualTangentCentreVariables d t) (j.natAdd d) b) ht
    change HolGerm.mk ((f ∘ tangentProjection d t) ∘
      actualNormalUnitForward (actualTangentCentreVariables d t) (j.natAdd d) b) hF=
      HolGerm.mk (f ∘ tangentProjection d t) ht
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z =>
      congrArg f (tangentProjection_actualNormalUnitForward d t j b z)

/-- Finite evaluation retains the SAME entire actual tangent coefficient map under the true pullback. -/
theorem actualNormalUnitGermEquiv_eval₂ (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (x : Fin t → HolGerm (ComplexModel (d+t)))
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    actualNormalUnitGermEquiv (actualTangentCentreVariables d t) (j.natAdd d) b
        (MvPolynomial.eval₂ (tangentPullback d t).toRingHom x P)=
      MvPolynomial.eval₂ (tangentPullback d t).toRingHom
        (fun i => actualNormalUnitGermEquiv (actualTangentCentreVariables d t) (j.natAdd d) b (x i)) P := by
  let E := actualNormalUnitGermEquiv (actualTangentCentreVariables d t) (j.natAdd d) b
  change E.toRingEquiv.toRingHom (MvPolynomial.eval₂ (tangentPullback d t).toRingHom x P)=_
  rw [MvPolynomial.hom_eval₂]
  have hc : E.toRingEquiv.toRingHom.comp (tangentPullback d t).toRingHom=
      (tangentPullback d t).toRingHom := by
    apply RingHom.ext
    intro a
    change E (tangentPullback d t a)=tangentPullback d t a
    exact actualNormalUnitGermEquiv_tangentPullback d t j b a
  rw [hc]
  rfl

private theorem homogeneous_eval₂_scaled {R S : Type*} [CommRing R] [CommRing S]
    {t : ℕ} (f : R →+* S) (P : MvPolynomial (Fin t) R) (q : ℕ)
    (hP : P.IsHomogeneous q) (x : Fin t → S) (c : S) :
    MvPolynomial.eval₂ f (fun i => c*x i) P=c^q*MvPolynomial.eval₂ f x P := by
  change MvPolynomial.eval₂Hom f (fun i => c*x i) P=c^q*MvPolynomial.eval₂Hom f x P
  rw [← P.support_sum_monomial_coeff,map_sum,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [MvPolynomial.eval₂Hom_monomial,Finsupp.prod,mul_pow,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rw [← hP.degree_eq_sum_deg_support ha]
  ac_rfl

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- Exact finite normal-homogeneous dictionary with arbitrary genuine original tangent germ coefficients. -/
theorem actualNormalUnitGermEquiv_analytic_dehomogenization (d t : ℕ) (j : Fin t)
    (b : Fin (d+t) → ℂ) (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (q : ℕ) (hP : P.IsHomogeneous q) :
    actualNormalUnitGermEquiv (actualTangentCentreVariables d t) (j.natAdd d) b
        (MvPolynomial.eval₂ (tangentPullback d t).toRingHom
          (fun i => if i=j then 1 else
            (algebraMap ℂ (HolGerm (ComplexModel (d+t)))) (b (i.natAdd d))+normalCoordinate d t i) P)=
      (actualPointUnitReciprocal (j.natAdd d))^q*
        MvPolynomial.eval₂ (tangentPullback d t).toRingHom
          (fun i => normalCoordinate d t i+
            (algebraMap ℂ (HolGerm (ComplexModel (d+t)))) (if i=j then 1 else b (i.natAdd d))) P := by
  rw [actualNormalUnitGermEquiv_eval₂]
  have hc : (fun i : Fin t =>
      actualNormalUnitGermEquiv (actualTangentCentreVariables d t) (j.natAdd d) b
        (if i=j then 1 else
          (algebraMap ℂ (HolGerm (ComplexModel (d+t)))) (b (i.natAdd d))+normalCoordinate d t i))=
      (fun i => actualPointUnitReciprocal (j.natAdd d)*(normalCoordinate d t i+
        (algebraMap ℂ (HolGerm (ComplexModel (d+t)))) (if i=j then 1 else b (i.natAdd d)))) := by
    funext i
    by_cases hi : i=j
    · subst i
      simp only [if_true,map_one,normalCoordinate,map_one]
      simpa only [add_comm] using (actualPointUnit_reciprocal_mul (j.natAdd d)).symm
    · have hiA : i.natAdd d ∈ actualTangentCentreVariables d t := ⟨i,rfl⟩
      have hie : i.natAdd d ≠ j.natAdd d := by
        intro h
        apply hi
        apply Fin.ext
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd] at hv
        omega
      simp only [if_neg hi,map_add,AlgEquiv.commutes,normalCoordinate,
        actualNormalUnitGermEquiv_coordinate,if_neg hie,if_pos hiA]
      ring
  rw [hc,homogeneous_eval₂_scaled _ P q hP]

end
end Hironaka.HironakaActualNormalUnitAnalyticCoefficients
