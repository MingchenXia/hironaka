/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCoordinateSpecializationHS
import Hironaka.Resolution.HironakaActualPointDehomogenizedInitial

/-! Genuine original single-coordinate contraction, nonzero inverse, and fixed dehomogenized polynomial germs. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAxisContraction
noncomputable section
open HolGerm OkaRelationSheaf HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetMonomialSpan HironakaActualPointDehomogenizedInitial
variable {n : ℕ}

/-- The actual continuous complex-linear contraction of exactly the chosen original coordinate. -/
def actualAxisContraction (e : Fin n) (c : ℂ) : ComplexModel n →L[ℂ] ComplexModel n :=
  ContinuousLinearMap.id ℂ (ComplexModel n)+(c-1) •
    (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).smulRight (EuclideanSpace.single e 1)

/-- Every actual coordinate retains its literal intended value. -/
theorem actualAxisContraction_apply (e : Fin n) (c : ℂ) (z : ComplexModel n) (i : Fin n) :
    actualAxisContraction e c z i=if i=e then c*z i else z i := by
  by_cases hi : i=e
  · subst i
    simp [actualAxisContraction]
    ring
  · simp [actualAxisContraction,hi]

/-- Genuine original coordinate contraction composition multiplies the true parameters. -/
theorem actualAxisContraction_comp (e : Fin n) (c t : ℂ) (z : ComplexModel n) :
    actualAxisContraction e c (actualAxisContraction e t z)=actualAxisContraction e (c*t) z := by
  ext i
  simp only [actualAxisContraction_apply]
  split_ifs <;> ring

private theorem actualAxisContraction_one (e : Fin n) (z : ComplexModel n) :
    actualAxisContraction e 1 z=z := by
  ext i
  simp [actualAxisContraction_apply]

/-- Actual whole original germ pullback by the genuine coordinate contraction. -/
def actualAxisContractionGerm (e : Fin n) (c : ℂ) :
    HolGerm (ComplexModel n) →ₐ[ℂ] HolGerm (ComplexModel n) :=
  compAlgHom (actualAxisContraction e c)
    (Eventually.of_forall fun _ => (actualAxisContraction e c).differentiableAt)
    (actualAxisContraction e c).map_zero

private theorem actualAxisContractionGerm_mk (e : Fin n) (c : ℂ) (f : ComplexModel n → ℂ)
    (hf : HolAt f 0) :
    actualAxisContractionGerm e c (HolGerm.mk f hf)=
      HolGerm.mk (f ∘ actualAxisContraction e c)
        (holomorphic_comp _ (Eventually.of_forall fun _ => (actualAxisContraction e c).differentiableAt)
          (actualAxisContraction e c).map_zero hf) := rfl

/-- Composition of true whole pullbacks has its actual contravariant coordinate order. -/
theorem actualAxisContractionGerm_comp (e : Fin n) (c t : ℂ) :
    (actualAxisContractionGerm e c).comp (actualAxisContractionGerm e t)=actualAxisContractionGerm e (t*c) := by
  apply AlgHom.ext
  intro g
  induction g using HolGerm.induction_on with
  | h f hf =>
      rw [AlgHom.comp_apply,actualAxisContractionGerm_mk,actualAxisContractionGerm_mk,
        actualAxisContractionGerm_mk]
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z => congrArg f (actualAxisContraction_comp e t c z)

/-- Parameter one is the identity on EVERY genuine original whole germ. -/
theorem actualAxisContractionGerm_one (e : Fin n) :
    actualAxisContractionGerm e 1=AlgHom.id ℂ (HolGerm (ComplexModel n)) := by
  apply AlgHom.ext
  intro g
  induction g using HolGerm.induction_on with
  | h f hf =>
      change actualAxisContractionGerm e 1 (HolGerm.mk f hf)=HolGerm.mk f hf
      rw [actualAxisContractionGerm_mk e 1 f hf]
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z => congrArg f (actualAxisContraction_one e z)

/-- The actual inverse-parameter maps supply a genuine original complex germ algebra equivalence. -/
def actualAxisContractionGermEquiv (e : Fin n) (c : ℂ) (hc : c ≠ 0) :
    HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) := by
  apply AlgEquiv.ofAlgHom (actualAxisContractionGerm e c) (actualAxisContractionGerm e c⁻¹)
  · rw [actualAxisContractionGerm_comp,inv_mul_cancel₀ hc,actualAxisContractionGerm_one]
  · rw [actualAxisContractionGerm_comp,mul_inv_cancel₀ hc,actualAxisContractionGerm_one]

/-- Whole original coordinate germs have exactly the true actual contraction values. -/
theorem actualAxisContractionGerm_coordinate (e : Fin n) (c : ℂ) (i : Fin n) :
    actualAxisContractionGerm e c (coordinateGerm i)=
      if i=e then algebraMap ℂ _ c*coordinateGerm i else coordinateGerm i := by
  by_cases hi : i=e
  · rw [if_pos hi,coordinateGerm,actualAxisContractionGerm_mk]
    change HolGerm.mk ((fun z : ComplexModel n => z i) ∘ actualAxisContraction e c) _=
      HolGerm.mk (fun _ => c) (eventually_differentiableAt_const c)*HolGerm.mk (fun z : ComplexModel n => z i) _
    rw [← HolGerm.mk_mul]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by simpa only [Function.comp_apply,if_pos hi] using actualAxisContraction_apply e c z i
  · rw [if_neg hi,coordinateGerm,actualAxisContractionGerm_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by simpa only [Function.comp_apply,if_neg hi] using actualAxisContraction_apply e c z i

/-- EVERY actual finite dehomogenized polynomial germ is fixed, including by the true coordinate-zero contraction. -/
theorem actualAxisContractionGerm_dehomogenization (e : Fin n) (b : Fin n → ℂ) (c : ℂ)
    (P : MvPolynomial (Fin n) ℂ) :
    actualAxisContractionGerm e c
        (MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n)) (actualPointDehomogenization e b P))=
      MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n)) (actualPointDehomogenization e b P) := by
  have hm : (actualAxisContractionGerm e c).comp
      ((MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))).comp (actualPointDehomogenization e b))=
        (MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))).comp (actualPointDehomogenization e b) := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i=e <;>
      simp [AlgHom.comp_apply,actualPointDehomogenization,hi,actualAxisContractionGerm_coordinate]
  exact DFunLike.congr_fun hm P

/-- The same actual contraction is jointly complex smooth in its genuine parameter and original variables. -/
theorem actualAxisContractionJoint_contDiff (e : Fin n) :
    ContDiff ℂ ∞ (fun u : ComplexModel 1 × ComplexModel n => actualAxisContraction e (u.1 0) u.2) := by
  have hp : ContDiff ℂ ∞ (fun u : ComplexModel 1 × ComplexModel n => u.1 0) :=
    (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).contDiff.comp contDiff_fst
  have hx : ContDiff ℂ ∞ (fun u : ComplexModel 1 × ComplexModel n => u.2 e) :=
    (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).contDiff.comp contDiff_snd
  have he : (fun u : ComplexModel 1 × ComplexModel n => actualAxisContraction e (u.1 0) u.2)=
      fun u : ComplexModel 1 × ComplexModel n => u.2+((u.1 0-1)*u.2 e) • EuclideanSpace.single e 1 := by
    funext u
    change u.2+(u.1 0-1) • (u.2 e • EuclideanSpace.single e 1)=_
    rw [smul_smul]
  rw [he]
  exact contDiff_snd.add (((hp.sub contDiff_const).mul hx).smul contDiff_const)

end
end Hironaka.HironakaActualAxisContraction
