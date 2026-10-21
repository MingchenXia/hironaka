/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalNormalTruncations
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Actual relative formal quotients by every original analytic ideal

Every whole extended original ideal image in a formal normal truncation is
the original formal-tangent span of literal Taylor numerators. Actual
finite normal monomial expansion supplies closure under every entire formal
multiplier. The ambient linear normal base-change dictionary identifies the
entire actual tensor ideal image, and descends through arbitrary original
whole ideal quotients by genuine right exactness.
No supplied ideal-image, flatness, basis or reduced-vertex certificate enters.
Blueprint: `hironaka-actual-relative-formal-quotients-extension.tex`.
-/

set_option autoImplicit false
open Set TensorProduct
open scoped TensorProduct
namespace Hironaka.HironakaActualRelativeFormalQuotients
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalCoordinatePowerDivision
  HironakaActualRelativeTaylorCoefficients HironakaActualFormalNormalTruncations

variable (d t q : ℕ)
local instance : Fintype (normalExponentIndex t q) := normalExponentFintype t q
local instance : Algebra (MvPowerSeries (Fin d) ℂ) (MvPowerSeries (Fin (d+t)) ℂ) :=
  (MvPowerSeries.rename (Fin.castAdd t : Fin d → Fin (d+t))).toRingHom.toAlgebra
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t
local instance : Algebra (HolGerm (ComplexModel d)) (MvPowerSeries (Fin d) ℂ) :=
  (actualUnshiftedTaylorAlgHom d).toRingHom.toAlgebra

/-- Literal original Taylor numerators, spanning only over the unchanged formal tangent ring. -/
def formalTaylorIdealSpan (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Submodule (MvPowerSeries (Fin d) ℂ)
      (MvPowerSeries (Fin (d+t)) ℂ ⧸
        actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q) :=
  Submodule.span (MvPowerSeries (Fin d) ℂ)
    (range fun g : I => Ideal.Quotient.mk
      (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)
      (actualUnshiftedTaylorAlgHom (d+t) g.val))

/-- The WHOLE original extended ideal image in the literal formal normal quotient. -/
def formalIdealImage (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Ideal (MvPowerSeries (Fin (d+t)) ℂ ⧸
      actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q) :=
  Ideal.map (Ideal.Quotient.mk
    (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q))
    (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)

theorem formalNormalMonomialMap_eq_sum
    (a : normalExponentIndex t q → MvPowerSeries (Fin d) ℂ) :
    formalNormalMonomialMap d t q a=
      ∑ γ : normalExponentIndex t q, a γ • Ideal.Quotient.mk
        (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)
        (actualUnshiftedTaylorAlgHom (d+t) (normalExponentMonomial d t γ.val)) := by
  unfold formalNormalMonomialMap formalNormalCombination
  simp only [LinearMap.comp_apply,Fintype.linearCombination_apply,map_sum,map_smul,
    actualUnshiftedTaylor_normalExponentMonomial]
  rfl

private theorem mul_generator_mem_formalTaylorIdealSpan
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (F : MvPowerSeries (Fin (d+t)) ℂ ⧸
      actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)
    (g : HolGerm (ComplexModel (d+t))) (hg : g ∈ I) :
    F * Ideal.Quotient.mk
      (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)
      (actualUnshiftedTaylorAlgHom (d+t) g) ∈ formalTaylorIdealSpan d t q I := by
  obtain ⟨a,rfl⟩ := formalNormalMonomialMap_surjective d t q F
  rw [formalNormalMonomialMap_eq_sum,Finset.sum_mul]
  apply (formalTaylorIdealSpan d t q I).sum_mem
  intro γ _
  rw [smul_mul_assoc,← map_mul,← map_mul]
  apply (formalTaylorIdealSpan d t q I).smul_mem
  exact Submodule.subset_span ⟨⟨normalExponentMonomial d t γ.val*g,
    I.mul_mem_left _ hg⟩,rfl⟩

private theorem mul_mem_formalTaylorIdealSpan
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (F z : MvPowerSeries (Fin (d+t)) ℂ ⧸
      actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)
    (hz : z ∈ formalTaylorIdealSpan d t q I) : F*z ∈ formalTaylorIdealSpan d t q I := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g,rfl⟩ := hz
    exact mul_generator_mem_formalTaylorIdealSpan d t q I F g.val g.property
  | zero => simpa only [mul_zero] using (formalTaylorIdealSpan d t q I).zero_mem
  | add a b _ _ ha hb =>
    simpa only [mul_add] using (formalTaylorIdealSpan d t q I).add_mem ha hb
  | smul c a _ ha =>
    simpa only [mul_smul_comm] using (formalTaylorIdealSpan d t q I).smul_mem c ha

private def formalTaylorSpanAsIdeal (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Ideal (MvPowerSeries (Fin (d+t)) ℂ ⧸
      actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q) where
  carrier := formalTaylorIdealSpan d t q I
  zero_mem' := (formalTaylorIdealSpan d t q I).zero_mem
  add_mem' := (formalTaylorIdealSpan d t q I).add_mem
  smul_mem' := fun F z hz => mul_mem_formalTaylorIdealSpan d t q I F z hz

/-- The genuine whole extended ideal image is exactly the actual formal-tangent coefficient span. -/
theorem formalTaylorIdealSpan_eq_wholeIdealImage
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    formalTaylorIdealSpan d t q I=
      (formalIdealImage d t q I).restrictScalars (MvPowerSeries (Fin d) ℂ) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,rfl⟩
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ g.property)
  · have hle : formalIdealImage d t q I ≤ formalTaylorSpanAsIdeal d t q I := by
      unfold formalIdealImage
      rw [Ideal.map_map]
      apply Ideal.map_le_iff_le_comap.mpr
      intro g hg
      exact Submodule.subset_span ⟨⟨g,hg⟩,rfl⟩
    exact hle

/-- The whole original ideal image inside the analytic normal quotient, over B. -/
def analyticNormalIdealImage (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Submodule (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t^q) :=
  (Ideal.map (Ideal.Quotient.mk (normalIdeal d t^q)) I).restrictScalars (HolGerm (ComplexModel d))

/-- The actual entire module image after formal tangent scalar extension. -/
def tensorIdealRange (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Submodule (MvPowerSeries (Fin d) ℂ)
      (MvPowerSeries (Fin d) ℂ ⊗[HolGerm (ComplexModel d)]
        (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t^q)) :=
  LinearMap.range (AlgebraTensorModule.lTensor (MvPowerSeries (Fin d) ℂ)
    (MvPowerSeries (Fin d) ℂ) (analyticNormalIdealImage d t q I).subtype)

/-- The same actual ambient dictionary identifies the ENTIRE tensor ideal image with the whole formal ideal image. -/
theorem map_tensorIdealRange_eq_wholeIdealImage
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Submodule.map (normalTruncationBaseChangeEquiv d t q).toLinearMap
      (tensorIdealRange d t q I)=
    (formalIdealImage d t q I).restrictScalars (MvPowerSeries (Fin d) ℂ) := by
  rw [← formalTaylorIdealSpan_eq_wholeIdealImage]
  unfold tensorIdealRange
  rw [← LinearMap.range_comp]
  apply le_antisymm
  · rintro _ ⟨w,rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using (formalTaylorIdealSpan d t q I).zero_mem
    | tmul c a =>
      change normalTruncationBaseChangeEquiv d t q
        (c ⊗ₜ[HolGerm (ComplexModel d)] a.val) ∈ formalTaylorIdealSpan d t q I
      have ha : a.val ∈ Ideal.map (Ideal.Quotient.mk (normalIdeal d t^q)) I := a.property
      obtain ⟨g,hg,he⟩ :=
        (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (normalIdeal d t^q))
          Ideal.Quotient.mk_surjective).mp ha
      rw [← he,normalTruncationBaseChangeEquiv_tmul_mk]
      exact (formalTaylorIdealSpan d t q I).smul_mem c (Submodule.subset_span ⟨⟨g,hg⟩,rfl⟩)
    | add a b ha hb =>
      simpa only [map_add] using (formalTaylorIdealSpan d t q I).add_mem ha hb
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,rfl⟩
    refine ⟨(1 : MvPowerSeries (Fin d) ℂ) ⊗ₜ[HolGerm (ComplexModel d)]
      (⟨Ideal.Quotient.mk (normalIdeal d t^q) g.val,Ideal.mem_map_of_mem _ g.property⟩ :
        analyticNormalIdealImage d t q I),?_⟩
    change normalTruncationBaseChangeEquiv d t q
      (1 ⊗ₜ[HolGerm (ComplexModel d)] Ideal.Quotient.mk (normalIdeal d t^q) g.val)=_
    simpa only [one_smul] using normalTruncationBaseChangeEquiv_tmul_mk d t q 1 g.val

private def quotientOfImageEquiv {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (N I : Ideal A) : ((A ⧸ N) ⧸ Ideal.map (Ideal.Quotient.mk N) I) ≃ₐ[B] A ⧸ (I ⊔ N) :=
  (DoubleQuot.quotQuotEquivQuotSupₐ B N I).trans
    (Ideal.quotientEquivAlgOfEq B (sup_comm N I))

private theorem quotientOfImageEquiv_mk {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (N I : Ideal A) (g : A) :
    quotientOfImageEquiv (B := B) N I
      (Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk N) I) (Ideal.Quotient.mk N g))=
    Ideal.Quotient.mk (I ⊔ N) g := rfl

/-- Every whole original analytic ideal quotient has its actual relative formal base change. -/
def relativeFormalQuotientEquiv (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    (MvPowerSeries (Fin d) ℂ ⊗[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t^q))) ≃ₗ[MvPowerSeries (Fin d) ℂ]
    (MvPowerSeries (Fin (d+t)) ℂ ⧸
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I ⊔
        actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)) := by
  let e0 := ((quotientOfImageEquiv (B := HolGerm (ComplexModel d))
    (normalIdeal d t^q) I).symm.toLinearEquiv).baseChange
      (HolGerm (ComplexModel d)) (MvPowerSeries (Fin d) ℂ) _ _
  let e1 := AlgebraTensorModule.tensorQuotientEquiv (R := HolGerm (ComplexModel d))
    (MvPowerSeries (Fin d) ℂ) (HolGerm (ComplexModel d)) (MvPowerSeries (Fin d) ℂ)
      (analyticNormalIdealImage d t q I)
  let e2 := Submodule.Quotient.equiv (tensorIdealRange d t q I)
    ((formalIdealImage d t q I).restrictScalars (MvPowerSeries (Fin d) ℂ))
    (normalTruncationBaseChangeEquiv d t q) (map_tensorIdealRange_eq_wholeIdealImage d t q I)
  let e3 := (quotientOfImageEquiv (B := MvPowerSeries (Fin d) ℂ)
    (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)
    (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)).toLinearEquiv
  exact e0.trans (e1.trans (e2.trans e3))

/-- The arbitrary-original-ideal dictionary retains every actual pure tensor Taylor numerator. -/
theorem relativeFormalQuotientEquiv_tmul_mk
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (c : MvPowerSeries (Fin d) ℂ) (g : HolGerm (ComplexModel (d+t))) :
    relativeFormalQuotientEquiv d t q I
      (c ⊗ₜ[HolGerm (ComplexModel d)] Ideal.Quotient.mk (I ⊔ normalIdeal d t^q) g)=
    c • Ideal.Quotient.mk
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I ⊔
        actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)
      (actualUnshiftedTaylorAlgHom (d+t) g) := by
  change quotientOfImageEquiv (B := MvPowerSeries (Fin d) ℂ)
    (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)
    (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)
    (Ideal.Quotient.mk (formalIdealImage d t q I)
      (normalTruncationBaseChangeEquiv d t q
        (c ⊗ₜ[HolGerm (ComplexModel d)] Ideal.Quotient.mk (normalIdeal d t^q) g)))=_
  rw [normalTruncationBaseChangeEquiv_tmul_mk]
  change (quotientOfImageEquiv (B := MvPowerSeries (Fin d) ℂ)
    (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)
    (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)).toLinearEquiv
    (c • Ideal.Quotient.mk
      (Ideal.map (Ideal.Quotient.mk
        (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q))
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I))
      (Ideal.Quotient.mk
        (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)
        (actualUnshiftedTaylorAlgHom (d+t) g)))=_
  rw [map_smul]
  apply congrArg (fun z => c • z)
  exact quotientOfImageEquiv_mk
    (B := MvPowerSeries (Fin d) ℂ)
    (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)
    (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)
    (actualUnshiftedTaylorAlgHom (d+t) g)

section Transitions
set_option maxHeartbeats 1000000

/-- The actual original normal-power quotient transition, retaining the same whole original ideal. -/
def analyticRelativeTruncationMap (I : Ideal (HolGerm (ComplexModel (d+t))))
    (s : ℕ) (hs : s ≤ q) :
    (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t^q)) →ₐ[HolGerm (ComplexModel d)]
    (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t^s)) :=
  Ideal.Quotient.factorₐ (HolGerm (ComplexModel d))
    (sup_le_sup le_rfl (Ideal.pow_le_pow_right hs))

/-- The literal formal normal-power transition for the same original Taylor ideal. -/
def formalRelativeTruncationMap (I : Ideal (HolGerm (ComplexModel (d+t))))
    (s : ℕ) (hs : s ≤ q) :
    (MvPowerSeries (Fin (d+t)) ℂ ⧸
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I ⊔
        actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q)) →ₐ[MvPowerSeries (Fin d) ℂ]
    (MvPowerSeries (Fin (d+t)) ℂ ⧸
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I ⊔
        actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^s)) :=
  Ideal.Quotient.factorₐ (MvPowerSeries (Fin d) ℂ)
    (sup_le_sup le_rfl (Ideal.pow_le_pow_right hs))

/-- Every normal-power transition commutes on the entire actual tensor product, including order zero. -/
theorem relativeFormalQuotientEquiv_transition
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) (hs : s ≤ q)
    (z : MvPowerSeries (Fin d) ℂ ⊗[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t^q))) :
    relativeFormalQuotientEquiv d t s I
      (AlgebraTensorModule.lTensor (MvPowerSeries (Fin d) ℂ) (MvPowerSeries (Fin d) ℂ)
        (analyticRelativeTruncationMap d t q I s hs).toLinearMap z)=
    formalRelativeTruncationMap d t q I s hs (relativeFormalQuotientEquiv d t q I z) := by
  let f := (relativeFormalQuotientEquiv d t s I).toLinearMap.comp
    (AlgebraTensorModule.lTensor (MvPowerSeries (Fin d) ℂ) (MvPowerSeries (Fin d) ℂ)
      (analyticRelativeTruncationMap d t q I s hs).toLinearMap)
  let g := (formalRelativeTruncationMap d t q I s hs).toLinearMap.comp
    (relativeFormalQuotientEquiv d t q I).toLinearMap
  have hfg : ∀ w, f w=g w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact f.map_zero.trans g.map_zero.symm
    | tmul c a =>
      obtain ⟨h,rfl⟩ := Ideal.Quotient.mk_surjective a
      change relativeFormalQuotientEquiv d t s I
        (c ⊗ₜ[HolGerm (ComplexModel d)] Ideal.Quotient.mk (I ⊔ normalIdeal d t^s) h)=
        formalRelativeTruncationMap d t q I s hs (relativeFormalQuotientEquiv d t q I
          (c ⊗ₜ[HolGerm (ComplexModel d)] Ideal.Quotient.mk (I ⊔ normalIdeal d t^q) h))
      rw [relativeFormalQuotientEquiv_tmul_mk,relativeFormalQuotientEquiv_tmul_mk,map_smul]
      rfl
    | add a b ha hb =>
      exact (f.map_add a b).trans ((congrArg₂ (·+·) ha hb).trans (g.map_add a b).symm)
  exact hfg z

end Transitions
end
end Hironaka.HironakaActualRelativeFormalQuotients
