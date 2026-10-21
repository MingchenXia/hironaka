/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalNormalTruncations
import Hironaka.Resolution.HironakaActualPolynomialAnalyticFlatness
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Whole actual formal normal series and entire relative polynomial flatness

Literal joined-exponent currying gives a genuine entire formal-series algebra
isomorphism, with multiplication proved by a finite antidiagonal bijection.
The actual relative Taylor coefficient dictionary gives exact polynomial scalar
compatibility. Genuine flat polynomial base change, normal-adic completion and
faithful actual Taylor target descent prove entire relative polynomial
flatness and all actual analytic relations by whole polynomial syzygies.

No relative normalized saturation, transformed standardness or current
Hilbert--Samuel persistence criterion is assumed or concluded here.
Blueprint: `hironaka-actual-formal-normal-series-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators TensorProduct
namespace Hironaka.HironakaActualFormalNormalSeries
noncomputable section
open HolGerm HironakaActualCoefficientPresentationCentrePower
  HironakaActualRelativeTaylorCoefficients HironakaActualRelativeCoefficientGerms
  HironakaActualFormalNormalTruncations HironakaActualOriginalFormalTaylor
  HironakaActualTaylorFaithfullyFlat HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualPolynomialAnalyticFlatness
variable {d t : ℕ}
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t

@[simp] theorem tangent_joined (β : Fin d →₀ ℕ) (γ : Fin t →₀ ℕ) :
    actualTangentExponent (actualJoinedExponent β γ)=β := by
  ext i
  simp [actualTangentExponent,actualJoinedExponent]
@[simp] theorem normal_joined (β : Fin d →₀ ℕ) (γ : Fin t →₀ ℕ) :
    actualNormalExponent (actualJoinedExponent β γ)=γ := by
  ext i
  simp [actualNormalExponent,actualJoinedExponent]
@[simp] theorem tangent_add (a b : Fin (d+t) →₀ ℕ) :
    actualTangentExponent (a+b)=actualTangentExponent a+actualTangentExponent b := by
  ext i
  simp [actualTangentExponent]
@[simp] theorem normal_add (a b : Fin (d+t) →₀ ℕ) :
    actualNormalExponent (a+b)=actualNormalExponent a+actualNormalExponent b := by
  ext i
  simp [actualNormalExponent]
theorem joined_add (β₁ β₂ : Fin d →₀ ℕ) (γ₁ γ₂ : Fin t →₀ ℕ) :
    actualJoinedExponent (β₁+β₂) (γ₁+γ₂)=actualJoinedExponent β₁ γ₁+actualJoinedExponent β₂ γ₂ := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [actualJoinedExponent]

@[simp] theorem tangent_zero : actualTangentExponent (0 : Fin (d+t) →₀ ℕ)=0 := by
  ext i
  simp [actualTangentExponent]
@[simp] theorem normal_zero : actualNormalExponent (0 : Fin (d+t) →₀ ℕ)=0 := by
  ext i
  simp [actualNormalExponent]
@[simp] theorem joined_eq_zero (β : Fin d →₀ ℕ) (γ : Fin t →₀ ℕ) :
    actualJoinedExponent β γ=0 ↔ β=0 ∧ γ=0 := by
  constructor
  · intro h
    exact ⟨by simpa only [tangent_joined,tangent_zero] using congrArg actualTangentExponent h,
      by simpa only [normal_joined,normal_zero] using congrArg actualNormalExponent h⟩
  · rintro ⟨rfl,rfl⟩
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [actualJoinedExponent]

/-- Literal WHOLE normal coefficient currying. -/
def formalNormalSeries (F : MvPowerSeries (Fin (d+t)) ℂ) :
    MvPowerSeries (Fin t) (MvPowerSeries (Fin d) ℂ) := actualFormalNormalCoefficient F

private theorem formalNormalSeries_mul (F G : MvPowerSeries (Fin (d+t)) ℂ) :
    formalNormalSeries (F*G)=formalNormalSeries F*formalNormalSeries G := by
  ext γ β
  change MvPowerSeries.coeff (actualJoinedExponent β γ) (F*G)=_
  rw [MvPowerSeries.coeff_mul,MvPowerSeries.coeff_mul,map_sum]
  simp_rw [MvPowerSeries.coeff_mul]
  rw [←Finset.sum_product']
  refine Finset.sum_bij (fun a _ =>
    ((actualNormalExponent a.1,actualNormalExponent a.2),
      (actualTangentExponent a.1,actualTangentExponent a.2))) ?_ ?_ ?_ ?_
  · intro a ha
    have hsum := Finset.mem_antidiagonal.mp ha
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_antidiagonal.mpr
      simpa only [normal_add,normal_joined] using congrArg actualNormalExponent hsum
    · apply Finset.mem_antidiagonal.mpr
      simpa only [tangent_add,tangent_joined] using congrArg actualTangentExponent hsum
  · intro a _ b _ hab
    have hN := congrArg Prod.fst hab
    have hT := congrArg Prod.snd hab
    apply Prod.ext
    · rw [←actualJoinedExponent_split a.1,←actualJoinedExponent_split b.1]
      exact congrArg₂ actualJoinedExponent (congrArg Prod.fst hT) (congrArg Prod.fst hN)
    · rw [←actualJoinedExponent_split a.2,←actualJoinedExponent_split b.2]
      exact congrArg₂ actualJoinedExponent (congrArg Prod.snd hT) (congrArg Prod.snd hN)
  · rintro ⟨⟨γ₁,γ₂⟩,⟨β₁,β₂⟩⟩ ha
    obtain ⟨hγ,hβ⟩ := Finset.mem_product.mp ha
    have hγ' := Finset.mem_antidiagonal.mp hγ
    have hβ' := Finset.mem_antidiagonal.mp hβ
    refine ⟨(actualJoinedExponent β₁ γ₁,actualJoinedExponent β₂ γ₂),?_,?_⟩
    · apply Finset.mem_antidiagonal.mpr
      rw [←joined_add,hβ',hγ']
    · simp only [normal_joined,tangent_joined]
  · intro a _
    change MvPowerSeries.coeff a.1 F*MvPowerSeries.coeff a.2 G=
      MvPowerSeries.coeff (actualJoinedExponent (actualTangentExponent a.1) (actualNormalExponent a.1)) F*
        MvPowerSeries.coeff (actualJoinedExponent (actualTangentExponent a.2) (actualNormalExponent a.2)) G
    rw [actualJoinedExponent_split,actualJoinedExponent_split]

/-- The genuine whole original formal series ring is the iterated normal series ring. -/
def formalNormalSeriesEquiv (d t : ℕ) :
    MvPowerSeries (Fin (d+t)) ℂ ≃ₐ[ℂ] MvPowerSeries (Fin t) (MvPowerSeries (Fin d) ℂ) where
  toFun := formalNormalSeries
  invFun := fun F α => MvPowerSeries.coeff (actualTangentExponent α)
    (MvPowerSeries.coeff (actualNormalExponent α) F)
  left_inv F := by
    apply MvPowerSeries.ext
    intro α
    change MvPowerSeries.coeff (actualJoinedExponent (actualTangentExponent α) (actualNormalExponent α)) F=_
    rw [actualJoinedExponent_split]
  right_inv F := by
    ext γ β
    change MvPowerSeries.coeff (actualTangentExponent (actualJoinedExponent β γ))
      (MvPowerSeries.coeff (actualNormalExponent (actualJoinedExponent β γ)) F)=_
    rw [tangent_joined,normal_joined]
  map_mul' := formalNormalSeries_mul
  map_add' F G := by ext γ β; rfl
  commutes' c := by
    simp only [MvPowerSeries.algebraMap_apply,Algebra.algebraMap_self_apply]
    ext γ β
    change MvPowerSeries.coeff (actualJoinedExponent β γ) (MvPowerSeries.C c)=
      MvPowerSeries.coeff β (MvPowerSeries.coeff γ (MvPowerSeries.C (MvPowerSeries.C c)))
    by_cases hγ : γ=0 <;> by_cases hβ : β=0 <;>
      simp [MvPowerSeries.coeff_C,joined_eq_zero,hγ,hβ]



/-- Both original coordinate blocks and the entire actual coefficient are retained. -/
theorem formalNormalSeriesEquiv_coefficient (d t : ℕ) (F : MvPowerSeries (Fin (d+t)) ℂ)
    (γ : Fin t →₀ ℕ) (β : Fin d →₀ ℕ) :
    MvPowerSeries.coeff β (MvPowerSeries.coeff γ (formalNormalSeriesEquiv d t F))=
      MvPowerSeries.coeff (actualJoinedExponent β γ) F := rfl

/-- Literal relative polynomial evaluation retains every actual whole Taylor coefficient. -/
theorem formalNormalSeries_normalPolynomialEval (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    formalNormalSeriesEquiv d t (actualUnshiftedTaylorAlgHom (d+t) (normalPolynomialEval d t P))=
      ((MvPolynomial.map (actualUnshiftedTaylorAlgHom d).toRingHom P) :
        MvPowerSeries (Fin t) (MvPowerSeries (Fin d) ℂ)) := by
  apply MvPowerSeries.ext
  intro γ
  change actualFormalNormalCoefficient
    (actualUnshiftedTaylorAlgHom (d+t) (normalPolynomialEval d t P)) γ=_
  rw [actualFormalNormalCoefficient_normalPolynomialEval,MvPolynomial.coeff_coe,MvPolynomial.coeff_map]
  rfl

private theorem polynomial_coefficient_map_flat {B C : Type*} [CommRing B] [CommRing C]
    [Algebra B C] [Module.Flat B C] (t : ℕ) :
    (MvPolynomial.map (algebraMap B C) : MvPolynomial (Fin t) B →+* MvPolynomial (Fin t) C).Flat := by
  let E : (MvPolynomial (Fin t) B) ⊗[B] C ≃+* MvPolynomial (Fin t) C :=
    (Algebra.TensorProduct.comm B (MvPolynomial (Fin t) B) C).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv B C).toRingEquiv
  have hE (p : MvPolynomial (Fin t) B) : E (p ⊗ₜ[B] (1 : C))=MvPolynomial.map (algebraMap B C) p := by
    change (MvPolynomial.algebraTensorAlgEquiv B C)
      ((Algebra.TensorProduct.comm B (MvPolynomial (Fin t) B) C) (p ⊗ₜ[B] (1 : C)))=_
    rw [Algebra.TensorProduct.comm_tmul]
    simpa only [one_smul] using (MvPolynomial.algebraTensorAlgEquiv_tmul B C (1 : C) p)
  have hflat : (algebraMap (MvPolynomial (Fin t) B) ((MvPolynomial (Fin t) B) ⊗[B] C)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have heq : E.toRingHom.comp (algebraMap (MvPolynomial (Fin t) B) ((MvPolynomial (Fin t) B) ⊗[B] C))=
      MvPolynomial.map (algebraMap B C) := by
    apply RingHom.ext
    intro p
    rw [RingHom.comp_apply,Algebra.TensorProduct.algebraMap_def,RingHom.comp_apply,
      Algebra.algebraMap_self_apply]
    exact hE p
  rw [←heq]
  exact hflat.comp (RingHom.Flat.of_bijective E.bijective)

private theorem polynomial_formal_flat {B : Type*} [CommRing B] [IsNoetherianRing B] (t : ℕ) :
    Module.Flat (MvPolynomial (Fin t) B) (MvPowerSeries (Fin t) B) := by
  have : Module.Flat (MvPolynomial (Fin t) B)
      (AdicCompletion (MvPolynomial.idealOfVars (Fin t) B) (MvPolynomial (Fin t) B)) := inferInstance
  exact Module.Flat.of_linearEquiv (MvPowerSeries.toAdicCompletionAlgEquiv (Fin t) B).toLinearEquiv

private theorem unshiftedTaylor_faithfullyFlat (n : ℕ) :
    (actualUnshiftedTaylorAlgHom n).toRingHom.FaithfullyFlat := by
  have hc (m : ℕ) (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ)
      (hf : f.toRingHom.FaithfullyFlat) :
      (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) hm) f).toRingHom.FaithfullyFlat := by
    subst m
    exact hf
  exact hc (0+n) (Nat.zero_add n) (originalTaylorAlgHom n) (originalTaylorAlgHom_faithfullyFlat n)


/-- Whole relative polynomial evaluation is genuinely flat over the actual analytic coefficient ring. -/
theorem normalPolynomialEval_flat (d t : ℕ) : (normalPolynomialEval d t).toRingHom.Flat := by
  let B := HolGerm (ComplexModel d)
  let Bh := MvPowerSeries (Fin d) ℂ
  let P := MvPolynomial (Fin t) B
  let Q := MvPolynomial (Fin t) Bh
  let R := HolGerm (ComplexModel (d+t))
  let S := MvPowerSeries (Fin (d+t)) ℂ
  let V := MvPowerSeries (Fin t) Bh
  let τB := actualUnshiftedTaylorAlgHom d
  let τR := actualUnshiftedTaylorAlgHom (d+t)
  let : Algebra B Bh := τB.toRingHom.toAlgebra
  let : Module.Flat B Bh := (unshiftedTaylor_faithfullyFlat d).flat
  let a : P →+* Q := MvPolynomial.map τB.toRingHom
  have ha : a.Flat := polynomial_coefficient_map_flat t
  let ψ : Q →+* V := MvPolynomial.coeToMvPowerSeries.ringHom
  have hψ : ψ.Flat := by
    change Module.Flat Q V
    exact polynomial_formal_flat t
  let E := formalNormalSeriesEquiv d t
  have hcomp : (τR.toRingHom.comp (normalPolynomialEval d t).toRingHom).Flat := by
    have heq : τR.toRingHom.comp (normalPolynomialEval d t).toRingHom=
        E.symm.toRingHom.comp (ψ.comp a) := by
      apply RingHom.ext
      intro F
      apply E.injective
      change E (τR (normalPolynomialEval d t F))=E (E.symm (ψ (a F)))
      rw [E.apply_symm_apply,formalNormalSeries_normalPolynomialEval]
      rfl
    rw [heq]
    exact (ha.comp hψ).comp (RingHom.Flat.of_bijective E.symm.bijective)
  let : Algebra P R := (normalPolynomialEval d t).toRingHom.toAlgebra
  let : Algebra R S := τR.toRingHom.toAlgebra
  let : Algebra P S := (τR.toRingHom.comp (normalPolynomialEval d t).toRingHom).toAlgebra
  let : IsScalarTower P R S := IsScalarTower.of_algebraMap_eq fun F => rfl
  let : Module.Flat P S := hcomp
  let : Module.FaithfullyFlat R S := unshiftedTaylor_faithfullyFlat (d+t)
  change Module.Flat P R
  exact flat_of_faithfully_flat_target P R S


/-- EVERY true whole analytic relation on literal polynomial functions is generated by internally produced actual polynomial syzygies. -/
theorem relative_analytic_relation_iff_polynomial_syzygies (d t r : ℕ)
    (p : Fin r → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (A : Fin r → HolGerm (ComplexModel (d+t))) :
    (∑ i,normalPolynomialEval d t (p i)*A i)=0 ↔
      ∃ (k : ℕ) (c : Fin r → Fin k → MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
        (B : Fin k → HolGerm (ComplexModel (d+t))),
        (∀ i,A i=∑ j,normalPolynomialEval d t (c i j)*B j) ∧
        ∀ j,∑ i,p i*c i j=0 := by
  let P := MvPolynomial (Fin t) (HolGerm (ComplexModel d))
  let R := HolGerm (ComplexModel (d+t))
  let : Algebra P R := (normalPolynomialEval d t).toRingHom.toAlgebra
  have : Module.Flat P R := normalPolynomialEval_flat d t
  constructor
  · intro h
    have hs : (∑ i,p i • A i)=0 := by
      simpa only [Algebra.smul_def,RingHom.algebraMap_toAlgebra,
        AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using h
    obtain ⟨k,c,B,hc,hp⟩ := (Module.Flat.iff_forall_isTrivialRelation (R := P) (M := R)).mp
      ‹Module.Flat P R› (f := p) (x := A) hs
    refine ⟨k,c,B,?_,hp⟩
    intro i
    simpa only [Algebra.smul_def,RingHom.algebraMap_toAlgebra,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hc i
  · rintro ⟨k,c,B,hc,hp⟩
    have ht : Module.IsTrivialRelation p A := ⟨k,c,B,
      fun i => by simpa only [Algebra.smul_def,RingHom.algebraMap_toAlgebra,
        AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hc i,hp⟩
    simpa only [Algebra.smul_def,RingHom.algebraMap_toAlgebra,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using Module.sum_smul_eq_zero_of_isTrivialRelation ht

end
end Hironaka.HironakaActualFormalNormalSeries
