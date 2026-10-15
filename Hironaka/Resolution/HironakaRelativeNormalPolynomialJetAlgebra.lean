/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalDeformationInitialRelations

/-! Genuine multiplicative models of ENTIRE normal jets. Mathematics.tex first.
OWN OFFLIB; nearby whole normal-cone/Rees and all-order analytic free open are OPEN. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalPolynomialJetAlgebra
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalIdealMatrices

def actualPolynomialNormalIdeal (d t : ℕ) : Ideal (MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :=
  Ideal.span (range MvPolynomial.X)

theorem actualPolynomialNormalIdeal_monomial_mem (d t : ℕ) (α : Fin t →₀ ℕ)
    (a : HolGerm (ComplexModel d)) :
    MvPolynomial.monomial α a ∈ actualPolynomialNormalIdeal d t ^ normalExponentDegree α := by
  classical
  rw [MvPolynomial.monomial_eq,α.prod_fintype
    (fun i k => (MvPolynomial.X i : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) ^ k) (fun _ => pow_zero _)]
  apply Ideal.mul_mem_left
  have h : (∏ i : Fin t, (MvPolynomial.X i : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) ^ α i) ∈
      ∏ i : Fin t, actualPolynomialNormalIdeal d t ^ α i :=
    Ideal.prod_mem_prod (fun i _ => Ideal.pow_mem_pow (show (MvPolynomial.X i : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) ∈ actualPolynomialNormalIdeal d t from Ideal.subset_span ⟨i,rfl⟩) (α i))
  simpa only [Finset.prod_pow_eq_pow_sum,normalExponentDegree] using h

theorem actualPolynomialNormalIdeal_map (d t : ℕ) :
    let := tangentAlgebra d t
    Ideal.map (normalPolynomialEval d t).toRingHom (actualPolynomialNormalIdeal d t) = normalIdeal d t := by
  let := tangentAlgebra d t
  rw [actualPolynomialNormalIdeal,Ideal.map_span]
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨P,⟨i,rfl⟩,rfl⟩
    exact ⟨i,(MvPolynomial.aeval_X (normalCoordinate d t) i).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨MvPolynomial.X i,⟨i,rfl⟩,MvPolynomial.aeval_X (normalCoordinate d t) i⟩

theorem normalPolynomialEval_mem_power_iff (d t q : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    normalPolynomialEval d t P ∈ normalIdeal d t ^ q ↔ P ∈ actualPolynomialNormalIdeal d t ^ q := by
  classical
  let := tangentAlgebra d t
  constructor
  · intro hP
    rw [P.as_sum]
    apply Ideal.sum_mem
    intro α hα
    have hdeg : q ≤ normalExponentDegree α := by
      by_contra hn
      have hz := coefficient_eq_zero_of_normalPolynomialEval_mem d t q P α (by omega) hP
      exact (MvPolynomial.mem_support_iff.mp hα) hz
    exact Ideal.pow_le_pow_right hdeg (actualPolynomialNormalIdeal_monomial_mem d t α (MvPolynomial.coeff α P))
  · intro hP
    have hm := Ideal.mem_map_of_mem (normalPolynomialEval d t).toRingHom hP
    rwa [Ideal.map_pow,actualPolynomialNormalIdeal_map] at hm

theorem actualPolynomialNormalIdeal_power_iff_coefficients (d t q : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    P ∈ actualPolynomialNormalIdeal d t ^ q ↔
      ∀ α, normalExponentDegree α < q → MvPolynomial.coeff α P = 0 := by
  classical
  constructor
  · intro h α hα
    exact coefficient_eq_zero_of_normalPolynomialEval_mem d t q P α hα
      ((normalPolynomialEval_mem_power_iff d t q P).mpr h)
  · intro h
    rw [P.as_sum]
    apply Ideal.sum_mem
    intro α hα
    have hdeg : q ≤ normalExponentDegree α := by
      by_contra hn
      exact (MvPolynomial.mem_support_iff.mp hα) (h α (by omega))
    exact Ideal.pow_le_pow_right hdeg (actualPolynomialNormalIdeal_monomial_mem d t α (MvPolynomial.coeff α P))

def actualPolynomialJetMap (d t q : ℕ) :
    let := tangentAlgebra d t
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) →ₐ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t ^ q) :=
  let := tangentAlgebra d t
  (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ q)).comp (normalPolynomialEval d t)

theorem actualPolynomialJetMap_surjective (d t q : ℕ) :
    Function.Surjective (actualPolynomialJetMap d t q) := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  intro y
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a,ha⟩ := exists_normalMonomial_coefficient_representative d t q g
  let P := ∑ α : normalExponentIndex t q, MvPolynomial.monomial α.val (a α)
  refine ⟨P,?_⟩
  change Ideal.Quotient.mk (normalIdeal d t ^ q) (normalPolynomialEval d t P) = Ideal.Quotient.mk (normalIdeal d t ^ q) g
  apply Eq.symm
  apply Ideal.Quotient.eq.mpr
  simpa only [P,map_sum,normalPolynomialEval_monomial] using ha

theorem actualPolynomialJetMap_kernel (d t q : ℕ) :
    let := tangentAlgebra d t
    RingHom.ker (actualPolynomialJetMap d t q).toRingHom = actualPolynomialNormalIdeal d t ^ q := by
  let := tangentAlgebra d t
  dsimp only
  ext P
  rw [RingHom.mem_ker]
  change Ideal.Quotient.mk (normalIdeal d t ^ q) (normalPolynomialEval d t P) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact normalPolynomialEval_mem_power_iff d t q P

def actualPolynomialJetAlgebraEquiv (d t q : ℕ) :
    let := tangentAlgebra d t
    (MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸ actualPolynomialNormalIdeal d t ^ q) ≃ₐ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t ^ q) :=
by
  let := tangentAlgebra d t
  dsimp only
  let f := actualPolynomialJetMap d t q
  let e : (MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸ RingHom.ker f.toRingHom) ≃ₐ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t ^ q) :=
    Ideal.quotientKerAlgEquivOfSurjective (actualPolynomialJetMap_surjective d t q)
  exact (Ideal.quotientEquivAlgOfEq (HolGerm (ComplexModel d)) (actualPolynomialJetMap_kernel d t q).symm).trans e

theorem actualPolynomialJetAlgebraEquiv_mk (d t q : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    let := tangentAlgebra d t
    actualPolynomialJetAlgebraEquiv d t q (Ideal.Quotient.mk (actualPolynomialNormalIdeal d t ^ q) P) =
      Ideal.Quotient.mk (normalIdeal d t ^ q) (normalPolynomialEval d t P) := by
  let := tangentAlgebra d t
  rfl

def actualWholePolynomialJet (d t q : ℕ) :
    let := tangentAlgebra d t
    HolGerm (ComplexModel (d+t)) →ₐ[HolGerm (ComplexModel d)]
      (MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸ actualPolynomialNormalIdeal d t ^ q) :=
  let := tangentAlgebra d t
  (actualPolynomialJetAlgebraEquiv d t q).symm.toAlgHom.comp
    (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ q))

theorem actualWholePolynomialJet_evaluation (d t q : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    let := tangentAlgebra d t
    actualWholePolynomialJet d t q (normalPolynomialEval d t P) =
      Ideal.Quotient.mk (actualPolynomialNormalIdeal d t ^ q) P := by
  let := tangentAlgebra d t
  change (actualPolynomialJetAlgebraEquiv d t q).symm
    (Ideal.Quotient.mk (normalIdeal d t ^ q) (normalPolynomialEval d t P)) = _
  rw [← actualPolynomialJetAlgebraEquiv_mk,AlgEquiv.symm_apply_apply]

theorem actualWholePolynomialJet_mul (d t q : ℕ)
    (g h : HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    actualWholePolynomialJet d t q (g*h) = actualWholePolynomialJet d t q g * actualWholePolynomialJet d t q h :=
  map_mul _ _ _

def actualRelativePolynomialJetMap (d t q : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let := tangentAlgebra d t
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) →ₐ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q)) :=
  let := tangentAlgebra d t
  (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (I ⊔ normalIdeal d t ^ q)).comp (normalPolynomialEval d t)

def actualRelativePolynomialJetIdeal (d t q : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Ideal (MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :=
  let := tangentAlgebra d t
  Ideal.comap (normalPolynomialEval d t).toRingHom (I ⊔ normalIdeal d t ^ q)

theorem actualRelativePolynomialJetMap_surjective (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) : Function.Surjective (actualRelativePolynomialJetMap d t q I) := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  intro y
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a,ha⟩ := exists_normalMonomial_coefficient_representative d t q g
  let P := ∑ α : normalExponentIndex t q, MvPolynomial.monomial α.val (a α)
  refine ⟨P,?_⟩
  change Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ q) (normalPolynomialEval d t P) = Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ q) g
  apply Eq.symm
  apply Ideal.Quotient.eq.mpr
  apply (show normalIdeal d t ^ q ≤ I ⊔ normalIdeal d t ^ q from le_sup_right)
  simpa only [P,map_sum,normalPolynomialEval_monomial] using ha

theorem actualRelativePolynomialJetMap_kernel (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let := tangentAlgebra d t
    RingHom.ker (actualRelativePolynomialJetMap d t q I).toRingHom = actualRelativePolynomialJetIdeal d t q I := by
  let := tangentAlgebra d t
  dsimp only
  ext P
  rw [RingHom.mem_ker]
  change Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ q) (normalPolynomialEval d t P) = 0 ↔
    normalPolynomialEval d t P ∈ I ⊔ normalIdeal d t ^ q
  exact Ideal.Quotient.eq_zero_iff_mem

def actualRelativePolynomialJetAlgebraEquiv (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let := tangentAlgebra d t
    (MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸ actualRelativePolynomialJetIdeal d t q I) ≃ₐ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q)) :=
by
  let := tangentAlgebra d t
  dsimp only
  let f := actualRelativePolynomialJetMap d t q I
  let e : (MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸ RingHom.ker f.toRingHom) ≃ₐ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q)) :=
    Ideal.quotientKerAlgEquivOfSurjective (actualRelativePolynomialJetMap_surjective d t q I)
  exact (Ideal.quotientEquivAlgOfEq (HolGerm (ComplexModel d)) (actualRelativePolynomialJetMap_kernel d t q I).symm).trans e

theorem actualRelativePolynomialJetAlgebraEquiv_mk (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    let := tangentAlgebra d t
    actualRelativePolynomialJetAlgebraEquiv d t q I (Ideal.Quotient.mk (actualRelativePolynomialJetIdeal d t q I) P) =
      Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ q) (normalPolynomialEval d t P) := by
  let := tangentAlgebra d t
  rfl

def actualOriginalCoherentPolynomialJetAlgebraEquiv (d t q : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    (MvPolynomial (Fin t) (HolGerm (ComplexModel d)) ⧸
      actualRelativePolynomialJetIdeal d t q (originalCoherentOriginIdeal I)) ≃ₐ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ (originalCoherentOriginIdeal I ⊔ normalIdeal d t ^ q)) :=
  actualRelativePolynomialJetAlgebraEquiv d t q (originalCoherentOriginIdeal I)

end
end Hironaka.HironakaRelativeNormalPolynomialJetAlgebra
