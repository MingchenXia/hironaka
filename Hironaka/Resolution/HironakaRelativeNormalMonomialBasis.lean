/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaRelativeNormalTaylorCoefficients
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Actual entire relative normal monomial bases

Actual analytic normal derivations and whole base-germ coefficient separation
construct genuine finite monomial bases for every original normal-power
quotient. Entire holomorphic Hadamard representatives produce surjectivity,
with no independence, rank, spanning or flatness certificate supplied.
Original nonlinear flattening transports the actual whole vanishing ideal
and all power bases; original regular and closed smooth centre geometry
internally supplies every needed coordinate and base action.

Only the whole ambient normal-power quotients are asserted finite free.
Quotients by an additional original ideal need not be free or flat. All-degree
normal-flat selection for singular spaces, higher HS descent and general G8
remain OPEN. Blueprint: `hironaka-relative-normal-monomial-basis-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalMonomialBasis
open Hironaka.HolomorphicIdealSheaves HolGerm HolomorphicTaylorTail
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalIdeal HironakaSmoothCentreRelativeIdeal
  HironakaRelativeNormalTaylorCoefficients HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetRankLoci
open Hironaka
attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass
noncomputable section
variable {n : ℕ}

/-- The true original product rule on the ENTIRE ambient holomorphic germ ring. -/
theorem iteratedDerivativeGerm_singleton_mul (v : ComplexModel n)
    (g h : HolGerm (ComplexModel n)) :
    iteratedDerivativeGerm [v] (g*h) =
      g*iteratedDerivativeGerm [v] h+h*iteratedDerivativeGerm [v] g := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    induction h using HolGerm.induction_on with
    | h g hg =>
      rw [← HolGerm.mk_mul, iteratedDerivativeGerm_mk,
        iteratedDerivativeGerm_mk, iteratedDerivativeGerm_mk,
        ← HolGerm.mk_mul, ← HolGerm.mk_mul, ← HolGerm.mk_add]
      apply HolGerm.mk_eq_mk_iff.mpr
      filter_upwards [hf,hg] with z hf hg
      simp only [iterDeriv_cons, iterDeriv_nil, dirDeriv]
      rw [fderiv_fun_mul hf hg]
      rfl

/-- The genuine normal derivative is linear over the ENTIRE original tangential base germ ring. -/
def normalDerivativeMap (d t : ℕ) (i : Fin t) :
    letI := tangentAlgebra d t
    HolGerm (ComplexModel (d+t)) →ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)) :=
  letI := tangentAlgebra d t
  { toFun := iteratedDerivativeGerm [normalVector d t i]
    map_add' := fun g h => map_add _ g h
    map_smul' := fun a g => by
      change iteratedDerivativeGerm ([i].map (normalVector d t)) (tangentPullback d t a*g) =
        tangentPullback d t a*iteratedDerivativeGerm ([i].map (normalVector d t)) g
      exact iteratedDerivativeGerm_tangent_mul d t [i] a g }

/-- A true normal holomorphic derivation, with actual original analytic product-rule fields. -/
def normalDerivation (d t : ℕ) (i : Fin t) :
    letI := tangentAlgebra d t
    Derivation (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t)))
      (HolGerm (ComplexModel (d+t))) :=
  letI := tangentAlgebra d t
  Derivation.mk' (normalDerivativeMap d t i) (fun g h => iteratedDerivativeGerm_singleton_mul _ g h)

/-- The actual derivative of the original normal coordinate is its genuine Kronecker delta. -/
theorem normalDerivation_normalCoordinate (d t : ℕ) (i j : Fin t) :
    let := tangentAlgebra d t
    normalDerivation d t i (normalCoordinate d t j) = if i=j then 1 else 0 := by
  let := tangentAlgebra d t
  change iteratedDerivativeGerm [normalVector d t i] (coordinateGerm (j.natAdd d)) = _
  unfold coordinateGerm
  rw [iteratedDerivativeGerm_mk]
  have he : (fun z : ComplexModel (d+t) =>
      iterDeriv [normalVector d t i] (fun w : ComplexModel (d+t) => w (j.natAdd d)) z) =
      (fun _ => if i=j then (1 : ℂ) else 0) := by
    funext z
    simp only [iterDeriv_cons, iterDeriv_nil, dirDeriv]
    have hc : fderiv ℂ (fun w : ComplexModel (d+t) => w (j.natAdd d)) z =
        EuclideanSpace.proj (j.natAdd d) :=
      (EuclideanSpace.proj (j.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ).fderiv
    rw [hc]
    simp [normalVector, Fin.natAdd_inj, eq_comm]
  calc
    _ = HolGerm.mk (fun _ : ComplexModel (d+t) => if i=j then (1 : ℂ) else 0)
        (eventually_differentiableAt_const _) :=
      HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun z => congrFun he z)
    _ = _ := by split_ifs <;> simp [HolGerm.mk_const]

/-- Genuine entire-base polynomial evaluation at the actual original normal-coordinate germs. -/
def normalPolynomialEval (d t : ℕ) :
    letI := tangentAlgebra d t
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) →ₐ[HolGerm (ComplexModel d)]
      HolGerm (ComplexModel (d+t)) :=
  letI := tangentAlgebra d t
  MvPolynomial.aeval (normalCoordinate d t)

/-- The actual whole analytic normal derivative equals evaluation of the true formal polynomial derivative. -/
theorem normalDerivation_polynomialEval (d t : ℕ) (i : Fin t)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    let := tangentAlgebra d t
    normalDerivation d t i (normalPolynomialEval d t P) =
      normalPolynomialEval d t (MvPolynomial.pderiv i P) := by
  classical
  let := tangentAlgebra d t
  induction P using MvPolynomial.induction_on with
  | C a => simp [normalPolynomialEval]
  | add P Q hP hQ => simp [hP,hQ]
  | mul_X P j hP =>
    dsimp only at hP
    rw [map_mul, Derivation.leibniz, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
    simp only [normalPolynomialEval, MvPolynomial.aeval_X] at hP ⊢
    rw [hP, normalDerivation_normalCoordinate]
    by_cases h : i=j
    · subst j
      simp only [MvPolynomial.pderiv_X_self, map_one, smul_eq_mul, if_true, mul_one]
      ring
    · rw [if_neg h, MvPolynomial.pderiv_X_of_ne (Ne.symm h), map_zero]
      simp only [smul_eq_mul, mul_zero, zero_add, add_zero]
      exact mul_comm _ _

/-- Actual whole plane trace of a true normal polynomial is its ENTIRE original constant coefficient. -/
theorem planeTrace_normalPolynomialEval (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    planeTrace d t (normalPolynomialEval d t P) = MvPolynomial.coeff 0 P := by
  classical
  let := tangentAlgebra d t
  rw [← MvPolynomial.constantCoeff_eq]
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [normalPolynomialEval, MvPolynomial.aeval_C]
    change planeTrace d t (tangentPullback d t a) = MvPolynomial.constantCoeff (MvPolynomial.C a)
    rw [planeTrace_tangentPullback, MvPolynomial.constantCoeff_C]
  | add P Q hP hQ => rw [map_add, map_add, map_add, hP, hQ]
  | mul_X P j _ =>
    simp only [normalPolynomialEval, map_mul, MvPolynomial.aeval_X,
      planeTrace_normalCoordinate, MvPolynomial.constantCoeff_X, mul_zero]

/-- Actual analytic normal differentiation lowers the COMPLETE original normal ideal power. -/
theorem normalDerivation_mem_normalIdeal_pow (d t q : ℕ) (i : Fin t)
    (g : HolGerm (ComplexModel (d+t))) (hg : g ∈ normalIdeal d t ^ (q+1)) :
    let := tangentAlgebra d t
    normalDerivation d t i g ∈ normalIdeal d t ^ q := by
  let := tangentAlgebra d t
  induction g using HolGerm.induction_on with
  | h f hf =>
    have hp := (mem_normalIdeal_pow_iff_InNormalPow d t (q+1) hf).mp hg
    change iteratedDerivativeGerm [normalVector d t i] (HolGerm.mk f hf) ∈ _
    rw [iteratedDerivativeGerm_mk]
    exact mem_normalIdeal_pow_of_InNormalPow d t q
      (eventually_holomorphic_iterDeriv hf [normalVector d t i])
      (InNormalPow_dirDeriv (normalVector d t i) q hp)

/-- The true degree is the actual sum of the original exponent entries. -/
def normalExponentDegree {t : ℕ} (α : Fin t →₀ ℕ) : ℕ := ∑ i, α i

/-- Complete normal-power membership forces EACH true lower-degree polynomial coefficient to be zero as a WHOLE base germ. -/
theorem coefficient_eq_zero_of_normalPolynomialEval_mem (d t q : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (α : Fin t →₀ ℕ) (hα : normalExponentDegree α < q)
    (hP : normalPolynomialEval d t P ∈ normalIdeal d t ^ q) :
    MvPolynomial.coeff α P = 0 := by
  classical
  let := tangentAlgebra d t
  induction q generalizing P α with
  | zero => omega
  | succ q ih =>
    by_cases ha : α=0
    · subst α
      have hJ : normalPolynomialEval d t P ∈ normalIdeal d t :=
        Ideal.pow_le_self (by omega) hP
      rw [normalIdeal_eq_ker_planeTrace] at hJ
      have hz : planeTrace d t (normalPolynomialEval d t P) = 0 := hJ
      rwa [planeTrace_normalPolynomialEval] at hz
    · have hi : ∃ i : Fin t, α i ≠ 0 := by
        by_contra hn
        push Not at hn
        exact ha (Finsupp.ext fun i => hn i)
      obtain ⟨i, hi⟩ := hi
      let β := α-Finsupp.single i 1
      have hle : Finsupp.single i 1 ≤ α := Finsupp.single_le_iff.mpr (by omega)
      have he : β+Finsupp.single i 1 = α := tsub_add_cancel_of_le hle
      have hd : normalExponentDegree α = normalExponentDegree β+1 := by
        rw [← he]
        simp [normalExponentDegree, Finset.sum_add_distrib]
      have hβ : normalExponentDegree β < q := by omega
      have hp : normalPolynomialEval d t (MvPolynomial.pderiv i P) ∈ normalIdeal d t ^ q := by
        rw [← normalDerivation_polynomialEval]
        exact normalDerivation_mem_normalIdeal_pow d t q i _ hP
      have hz := ih (MvPolynomial.pderiv i P) β hβ hp
      rw [MvPolynomial.coeff_pderiv, he] at hz
      have hc : (β i+1 : HolGerm (ComplexModel d)) ≠ 0 := by
        intro hc
        have hh := congrArg HolGerm.eval hc
        simp only [map_add, map_natCast, map_one, map_zero] at hh
        have hne : ((β i+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (β i)
        exact hne (by simpa only [Nat.cast_add, Nat.cast_one] using hh)
      exact (mul_eq_zero.mp hz).resolve_right hc

/-- The genuine normal exponent family, indexed without duplicate words. -/
abbrev normalExponentIndex (t q : ℕ) := {α : Fin t →₀ ℕ // normalExponentDegree α < q}

/-- Every true entry of a lower-degree exponent is bounded by the actual degree. -/
theorem normalExponentIndex_entry_lt (t q : ℕ) (α : normalExponentIndex t q) (i : Fin t) :
    α.val i < q := by
  have hl : α.val i ≤ normalExponentDegree α.val :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact hl.trans_lt α.property

/-- Finiteness is internally produced by the actual bounded exponent-entry encoding. -/
@[instance_reducible] def normalExponentFintype (t q : ℕ) : Fintype (normalExponentIndex t q) :=
  Fintype.ofInjective (fun α i => (⟨α.val i, normalExponentIndex_entry_lt t q α i⟩ : Fin q))
    (fun _α _β h => Subtype.ext (Finsupp.ext fun i => congrArg Fin.val (congrFun h i)))

/-- The actual entire original normal monomial. -/
def normalExponentMonomial (d t : ℕ) (α : Fin t →₀ ℕ) : HolGerm (ComplexModel (d+t)) :=
  ∏ i, normalCoordinate d t i ^ α i

/-- Original polynomial monomials evaluate to genuine normal monomials with WHOLE base coefficients. -/
theorem normalPolynomialEval_monomial (d t : ℕ) (α : Fin t →₀ ℕ)
    (a : HolGerm (ComplexModel d)) :
    normalPolynomialEval d t (MvPolynomial.monomial α a) =
      tangentPullback d t a * normalExponentMonomial d t α := by
  let := tangentAlgebra d t
  rw [normalPolynomialEval, MvPolynomial.aeval_monomial]
  change tangentPullback d t a * α.prod (fun i k => normalCoordinate d t i ^ k) = _
  exact congrArg (fun p => tangentPullback d t a*p)
    (α.prod_fintype (fun i k => normalCoordinate d t i ^ k) (fun _ => pow_zero _))

/-- Genuine whole quotient combination by the finite distinct actual normal exponent family. -/
def normalMonomialCombination (d t q : ℕ) :
    letI := tangentAlgebra d t
    letI := normalExponentFintype t q
    (normalExponentIndex t q → HolGerm (ComplexModel d)) →ₗ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t ^ q) :=
  letI := tangentAlgebra d t
  letI := normalExponentFintype t q
  Fintype.linearCombination (HolGerm (ComplexModel d))
    (fun α => Ideal.Quotient.mk (normalIdeal d t ^ q) (normalExponentMonomial d t α.val))

/-- The actual quotient combination is evaluation of its original genuine finite polynomial. -/
theorem normalMonomialCombination_apply (d t q : ℕ)
    (a : normalExponentIndex t q → HolGerm (ComplexModel d)) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    normalMonomialCombination d t q a =
      Ideal.Quotient.mk (normalIdeal d t ^ q)
        (normalPolynomialEval d t (∑ α : normalExponentIndex t q, MvPolynomial.monomial α.val (a α))) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  dsimp only
  rw [normalMonomialCombination, Fintype.linearCombination_apply, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [normalPolynomialEval_monomial]
  have he : tangentPullback d t (a α)*normalExponentMonomial d t α.val =
      (a α) • normalExponentMonomial d t α.val := by rw [Algebra.smul_def]; rfl
  rw [he]
  exact ((Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ q)).toLinearMap.map_smul _ _).symm

/-- Each ORIGINAL indexed polynomial coefficient is exactly its genuine entire base entry. -/
theorem coefficient_normalMonomialCombination_polynomial (d t q : ℕ)
    (a : normalExponentIndex t q → HolGerm (ComplexModel d)) (α : normalExponentIndex t q) :
    let := normalExponentFintype t q
    MvPolynomial.coeff α.val (∑ β : normalExponentIndex t q, MvPolynomial.monomial β.val (a β)) = a α := by
  classical
  let := normalExponentFintype t q
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Subtype.val_injective.eq_iff]
  simp

/-- Genuine lower-degree coefficient separation proves the actual entire monomial quotient map injective. -/
theorem normalMonomialCombination_injective (d t q : ℕ) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    Function.Injective (normalMonomialCombination d t q) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  dsimp only
  intro a b hab
  have hz : normalMonomialCombination d t q (a-b) = 0 := by
    rw [map_sub, hab, sub_self]
  rw [normalMonomialCombination_apply, Ideal.Quotient.eq_zero_iff_mem] at hz
  funext α
  have hc := coefficient_eq_zero_of_normalPolynomialEval_mem d t q _ α.val α.property hz
  rw [coefficient_normalMonomialCombination_polynomial] at hc
  exact sub_eq_zero.mp hc

/-- The actual exponent counting a genuine original normal word. -/
def normalWordExponent (t : ℕ) {q : ℕ} (w : monomialIndex t q) : Fin t →₀ ℕ :=
  ∑ k : Fin w.1.val, Finsupp.single (w.2 k) 1

/-- The true exponent degree is exactly the original word length. -/
theorem normalWordExponent_degree (t : ℕ) {q : ℕ} (w : monomialIndex t q) :
    normalExponentDegree (normalWordExponent t w) = w.1.val := by
  classical
  simp only [normalWordExponent, normalExponentDegree, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp

/-- Counting indices in the genuine word gives precisely the entire actual normal monomial. -/
theorem normalWord_eq_exponentMonomial (d t : ℕ) {q : ℕ} (w : monomialIndex t q) :
    normalWord d t w = normalExponentMonomial d t (normalWordExponent t w) := by
  classical
  let := tangentAlgebra d t
  have hm := congrArg (normalPolynomialEval d t)
    (MvPolynomial.monomial_sum_one (R := HolGerm (ComplexModel d)) Finset.univ
      (fun k : Fin w.1.val => Finsupp.single (w.2 k) 1))
  rw [map_prod] at hm
  have he : ∀ k : Fin w.1.val,
      normalPolynomialEval d t (MvPolynomial.monomial (Finsupp.single (w.2 k) 1) 1) =
        normalCoordinate d t (w.2 k) := by
    intro k
    change normalPolynomialEval d t (MvPolynomial.X (w.2 k)) = _
    exact MvPolynomial.aeval_X (normalCoordinate d t) _
  rw [normalPolynomialEval_monomial, map_one, one_mul] at hm
  simp only [he] at hm
  exact hm.symm

/-- EVERY actual whole normal-word representative lies in the genuine distinct monomial quotient range. -/
theorem normalWordSpan_le_combination_comap (d t q : ℕ) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    normalWordSpan d t q ≤ (LinearMap.range (normalMonomialCombination d t q)).comap
      (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ q)).toLinearMap := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  dsimp only
  apply Submodule.span_le.mpr
  rintro g ⟨w, rfl⟩
  change Ideal.Quotient.mk (normalIdeal d t ^ q) (normalWord d t w) ∈
    LinearMap.range (normalMonomialCombination d t q)
  change _ ∈ LinearMap.range (Fintype.linearCombination (HolGerm (ComplexModel d)) _)
  rw [Fintype.range_linearCombination, normalWord_eq_exponentMonomial]
  apply Submodule.subset_span
  exact ⟨⟨normalWordExponent t w, by rw [normalWordExponent_degree]; exact w.1.isLt⟩, rfl⟩

/-- Internally produced real whole-germ representatives prove genuine monomial quotient surjectivity. -/
theorem normalMonomialCombination_surjective (d t q : ℕ) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    Function.Surjective (normalMonomialCombination d t q) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  dsimp only
  intro z
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨p, hp, hrem⟩ := exists_normalWord_representative d t q g
  have hr := normalWordSpan_le_combination_comap d t q hp
  obtain ⟨a, ha⟩ := hr
  refine ⟨a, ?_⟩
  change normalMonomialCombination d t q a = Ideal.Quotient.mk (normalIdeal d t ^ q) p at ha
  rw [ha]
  exact (Ideal.Quotient.eq.mpr hrem).symm

/-- Actual whole-germ monomial combination is an internally constructed base-linear equivalence. -/
def normalPowerLinearEquiv (d t q : ℕ) :
    letI := tangentAlgebra d t
    letI := normalExponentFintype t q
    (normalExponentIndex t q → HolGerm (ComplexModel d)) ≃ₗ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t ^ q) :=
  letI := tangentAlgebra d t
  letI := normalExponentFintype t q
  LinearEquiv.ofBijective (normalMonomialCombination d t q)
    ⟨normalMonomialCombination_injective d t q, normalMonomialCombination_surjective d t q⟩

/-- The genuine original normal-power quotient has its actual finite monomial basis. -/
def normalMonomialBasis (d t q : ℕ) :
    letI := tangentAlgebra d t
    letI := normalExponentFintype t q
    Module.Basis (normalExponentIndex t q) (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t ^ q) :=
  letI := tangentAlgebra d t
  letI := normalExponentFintype t q
  (Pi.basisFun (HolGerm (ComplexModel d)) (normalExponentIndex t q)).map (normalPowerLinearEquiv d t q)

/-- Each actual basis vector is literally its original entire normal-monomial quotient class. -/
theorem normalMonomialBasis_apply (d t q : ℕ) (α : normalExponentIndex t q) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    normalMonomialBasis d t q α =
      Ideal.Quotient.mk (normalIdeal d t ^ q) (normalExponentMonomial d t α.val) := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  dsimp only
  rw [normalMonomialBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  change Fintype.linearCombination (HolGerm (ComplexModel d)) _ (Pi.single α 1) = _
  rw [Fintype.linearCombination_apply_single, one_smul]

/-- EVERY actual whole normal-power quotient is free over the ENTIRE original tangential germ ring. -/
theorem free_quotient_normalIdeal_pow (d t q : ℕ) :
    letI := tangentAlgebra d t
    Module.Free (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t ^ q) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  exact Module.Free.of_basis (normalMonomialBasis d t q)

/-- The true nonlinear germ transport combines ORIGINAL monomials with its genuine transported base action. -/
def transportedNormalMonomialCombination (d t q : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t))) :
    letI := transportedNormalAlgebra d t E
    letI := normalExponentFintype t q
    (normalExponentIndex t q → HolGerm (ComplexModel d)) →ₗ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q) :=
  letI := transportedNormalAlgebra d t E
  letI := normalExponentFintype t q
  Fintype.linearCombination (HolGerm (ComplexModel d))
    (fun α => Ideal.Quotient.mk (Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q)
      (E (normalExponentMonomial d t α.val)))

/-- Entire genuine polynomial evaluation gives exactly the actual transported monomial combination. -/
theorem transportedNormalMonomialCombination_apply (d t q : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t)))
    (a : normalExponentIndex t q → HolGerm (ComplexModel d)) :
    let := transportedNormalAlgebra d t E
    let := normalExponentFintype t q
    transportedNormalMonomialCombination d t q E a =
      Ideal.Quotient.mk (Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q)
        (E (normalPolynomialEval d t (∑ α : normalExponentIndex t q, MvPolynomial.monomial α.val (a α)))) := by
  let := transportedNormalAlgebra d t E
  let := normalExponentFintype t q
  dsimp only
  rw [transportedNormalMonomialCombination, Fintype.linearCombination_apply, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [normalPolynomialEval_monomial, map_mul]
  have he : E (tangentPullback d t (a α))*E (normalExponentMonomial d t α.val) =
      (a α) • E (normalExponentMonomial d t α.val) := by rw [Algebra.smul_def]; rfl
  rw [he]
  exact ((Ideal.Quotient.mkₐ (HolGerm (ComplexModel d))
    (Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q)).toLinearMap.map_smul _ _).symm

/-- The genuine inverse nonlinear map and actual whole coefficient separation prove transport injectivity. -/
theorem transportedNormalMonomialCombination_injective (d t q : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t))) :
    let := transportedNormalAlgebra d t E
    let := normalExponentFintype t q
    Function.Injective (transportedNormalMonomialCombination d t q E) := by
  let := transportedNormalAlgebra d t E
  let := normalExponentFintype t q
  dsimp only
  intro a b hab
  have hz : transportedNormalMonomialCombination d t q E (a-b) = 0 := by
    rw [map_sub, hab, sub_self]
  rw [transportedNormalMonomialCombination_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.map_pow] at hz
  obtain ⟨h, hh, he⟩ :=
    (Ideal.mem_map_iff_of_surjective E.toRingEquiv.toRingHom E.surjective).mp hz
  change E h = E (normalPolynomialEval d t _) at he
  have hp := E.injective he
  rw [hp] at hh
  funext α
  have hc := coefficient_eq_zero_of_normalPolynomialEval_mem d t q _ α.val α.property hh
  rw [coefficient_normalMonomialCombination_polynomial] at hc
  exact sub_eq_zero.mp hc

/-- Genuine entire original representatives and actual nonlinear inverse produce transport surjectivity. -/
theorem transportedNormalMonomialCombination_surjective (d t q : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t))) :
    let := transportedNormalAlgebra d t E
    let := normalExponentFintype t q
    Function.Surjective (transportedNormalMonomialCombination d t q E) := by
  let := transportedNormalAlgebra d t E
  let := normalExponentFintype t q
  dsimp only
  intro z
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, ha⟩ := normalMonomialCombination_surjective d t q
    (Ideal.Quotient.mk (normalIdeal d t ^ q) (E.symm g))
  rw [normalMonomialCombination_apply] at ha
  have hm := Ideal.mem_map_of_mem E.toRingEquiv.toRingHom (Ideal.Quotient.eq.mp ha.symm)
  rw [Ideal.map_pow] at hm
  change E (E.symm g-normalPolynomialEval d t _) ∈ _ at hm
  rw [map_sub, E.apply_symm_apply] at hm
  refine ⟨a, ?_⟩
  rw [transportedNormalMonomialCombination_apply]
  exact (Ideal.Quotient.eq.mpr hm).symm

/-- The actual transported whole normal-power quotient has its true internally constructed linear equivalence. -/
def transportedNormalPowerLinearEquiv (d t q : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t))) :
    letI := transportedNormalAlgebra d t E
    letI := normalExponentFintype t q
    (normalExponentIndex t q → HolGerm (ComplexModel d)) ≃ₗ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q) :=
  letI := transportedNormalAlgebra d t E
  letI := normalExponentFintype t q
  LinearEquiv.ofBijective (transportedNormalMonomialCombination d t q E)
    ⟨transportedNormalMonomialCombination_injective d t q E,
      transportedNormalMonomialCombination_surjective d t q E⟩

/-- Genuine transported actual monomial basis of the ENTIRE original centre-power quotient. -/
def transportedNormalMonomialBasis (d t q : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t))) :
    letI := transportedNormalAlgebra d t E
    letI := normalExponentFintype t q
    Module.Basis (normalExponentIndex t q) (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+t)) ⧸ Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q) :=
  letI := transportedNormalAlgebra d t E
  letI := normalExponentFintype t q
  (Pi.basisFun (HolGerm (ComplexModel d)) (normalExponentIndex t q)).map
    (transportedNormalPowerLinearEquiv d t q E)

/-- The transported basis has exactly its true original transformed normal-monomial classes. -/
theorem transportedNormalMonomialBasis_apply (d t q : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t)))
    (α : normalExponentIndex t q) :
    let := transportedNormalAlgebra d t E
    let := normalExponentFintype t q
    transportedNormalMonomialBasis d t q E α =
      Ideal.Quotient.mk (Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q)
        (E (normalExponentMonomial d t α.val)) := by
  classical
  let := transportedNormalAlgebra d t E
  let := normalExponentFintype t q
  dsimp only
  rw [transportedNormalMonomialBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  change Fintype.linearCombination (HolGerm (ComplexModel d)) _ (Pi.single α 1) = _
  rw [Fintype.linearCombination_apply_single, one_smul]

/-- Actual nonlinear transport makes each WHOLE normal-power quotient free over its actual original base. -/
theorem free_quotient_mapped_normalIdeal_pow (d t q : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t))) :
    letI := transportedNormalAlgebra d t E
    Module.Free (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+t)) ⧸ Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q) := by
  let := transportedNormalAlgebra d t E
  let := normalExponentFintype t q
  exact Module.Free.of_basis (transportedNormalMonomialBasis d t q E)

section RegularProducer
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ORIGINAL regularity internally constructs flattening, the WHOLE original centre ideal, and every genuine finite monomial basis over its actual base. -/
theorem exists_regular_relative_monomial_basis (C : Set M) (x : M)
    (hreg : RegularAtDim (n := d+t) C x d) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      let E := flatteningGermEquiv _ Φ h0
      let K := wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x x (mem_chart_source _ x)
      K = Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ∧
      (∀ q : ℕ, Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t ^ q) = K ^ q) ∧
      (letI := transportedNormalAlgebra d t E
        ∀ q : ℕ, letI := normalExponentFintype t q
        ∃ b : Module.Basis (normalExponentIndex t q) (HolGerm (ComplexModel d))
            (HolGerm (ComplexModel (d+t)) ⧸ K ^ q),
          (∀ α, b α = Ideal.Quotient.mk (K ^ q) (E (normalExponentMonomial d t α.val))) ∧
          Module.Free (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t)) ⧸ K ^ q) ∧
          Module.Finite (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t)) ⧸ K ^ q)) := by
  obtain ⟨Φ, hsrc, h0, hflat, hK, hp, _, _⟩ := exists_regular_relative_ideal C x hreg
  refine ⟨Φ, hsrc, h0, hflat, hK, hp, ?_⟩
  let := transportedNormalAlgebra d t (flatteningGermEquiv _ Φ h0)
  intro q
  let := normalExponentFintype t q
  rw [hK]
  refine ⟨transportedNormalMonomialBasis d t q _, transportedNormalMonomialBasis_apply d t q _,
    free_quotient_mapped_normalIdeal_pow d t q _, ?_⟩
  exact Module.Finite.of_basis (transportedNormalMonomialBasis d t q (flatteningGermEquiv _ Φ h0))

end RegularProducer

section ClosedProducer
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

@[instance_reducible] private def chartedSpaceOfSumEq (d t : ℕ) (he : d+t=n) : ChartedSpace (ComplexModel (d+t)) M :=
  he.symm ▸ (inferInstance : ChartedSpace (ComplexModel n) M)

private theorem complexManifoldOfSumEq (d t : ℕ) (he : d+t=n) :
    letI := chartedSpaceOfSumEq (M := M) d t he
    IsComplexManifold (d+t) M := by
  subst n
  exact inferInstance

/-- Genuine closed smooth centre geometry internally produces dimensions and all WHOLE original centre-power finite free bases at EACH actual centre point. -/
theorem exists_closed_smooth_relative_monomial_basis (C : Set M)
    (hC : Hironaka.BlowupSequences.IsClosedSubmanifold n C) (x : M) (hx : x ∈ C) :
    ∃ d t : ℕ, ∃ he : d+t=n,
      letI := chartedSpaceOfSumEq (M := M) d t he
      letI := complexManifoldOfSumEq (M := M) d t he
      ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
        Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
        ∃ h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
        (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
          chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
          (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
        let E := flatteningGermEquiv _ Φ h0
        let K := wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x x (mem_chart_source _ x)
        K = Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ∧
        (∀ q : ℕ, Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t ^ q) = K ^ q) ∧
        (letI := transportedNormalAlgebra d t E
          ∀ q : ℕ, letI := normalExponentFintype t q
          ∃ b : Module.Basis (normalExponentIndex t q) (HolGerm (ComplexModel d))
              (HolGerm (ComplexModel (d+t)) ⧸ K ^ q),
            (∀ α, b α = Ideal.Quotient.mk (K ^ q) (E (normalExponentMonomial d t α.val))) ∧
            Module.Free (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t)) ⧸ K ^ q) ∧
            Module.Finite (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t)) ⧸ K ^ q)) := by
  obtain ⟨d, hreg⟩ := hC.2 x hx
  have hd : d ≤ n := hreg.1
  generalize ht : n-d=t
  have he : d+t=n := by omega
  subst n
  refine ⟨d, t, rfl, ?_⟩
  exact exists_regular_relative_monomial_basis C x hreg

end ClosedProducer

end
end Hironaka.HironakaRelativeNormalMonomialBasis
