/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPointDehomogenizedInitial
import Hironaka.Resolution.HironakaActualFormalBlowupAllDirections

/-!
# Actual chart polynomial rehomogenization

Literal finite support formulas lift pivot-independent chart relations to
whole homogeneous original polynomial relations. No analytic certificate is used.
Blueprint: `hironaka-actual-polynomial-rehomogenization-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace Hironaka.HironakaActualPolynomialRehomogenization
noncomputable section
open HironakaActualPointDehomogenizedInitial HironakaActualFormalBlowupAllDirections
  HironakaActualFormalCoordinatePowerDivision
variable {n : ℕ}

/-- A literal finite sum using the actual pivot and direction parameters. -/
def actualPolynomialRehomogenization (e : Fin n) (b : Fin n → ℂ)
    (m : ℕ) (q : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ α ∈ q.support, MvPolynomial.X e ^ (m-α.degree) *
    MvPolynomial.aeval (fun i => MvPolynomial.X i-MvPolynomial.C (b i)*MvPolynomial.X e)
      (MvPolynomial.monomial α (MvPolynomial.coeff α q))

/-- Whole finite-degree rehomogenization is genuinely homogeneous. -/
theorem actualPolynomialRehomogenization_homogeneous (e : Fin n) (b : Fin n → ℂ)
    (m : ℕ) (q : MvPolynomial (Fin n) ℂ) (hq : q.totalDegree ≤ m) :
    (actualPolynomialRehomogenization e b m q).IsHomogeneous m := by
  apply MvPolynomial.IsHomogeneous.sum
  intro α hα
  have hdeg : α.degree ≤ m := (MvPolynomial.le_totalDegree hα).trans hq
  have hlin (i : Fin n) :
      (MvPolynomial.X i-MvPolynomial.C (b i)*MvPolynomial.X e : MvPolynomial (Fin n) ℂ).IsHomogeneous 1 :=
    (MvPolynomial.isHomogeneous_X ℂ i).sub (MvPolynomial.isHomogeneous_C_mul_X (b i) e)
  have hmon := (MvPolynomial.isHomogeneous_monomial (d := α) (MvPolynomial.coeff α q) rfl).aeval _ hlin
  have hprod := (MvPolynomial.isHomogeneous_X_pow e (m-α.degree)).mul hmon
  simpa only [one_mul,Nat.sub_add_cancel hdeg] using hprod

/-- The same actual dehomogenization recovers EVERY original finite coefficient. -/
theorem actualPointDehomogenization_rehomogenization (e : Fin n) (b : Fin n → ℂ)
    (m : ℕ) (q : MvPolynomial (Fin n) ℂ)
    (hpivot : ∀ α ∈ q.support, α e = 0) :
    actualPointDehomogenization e b (actualPolynomialRehomogenization e b m q) = q := by
  rw [actualPolynomialRehomogenization,map_sum]
  conv_rhs => rw [← q.support_sum_monomial_coeff]
  apply Finset.sum_congr rfl
  intro α hα
  rw [map_mul,map_pow]
  have he : actualPointDehomogenization e b (MvPolynomial.X e) = 1 := by
    simp [actualPointDehomogenization]
  rw [he,one_pow,one_mul,MvPolynomial.aeval_monomial,MvPolynomial.monomial_eq]
  simp only [Finsupp.prod,map_mul,map_prod,map_pow,AlgHom.commutes]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hie : i ≠ e := by
    intro h
    subst i
    exact (Finsupp.mem_support_iff.mp hi) (hpivot α hα)
  simp [actualPointDehomogenization,hie]

/-- In a fixed degree, true formal blowup injectivity forces whole polynomial injectivity. -/
theorem actualPointDehomogenization_homogeneous_injective (e : Fin n) (b : Fin n → ℂ)
    (D : ℕ) (P Q : MvPolynomial (Fin n) ℂ) (hP : P.IsHomogeneous D) (hQ : Q.IsHomogeneous D)
    (h : actualPointDehomogenization e b P = actualPointDehomogenization e b Q) : P = Q := by
  apply MvPolynomial.coe_injective (R := ℂ)
  apply actualFormalBlowup_injective Set.univ e (mem_univ e) b
  rw [actualFormalBlowup_homogeneous_polynomial e b P D hP,
    actualFormalBlowup_homogeneous_polynomial e b Q D hQ,h]

/-- A natural finite degree bound and a literal pivot-independent polynomial
chart relation produce a true homogeneous original relation at that degree. -/
theorem homogeneous_polynomial_relation_lift_at_degree {ι : Type*} [Fintype ι]
    (e : Fin n) (b : Fin n → ℂ) (f q : ι → MvPolynomial (Fin n) ℂ) (w : ι → ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (w i))
    (hq : ∀ i α, α ∈ (q i).support → α e = 0)
    (hrel : (∑ i, q i * actualPointDehomogenization e b (f i)) = 0)
    (D : ℕ) (hD : ∀ i, w i + (q i).totalDegree ≤ D) :
    ∃ P : ι → MvPolynomial (Fin n) ℂ,
      (∀ i, (P i).IsHomogeneous (D-w i)) ∧
      (∀ i, actualPointDehomogenization e b (P i) = q i) ∧
      (∑ i, P i * f i) = 0 := by
  let P := fun i => actualPolynomialRehomogenization e b (D-w i) (q i)
  have hhom (i : ι) : (P i).IsHomogeneous (D-w i) := by
    apply actualPolynomialRehomogenization_homogeneous
    have := hD i
    omega
  have heval (i : ι) : actualPointDehomogenization e b (P i) = q i :=
    actualPointDehomogenization_rehomogenization e b (D-w i) (q i) (hq i)
  refine ⟨P,hhom,heval,?_⟩
  have hsum : (∑ i, P i * f i).IsHomogeneous D := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i _
    have hw : w i ≤ D := (Nat.le_add_right _ _).trans (hD i)
    simpa only [Nat.sub_add_cancel hw] using (hhom i).mul (hf i)
  apply actualPointDehomogenization_homogeneous_injective e b D _ 0 hsum
    (MvPolynomial.isHomogeneous_zero (Fin n) ℂ D)
  simpa only [map_sum,map_mul,heval,map_zero] using hrel

/-- One internally chosen common degree lifts EVERY given finite original
pivot-independent chart relation; no homogeneous output is a premise. -/
theorem exists_homogeneous_polynomial_relation_lift {ι : Type*} [Fintype ι]
    (e : Fin n) (b : Fin n → ℂ) (f q : ι → MvPolynomial (Fin n) ℂ) (w : ι → ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (w i))
    (hq : ∀ i α, α ∈ (q i).support → α e = 0)
    (hrel : (∑ i, q i * actualPointDehomogenization e b (f i)) = 0) :
    ∃ (D : ℕ) (P : ι → MvPolynomial (Fin n) ℂ),
      (∀ i, w i ≤ D) ∧ (∀ i, (P i).IsHomogeneous (D-w i)) ∧
      (∀ i, actualPointDehomogenization e b (P i) = q i) ∧ (∑ i, P i * f i) = 0 := by
  let D := ∑ i, (w i + (q i).totalDegree)
  have hD (i : ι) : w i + (q i).totalDegree ≤ D := by
    change w i + (q i).totalDegree ≤ ∑ j, (w j + (q j).totalDegree)
    exact Finset.single_le_sum (f := fun j : ι => w j + (q j).totalDegree)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  obtain ⟨P,hP,heval,hwhole⟩ := homogeneous_polynomial_relation_lift_at_degree e b f q w hf hq hrel D hD
  exact ⟨D,P,fun i => (Nat.le_add_right _ _).trans (hD i),hP,heval,hwhole⟩

end
end Hironaka.HironakaActualPolynomialRehomogenization
