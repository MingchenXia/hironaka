/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Polynomial elimination in the node charts

The polynomial quotient algebra identities in the proof of de Jong, Proposition 3.6.
The identification with actual affine blowup charts is a separate geometric assertion.
-/

set_option autoImplicit false

namespace DeJongAlterations.Algebra.NodeChart

noncomputable section

open MvPolynomial

variable (A : Type*) [CommRing A]

/-- The three-variable presentation in the `u` chart, with variables `u,v,w`. -/
def uPresentationIdeal (t q : A) : Ideal (MvPolynomial (Fin 3) A) :=
  Ideal.span {C t - X 0 * X 2, X 1 - X 2 * C q}

/-- The two-variable presentation in the `u` chart, with variables `u,w`. -/
def uChartIdeal (t : A) : Ideal (MvPolynomial (Fin 2) A) :=
  Ideal.span {X 0 * X 1 - C t}

/-- Substitution of the dependent coordinate `v = w*q`. -/
def uSubstitution (q : A) :
    MvPolynomial (Fin 3) A →ₐ[A] MvPolynomial (Fin 2) A :=
  aeval ![X 0, X 1 * C q, X 1]

/-- Inclusion of the independent coordinates `u,w`. -/
def uInclusion : MvPolynomial (Fin 2) A →ₐ[A] MvPolynomial (Fin 3) A :=
  aeval ![X 0, X 2]

private theorem uSubstitution_ideal_le (t q : A) :
    uPresentationIdeal A t q ≤ (uChartIdeal A t).comap (uSubstitution A q) := by
  apply Ideal.span_le.mpr
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · change uSubstitution A q (C t - X 0 * X 2) ∈ uChartIdeal A t
    have h : uSubstitution A q (C t - X 0 * X 2) = -(X 0 * X 1 - C t) := by
      simp [uSubstitution]
    rw [h]
    exact (uChartIdeal A t).neg_mem (Ideal.subset_span (by simp))
  · change uSubstitution A q (X 1 - X 2 * C q) ∈ uChartIdeal A t
    simp [uSubstitution]

private theorem uInclusion_ideal_le (t q : A) :
    uChartIdeal A t ≤ (uPresentationIdeal A t q).comap (uInclusion A) := by
  apply Ideal.span_le.mpr
  intro p hp
  simp only [Set.mem_singleton_iff] at hp
  subst p
  change uInclusion A (X 0 * X 1 - C t) ∈ uPresentationIdeal A t q
  have h : uInclusion A (X 0 * X 1 - C t) = -(C t - X 0 * X 2) := by
    simp [uInclusion]
  rw [h]
  exact (uPresentationIdeal A t q).neg_mem (Ideal.subset_span (by simp))

/-- Evaluation descends to the quotient in the `u` chart. -/
def uChartForward (t q : A) :
    (MvPolynomial (Fin 3) A ⧸ uPresentationIdeal A t q) →ₐ[A]
      (MvPolynomial (Fin 2) A ⧸ uChartIdeal A t) :=
  Ideal.quotientMapₐ _ (uSubstitution A q) (uSubstitution_ideal_le A t q)

/-- Inclusion descends to the quotient in the `u` chart. -/
def uChartBackward (t q : A) :
    (MvPolynomial (Fin 2) A ⧸ uChartIdeal A t) →ₐ[A]
      (MvPolynomial (Fin 3) A ⧸ uPresentationIdeal A t q) :=
  Ideal.quotientMapₐ _ (uInclusion A) (uInclusion_ideal_le A t q)

private theorem uChart_forward_backward (t q : A) :
    (uChartForward A t q).comp (uChartBackward A t q) = AlgHom.id A _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [uChartForward, uChartBackward, uSubstitution, uInclusion]

private theorem uChart_backward_forward (t q : A) :
    (uChartBackward A t q).comp (uChartForward A t q) = AlgHom.id A _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [uChartForward, uChartBackward, uSubstitution, uInclusion]
  · simp [uChartForward, uChartBackward, uSubstitution, uInclusion]
    apply Ideal.Quotient.eq.mpr
    have hmem : X 1 - X 2 * C q ∈ uPresentationIdeal A t q :=
      Ideal.subset_span (by simp)
    convert (uPresentationIdeal A t q).neg_mem hmem using 1
    simp only [MvPolynomial.algebraMap_eq]
    ring
  · simp [uChartForward, uChartBackward, uSubstitution, uInclusion]

/-- The first polynomial quotient identity in de Jong's Proposition 3.6, over any
commutative coefficient ring, obtained by eliminating `v = w*q`. -/
def uChartEquiv (t q : A) :
    (MvPolynomial (Fin 3) A ⧸ uPresentationIdeal A t q) ≃ₐ[A]
      (MvPolynomial (Fin 2) A ⧸ uChartIdeal A t) :=
  AlgEquiv.ofAlgHom (uChartForward A t q) (uChartBackward A t q)
    (uChart_forward_backward A t q) (uChart_backward_forward A t q)

/-- The three-variable presentation in the `t` chart, with variables `u,v,z`. -/
def tPresentationIdeal (t q : A) : Ideal (MvPolynomial (Fin 3) A) :=
  Ideal.span {X 0 - C t * X 2, X 2 * X 1 - C q}

/-- The two-variable presentation in the `t` chart, with variables `v,z`. -/
def tChartIdeal (q : A) : Ideal (MvPolynomial (Fin 2) A) :=
  Ideal.span {X 1 * X 0 - C q}

/-- Substitution of the dependent coordinate `u = t*z`. -/
def tSubstitution (t : A) :
    MvPolynomial (Fin 3) A →ₐ[A] MvPolynomial (Fin 2) A :=
  aeval ![C t * X 1, X 0, X 1]

/-- Inclusion of the independent coordinates `v,z`. -/
def tInclusion : MvPolynomial (Fin 2) A →ₐ[A] MvPolynomial (Fin 3) A :=
  aeval ![X 1, X 2]

private theorem tSubstitution_ideal_le (t q : A) :
    tPresentationIdeal A t q ≤ (tChartIdeal A q).comap (tSubstitution A t) := by
  apply Ideal.span_le.mpr
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · change tSubstitution A t (X 0 - C t * X 2) ∈ tChartIdeal A q
    simp [tSubstitution]
  · change tSubstitution A t (X 2 * X 1 - C q) ∈ tChartIdeal A q
    have hmem : X 1 * X 0 - C q ∈ tChartIdeal A q := Ideal.subset_span (by simp)
    simpa [tSubstitution] using hmem

private theorem tInclusion_ideal_le (t q : A) :
    tChartIdeal A q ≤ (tPresentationIdeal A t q).comap (tInclusion A) := by
  apply Ideal.span_le.mpr
  intro p hp
  simp only [Set.mem_singleton_iff] at hp
  subst p
  change tInclusion A (X 1 * X 0 - C q) ∈ tPresentationIdeal A t q
  have hmem : X 2 * X 1 - C q ∈ tPresentationIdeal A t q := Ideal.subset_span (by simp)
  simpa [tInclusion] using hmem

/-- Evaluation descends to the quotient in the `t` chart. -/
def tChartForward (t q : A) :
    (MvPolynomial (Fin 3) A ⧸ tPresentationIdeal A t q) →ₐ[A]
      (MvPolynomial (Fin 2) A ⧸ tChartIdeal A q) :=
  Ideal.quotientMapₐ _ (tSubstitution A t) (tSubstitution_ideal_le A t q)

/-- Inclusion descends to the quotient in the `t` chart. -/
def tChartBackward (t q : A) :
    (MvPolynomial (Fin 2) A ⧸ tChartIdeal A q) →ₐ[A]
      (MvPolynomial (Fin 3) A ⧸ tPresentationIdeal A t q) :=
  Ideal.quotientMapₐ _ (tInclusion A) (tInclusion_ideal_le A t q)

private theorem tChart_forward_backward (t q : A) :
    (tChartForward A t q).comp (tChartBackward A t q) = AlgHom.id A _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [tChartForward, tChartBackward, tSubstitution, tInclusion]

private theorem tChart_backward_forward (t q : A) :
    (tChartBackward A t q).comp (tChartForward A t q) = AlgHom.id A _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [tChartForward, tChartBackward, tSubstitution, tInclusion]
    apply Ideal.Quotient.eq.mpr
    have hmem : X 0 - C t * X 2 ∈ tPresentationIdeal A t q :=
      Ideal.subset_span (by simp)
    convert (tPresentationIdeal A t q).neg_mem hmem using 1
    simp only [MvPolynomial.algebraMap_eq]
    ring
  · simp [tChartForward, tChartBackward, tSubstitution, tInclusion]
  · simp [tChartForward, tChartBackward, tSubstitution, tInclusion]

/-- The second polynomial quotient identity in de Jong's Proposition 3.6, over any
commutative coefficient ring, obtained by eliminating `u = t*z`. -/
def tChartEquiv (t q : A) :
    (MvPolynomial (Fin 3) A ⧸ tPresentationIdeal A t q) ≃ₐ[A]
      (MvPolynomial (Fin 2) A ⧸ tChartIdeal A q) :=
  AlgEquiv.ofAlgHom (tChartForward A t q) (tChartBackward A t q)
    (tChart_forward_backward A t q) (tChart_backward_forward A t q)

@[simp]
theorem uChartEquiv_mk (t q : A) (p : MvPolynomial (Fin 3) A) :
    uChartEquiv A t q (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (uSubstitution A q p) := rfl

@[simp]
theorem uChartEquiv_symm_mk (t q : A) (p : MvPolynomial (Fin 2) A) :
    (uChartEquiv A t q).symm (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (uInclusion A p) := rfl

@[simp]
theorem tChartEquiv_mk (t q : A) (p : MvPolynomial (Fin 3) A) :
    tChartEquiv A t q (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (tSubstitution A t p) := rfl

@[simp]
theorem tChartEquiv_symm_mk (t q : A) (p : MvPolynomial (Fin 2) A) :
    (tChartEquiv A t q).symm (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (tInclusion A p) := rfl

end

end DeJongAlterations.Algebra.NodeChart
