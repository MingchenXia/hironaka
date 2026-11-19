import Hironaka.Algebra.ProjectiveIdealChartAlgebra
import Hironaka.Algebra.ProjectiveSecantTangentLinearForm
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Exact original polynomial differentials and coordinate dehomogenization
-/

noncomputable section

open MvPolynomial

namespace Hironaka.Algebra.ProjectiveSecant

open Geometry.ProjectiveIdeal

/- The derivation chain-rule proof is adapted from
EnvelopeProperty/EnvelopeProperty/Char0/AnalyticChartLocal.lean:92--112,
SHA256 fe395d48344687728244bba8e080c1816a8bf7b2e694a417f651ea3c6cff15ae.
The argument uses an arbitrary commutative coefficient ring, not characteristic zero. -/

/-- The literal whole polynomial substitution obeys the exact original chain rule over arbitrary coefficient rings. -/
theorem original_derivation_aeval {R S I : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Fintype I] (D : Derivation R S S)
    (v : I → S) (P : MvPolynomial I R) :
    D (aeval v P) = ∑ i, aeval v (pderiv i P) * D (v i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P o hP =>
    have h1 : ∀ i, aeval v (pderiv i (P * X o)) =
        v o * aeval v (pderiv i P) + if o = i then aeval v P else 0 := by
      intro i
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X,
        Pi.single_apply]
      split_ifs <;> simp [mul_comm, add_comm]
    rw [Finset.sum_congr rfl fun i _ => by rw [h1 i]]
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hP, add_mul,
      Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.mul_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Original partial differentiation in any actual remaining coordinate commutes with the whole original coordinate dehomogenization. -/
theorem original_pderiv_coordinateDehom (j : Fin (n + 1))
    (l : ChartIndex j) (H : MvPolynomial (Fin (n + 1)) R) :
    pderiv l (coordinateDehom j H) = coordinateDehom j (pderiv l.val H) := by
  classical
  change pderiv l (aeval (coordinateDehomCoord j) H) = _
  rw [original_derivation_aeval]
  have hcoord (m : Fin (n + 1)) :
      pderiv l (coordinateDehomCoord (R := R) j m) = if m = l.val then 1 else 0 := by
    by_cases hm : m = j
    · subst m
      simp [Ne.symm l.property]
    · change pderiv l (if h : m = j then 1 else X ⟨m, h⟩) = _
      simp only [dif_neg hm, pderiv_X, Pi.single_apply]
      have he : (⟨m, hm⟩ : ChartIndex j) = l ↔ m = l.val := by
        constructor
        · intro h
          exact congrArg Subtype.val h
        · intro h
          exact Subtype.ext h
      exact if_congr he rfl rfl
  simp only [hcoord, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rfl

end Hironaka.Algebra.ProjectiveSecant
