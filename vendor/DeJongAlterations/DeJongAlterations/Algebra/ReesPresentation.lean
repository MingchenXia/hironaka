import DeJongAlterations.Geometry.AffineBlowup
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.AlgHom
import Mathlib.Data.Fin.Tuple.Basic

/-!
# A graded polynomial presentation of the actual Rees algebra

Ideal generators give degree-one Rees elements and hence an explicit graded polynomial map.
When the generators span the ideal, homogeneous lifts of its powers prove surjectivity.
Finite generation yields a presentation with a nonempty finite set of variables.
-/

open MvPolynomial Polynomial
open scoped DirectSum

noncomputable section

namespace DeJongAlterations.Algebra.ReesPresentation

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R) {σ : Type v}
    (g : σ → R) (hg : ∀ i, g i ∈ I)

/-- Actual polynomial evaluation in the degree-one Rees elements of the ideal generators. -/
def reesPolynomialEval : MvPolynomial σ R →ₐ[R] reesAlgebra I :=
  MvPolynomial.aeval fun i => reesDegreeOne I (g i) (hg i)

/-- Evaluation in degree-one Rees elements preserves every homogeneous degree. -/
theorem reesPolynomialEval_mem {n : ℕ} {P : MvPolynomial σ R} (hP : P.IsHomogeneous n) :
    reesPolynomialEval I g hg P ∈ reesGrading I n := by
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => exact (reesGrading I n).zero_mem
  | add P Q _ _ hP hQ =>
    simpa only [map_add] using (reesGrading I n).add_mem hP hQ
  | monomial d r hd =>
    have hd' : d.degree = n := by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
    rw [reesPolynomialEval, MvPolynomial.aeval_monomial, ← hd', ← zero_add d.degree]
    apply SetLike.mul_mem_graded (SetLike.algebraMap_mem_graded (reesGrading I) r)
    simpa only [Finsupp.prod, Finsupp.degree_apply, smul_eq_mul, mul_one] using
      (SetLike.prod_pow_mem_graded (reesGrading I) (fun _ : σ => (1 : ℕ))
        (fun i => reesDegreeOne I (g i) (hg i)) (fun i => d i)
        (fun i _ => reesDegreeOne_mem I (g i) (hg i)))

/-- The genuine graded map, with its grading proof constructed from degree-one evaluation. -/
def reesPolynomialMap :
    GradedAlgHom R (MvPolynomial.homogeneousSubmodule σ R) (reesGrading I) where
  __ := reesPolynomialEval I g hg
  map_mem := reesPolynomialEval_mem I g hg

/-- Evaluation at one recovers the original evaluation in the coefficients. -/
theorem eval_one_reesPolynomialEval (P : MvPolynomial σ R) :
    Polynomial.aeval (1 : R) ((reesPolynomialEval I g hg P : reesAlgebra I) : R[X]) =
      MvPolynomial.eval g P := by
  have H : (Polynomial.aeval (1 : R)).comp
      ((reesAlgebra I).val.comp (reesPolynomialEval I g hg)) = MvPolynomial.aeval g := by
    ext i
    simp [reesPolynomialEval, reesDegreeOne]
  simpa only [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval, Subalgebra.val_apply] using AlgHom.congr_fun H P

/-- A homogeneous polynomial maps to its evaluated coefficient in the actual Rees degree. -/
theorem coe_reesPolynomialEval_of_isHomogeneous {n : ℕ} {P : MvPolynomial σ R}
    (hP : P.IsHomogeneous n) :
    ((reesPolynomialEval I g hg P : reesAlgebra I) : R[X]) =
      Polynomial.monomial n (MvPolynomial.eval g P) := by
  have H := (mem_reesGrading_iff I n _).mp (reesPolynomialEval_mem I g hg hP)
  have H1 := eval_one_reesPolynomialEval I g hg P
  rw [H] at H1
  simp only [Polynomial.aeval_monomial, Algebra.algebraMap_self_apply, one_pow, mul_one] at H1
  exact H.trans (congrArg (Polynomial.monomial n) H1)

/-- Every coefficient in an ideal power has a genuine homogeneous polynomial preimage. -/
theorem exists_homogeneous_preimage_monomial (hspan : Ideal.span (Set.range g) = I)
    (n : ℕ) (a : R) (ha : a ∈ I ^ n) :
    ∃ P : MvPolynomial σ R, P.IsHomogeneous n ∧
      ((reesPolynomialEval I g hg P : reesAlgebra I) : R[X]) = Polynomial.monomial n a := by
  rw [← hspan] at ha
  obtain ⟨P, hP, heval⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous g a).mp ha
  exact ⟨P, hP, (coe_reesPolynomialEval_of_isHomogeneous I g hg hP).trans
    (congrArg (Polynomial.monomial n) heval)⟩

/-- The actual graded polynomial map is surjective whenever the family generates the ideal. -/
theorem reesPolynomialMap_surjective (hspan : Ideal.span (Set.range g) = I) :
    Function.Surjective (reesPolynomialMap I g hg) := by
  classical
  intro p
  have H (n : ℕ) := exists_homogeneous_preimage_monomial I g hg hspan n
    ((p : R[X]).coeff n) (p.2 n)
  choose P hP heval using H
  refine ⟨∑ n ∈ (p : R[X]).support, P n, ?_⟩
  apply Subtype.ext
  change (reesAlgebra I).val (reesPolynomialEval I g hg
    (∑ n ∈ (p : R[X]).support, P n)) = (p : R[X])
  rw [map_sum, map_sum]
  exact (Finset.sum_congr rfl fun n _ => heval n).trans (p : R[X]).as_sum_support.symm

/-- Finite generation supplies a nonempty finite generating family by adjoining zero. -/
theorem exists_fin_succ_generators (hI : I.FG) :
    ∃ (n : ℕ) (g : Fin (n + 1) → R), (∀ i, g i ∈ I) ∧ Ideal.span (Set.range g) = I := by
  obtain ⟨n, g, hspan⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  have hspan' : Ideal.span (Set.range (Fin.cons (0 : R) g)) = I := by
    rw [Fin.range_cons, Ideal.span_insert_zero]
    exact hspan
  exact ⟨n, Fin.cons 0 g, fun i => hspan' ▸ Ideal.subset_span ⟨i, rfl⟩, hspan'⟩

/-- A finitely generated ideal has an actual surjective graded polynomial presentation. -/
theorem exists_surjective_gradedPolynomialMap (hI : I.FG) :
    ∃ (n : ℕ) (φ : GradedAlgHom R
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (reesGrading I)),
      Function.Surjective φ := by
  obtain ⟨n, g, hg, hspan⟩ := exists_fin_succ_generators I hI
  exact ⟨n, reesPolynomialMap I g hg, reesPolynomialMap_surjective I g hg hspan⟩

end DeJongAlterations.Algebra.ReesPresentation
