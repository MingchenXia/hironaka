import DeJongAlterations.Projective
import Mathlib.RingTheory.ReesAlgebra

/-!
# Native affine blowups

The blowup of an ideal is the native `Proj` of Mathlib's Rees subalgebra of the polynomial ring,
with its genuine polynomial-degree grading. Its degree-zero ring is the coefficient ring.
The comparison between Proj charts and fraction subalgebras is a separate downstream result.
-/

open CategoryTheory AlgebraicGeometry Polynomial
open scoped DirectSum

noncomputable section

namespace DeJongAlterations

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The degree-`n` part of the actual Rees subalgebra consists of single monomials. -/
def reesGrading (n : ℕ) : Submodule R (reesAlgebra I) :=
  (LinearMap.range (Polynomial.monomial n)).comap (reesAlgebra I).val.toLinearMap

/-- Membership in a degree piece is equality with the actual polynomial monomial component. -/
theorem mem_reesGrading_iff (n : ℕ) (p : reesAlgebra I) :
    p ∈ reesGrading I n ↔ (p : R[X]) = monomial n ((p : R[X]).coeff n) := by
  change (∃ a : R, monomial n a = (p : R[X])) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    rw [← ha, coeff_monomial]
    simp
  · intro hp
    exact ⟨_, hp.symm⟩

/-- Every actual polynomial coefficient produces a homogeneous Rees element. -/
def reesComponent (n : ℕ) (p : reesAlgebra I) : reesGrading I n :=
  ⟨⟨monomial n ((p : R[X]).coeff n), reesAlgebra.monomial_mem.mpr (p.2 n)⟩,
    ⟨(p : R[X]).coeff n, rfl⟩⟩

@[simp]
theorem coe_reesComponent (n : ℕ) (p : reesAlgebra I) :
    ((reesComponent I n p : reesAlgebra I) : R[X]) = monomial n ((p : R[X]).coeff n) := rfl

/-- The coefficient decomposition has finite support inherited from the original polynomial. -/
def reesDecompose (p : reesAlgebra I) : ⨁ n, reesGrading I n :=
  DFinsupp.mk' (fun n => reesComponent I n p) (Trunc.mk ⟨(p : R[X]).support.val, by
    intro n
    by_cases hn : n ∈ (p : R[X]).support
    · exact Or.inl hn
    · right
      apply Subtype.ext
      apply Subtype.ext
      change monomial n ((p : R[X]).coeff n) = 0
      rw [notMem_support_iff.mp hn, map_zero]⟩)

@[simp]
theorem reesDecompose_apply (p : reesAlgebra I) (n : ℕ) :
    reesDecompose I p n = reesComponent I n p := rfl

/-- A homogeneous polynomial has zero coefficients in every other degree. -/
theorem coeff_eq_zero_of_mem_reesGrading {n m : ℕ} (p : reesGrading I n) (hmn : m ≠ n) :
    ((p : reesAlgebra I) : R[X]).coeff m = 0 := by
  rw [(mem_reesGrading_iff I n _).mp p.2, coeff_monomial]
  simp [Ne.symm hmn]

/-- Taking the `n`th polynomial coefficient selects exactly the `n`th direct summand. -/
theorem coeff_reesRecompose (p : ⨁ n, reesGrading I n) (n : ℕ) :
    (((DirectSum.coeAddMonoidHom (reesGrading I)) p : reesAlgebra I) : R[X]).coeff n =
      ((p n : reesAlgebra I) : R[X]).coeff n := by
  induction p using DirectSum.induction_on with
  | zero => simp
  | of m p =>
    by_cases hmn : m = n
    · subst m
      simp
    · rw [DirectSum.coeAddMonoidHom_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hmn)]
      exact coeff_eq_zero_of_mem_reesGrading I p (Ne.symm hmn)
  | add p q hp hq =>
    simpa only [map_add, Subalgebra.coe_add, Submodule.coe_add, coeff_add,
      DirectSum.add_apply] using congrArg₂ (· + ·) hp hq

/-- The Rees grading is multiplicative, with degrees given by the polynomial exponent. -/
instance reesGradedMonoid : SetLike.GradedMonoid (reesGrading I) where
  one_mem := ⟨1, by simp⟩
  mul_mem := by
    intro n m p q hp hq
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    change monomial n a = (p : R[X]) at ha
    change monomial m b = (q : R[X]) at hb
    refine ⟨a * b, ?_⟩
    change monomial (n + m) (a * b) = (p : R[X]) * (q : R[X])
    rw [← ha, ← hb, monomial_mul_monomial]

/-- The actual coefficient decomposition and polynomial summation are inverse functions. -/
instance reesDecomposition : DirectSum.Decomposition (reesGrading I) where
  decompose' := reesDecompose I
  left_inv p := by
    apply Subtype.ext
    apply Polynomial.ext
    intro n
    rw [coeff_reesRecompose]
    simp
  right_inv p := by
    apply DirectSum.ext
    intro n
    apply Subtype.ext
    apply Subtype.ext
    change monomial n _ = ((p n : reesAlgebra I) : R[X])
    rw [coeff_reesRecompose]
    exact ((mem_reesGrading_iff I n _).mp (p n).2).symm

/-- Mathlib's actual Rees subalgebra with its native polynomial-degree grading. -/
instance reesGradedAlgebra : GradedAlgebra (reesGrading I) where

/-- The native graded-ring projection is the original coefficient monomial. -/
theorem reesGrading_proj (p : reesAlgebra I) (n : ℕ) :
    ((GradedRing.proj (reesGrading I) n p : reesAlgebra I) : R[X]) =
      monomial n ((p : R[X]).coeff n) := rfl

/-- A generator of the ideal as a genuine degree-one Rees element. -/
def reesDegreeOne (a : R) (ha : a ∈ I) : reesAlgebra I :=
  ⟨monomial 1 a, reesAlgebra.monomial_mem.mpr (by simpa only [pow_one] using ha)⟩

/-- The ideal generators have degree one in the native grading used by Proj. -/
theorem reesDegreeOne_mem (a : R) (ha : a ∈ I) : reesDegreeOne I a ha ∈ reesGrading I 1 :=
  ⟨a, rfl⟩

/-- Constants as elements of the actual degree-zero Rees ring. -/
def reesConstants : R →+* reesGrading I 0 where
  toFun a := ⟨algebraMap R (reesAlgebra I) a, SetLike.algebraMap_mem_graded (reesGrading I) a⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- Constants identify the coefficient ring with the genuine degree-zero Rees ring. -/
theorem reesConstants_bijective : Function.Bijective (reesConstants I) := by
  constructor
  · intro a b hab
    exact Polynomial.C_injective (congrArg (fun p : reesGrading I 0 =>
      ((p : reesAlgebra I) : R[X])) hab)
  · intro p
    refine ⟨((p : reesAlgebra I) : R[X]).coeff 0, Subtype.ext (Subtype.ext ?_)⟩
    change C (((p : reesAlgebra I) : R[X]).coeff 0) = ((p : reesAlgebra I) : R[X])
    simpa only [monomial_zero_left] using ((mem_reesGrading_iff I 0 _).mp p.2).symm

/-- The coefficient ring is the actual degree-zero Rees ring, over any commutative ring. -/
def reesDegreeZeroEquiv : R ≃+* reesGrading I 0 :=
  RingEquiv.ofBijective (reesConstants I) (reesConstants_bijective I)

/-- The actual affine blowup scheme, as the projective spectrum of the Rees algebra. -/
def affineBlowup : Scheme.{u} := AlgebraicGeometry.Proj (reesGrading I)

/-- The canonical morphism from the affine blowup to the original affine scheme. -/
def affineBlowupStructure : affineBlowup I ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (reesGrading I) ≫ Spec.map (reesDegreeZeroEquiv I).toCommRingCatIso.hom

set_option backward.isDefEq.respectTransparency.types false in
/-- A finitely generated ideal has Rees algebra of finite type over its degree-zero ring. -/
theorem reesGrading_finiteType (hI : I.FG) :
    Algebra.FiniteType (reesGrading I 0) (reesAlgebra I) := by
  let : Algebra.FiniteType R (reesAlgebra I) :=
    (Subalgebra.fg_iff_finiteType _).mp (reesAlgebra.fg hI)
  apply (RingHom.finiteType_algebraMap (A := reesGrading I 0) (B := reesAlgebra I)).mp
  apply RingHom.FiniteType.of_comp_finiteType (f := reesConstants I)
  change (algebraMap R (reesAlgebra I)).FiniteType
  exact RingHom.finiteType_algebraMap.mpr inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The native affine blowup of a finitely generated ideal is proper over the original affine. -/
theorem affineBlowupStructure_isProper (hI : I.FG) : IsProper (affineBlowupStructure I) := by
  let := reesGrading_finiteType I hI
  unfold affineBlowupStructure
  infer_instance

end DeJongAlterations
