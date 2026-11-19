import Hironaka.Analytic.Unibranch.HironakaG10TruncatedParameterResidue
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10FiniteParameterNorm
noncomputable section

/-- Concrete compatible norm structures, with the original ring and
complex algebra operations definitionally unchanged. -/
abbrev normedComplexAlgebraData (A : Type) [CommRing A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] :
    Σ R : NormedCommRing A, {N : @NormedAlgebra ℂ A _ R.toSeminormedRing //
      HEq N.toAlgebra (inferInstance : Algebra ℂ A)} := by
  let b := Module.finBasis ℂ A
  let e := b.equivFun
  let : NormedAddCommGroup A := NormedAddCommGroup.induced A _ e.toAddMonoidHom e.injective
  let : NormedSpace ℂ A := NormedSpace.induced ℂ A _ e.toLinearMap
  let ρ : A →ₐ[ℂ] (A →L[ℂ] A) := {
    toFun := fun a => LinearMap.toContinuousLinearMap ((Algebra.lmul ℂ A) a)
    map_one' := by ext x; simp
    map_mul' := by intro a b; ext x; simp [mul_assoc]
    map_zero' := by ext x; simp
    map_add' := by intro a b; ext x; simp
    commutes' := by intro c; ext x; simp }
  have hρ : Function.Injective ρ := by
    intro a b h
    have h1 := congrArg (fun f : A →L[ℂ] A => f 1) h
    simpa [ρ] using h1
  refine ⟨NormedCommRing.induced A _ ρ hρ, ⟨NormedAlgebra.induced ℂ A _ ρ, ?_⟩⟩
  apply heq_of_eq
  rfl

/-- A finite dimensional complex algebra has a submultiplicative norm. -/
theorem exists_normed_complex_algebra (A : Type) [CommRing A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] :
    ∃ (R : NormedCommRing A), R.toCommRing = (inferInstance : CommRing A) ∧
      ∃ (N : @NormedAlgebra ℂ A _ R.toSeminormedRing),
        HEq N.toAlgebra (inferInstance : Algebra ℂ A) := by
  exact ⟨(normedComplexAlgebraData A).1, rfl, (normedComplexAlgebraData A).2.1, (normedComplexAlgebraData A).2.2⟩
open Hironaka Hironaka
  HironakaHolomorphicPointJets

local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra

/-- The norm can be chosen on the literal holomorphic-germ quotient,
with the quotient ring and scalar structures unchanged. -/
theorem truncated_parameter_norm (n q : ℕ) (I : Ideal (HolGerm (ComplexModel n))) :
    let Q := HolGerm (ComplexModel n) ⧸
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)
    ∃ (R : NormedCommRing Q), R.toCommRing = (inferInstance : CommRing Q) ∧
      ∃ (N : @NormedAlgebra ℂ Q _ R.toSeminormedRing),
        HEq N.toAlgebra (inferInstance : Algebra ℂ Q) := by
  let := finiteDimensional_quotient_sup_maximalIdeal_pow n q I
  exact exists_normed_complex_algebra _
end
end Hironaka.Analytic.Unibranch.HironakaG10FiniteParameterNorm
