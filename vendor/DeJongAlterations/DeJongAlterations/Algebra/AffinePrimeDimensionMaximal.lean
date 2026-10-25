import DeJongAlterations.Algebra.FunctionFieldDimension
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Actual maximal heights in finite-type domains over fields

Pure proof extraction from EnvelopeProperty/AffineDimension.lean:
actual Noether normalization and normal-base going down identify every
maximal height with the original domain's full Krull dimension.
Only the algebraic Mathlib cone is imported.
-/

noncomputable section

namespace DeJongAlterations.Algebra.AffinePrimeDimension

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Integral incomparability removes the fiber height from the actual going-down formula. -/
theorem height_eq_under_of_isIntegral_of_hasGoingDown
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.IsIntegral R A] [Algebra.HasGoingDown R A]
    (P : Ideal A) [P.IsPrime] : P.height = (P.under R).height := by
  let I : Ideal A := (P.under R).map (algebraMap R A)
  have hm : P ∈ I.minimalPrimes := Ideal.IsIntegral.mem_minimalPrimes_map_under P
  rw [Ideal.minimalPrimes_eq_comap] at hm
  obtain ⟨q, hq, he⟩ := hm
  have : q.IsPrime := hq.isPrime
  have hmap : P.map (Ideal.Quotient.mk I) = q := by
    rw [← he, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hz : (P.map (Ideal.Quotient.mk I)).height = 0 := by
    rw [hmap]
    exact Ideal.height_eq_zero_iff.mpr hq
  have ht := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under R) P
  rw [hz, add_zero] at ht
  exact ht

/-- Each maximal polynomial prime over a field has exactly the number of coordinate heights. -/
theorem maximalHeight_mvPolynomialFin (k : Type*) [Field k] (n : ℕ)
    (M : Ideal (MvPolynomial (Fin n) k)) [M.IsMaximal] : M.height = (n : ℕ) := by
  induction n with
  | zero =>
    let e := (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toRingEquiv
    have : (M.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    rw [← e.height_map M]
    apply bot_unique
    have ht := Ideal.height_le_ringKrullDim_of_isPrime (I := M.map e)
    have hz : ((M.map e).height : WithBot ℕ∞) ≤ ((0 : ℕ∞) : WithBot ℕ∞) := by
      simpa only [ringKrullDim_eq_zero_of_field, WithBot.coe_zero] using ht
    exact WithBot.coe_le_coe.mp hz
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let P := M.map e
    have : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let p := P.under (MvPolynomial (Fin n) k)
    have : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    rw [← e.height_map M]
    change P.height = (n + 1 : ℕ)
    rw [Polynomial.height_eq_height_add_one p P, ih p]
    simp only [Nat.cast_add, Nat.cast_one]

/-- Actual Noether normalization internally gives one common finite maximal height. -/
theorem exists_constant_maximalHeight (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ n : ℕ, ∀ (M : Ideal A), M.IsMaximal → M.height = (n : ℕ) := by
  obtain ⟨n, f, hf, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let : Algebra P A := f.toRingHom.toAlgebra
  have : Module.Finite P A := hfin
  have : Algebra.IsIntegral P A := Algebra.IsIntegral.of_finite P A
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hf
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine ⟨n, ?_⟩
  intro M hM
  have : M.IsMaximal := hM
  have : (M.under P).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := P) M
  rw [height_eq_under_of_isIntegral_of_hasGoingDown (R := P) M]
  exact maximalHeight_mvPolynomialFin k n (M.under P)

/-- Every actual maximal ideal of a finite-type field domain has its full original dimension. -/
theorem maximalHeight_eq_ringKrullDim (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (M : Ideal A) [M.IsMaximal] :
    (M.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨n, hn⟩ := exists_constant_maximalHeight k A
  have hu : ringKrullDim A ≤ (n : WithBot ℕ∞) := by
    apply (ringKrullDim_le_iff_isMaximal_height_le _).mpr
    intro N hN
    rw [hn N hN]
    exact le_refl _
  have hl : (n : WithBot ℕ∞) ≤ ringKrullDim A := by
    have h := Ideal.height_le_ringKrullDim_of_isPrime (I := M)
    rw [hn M inferInstance] at h
    exact h
  have hd : ringKrullDim A = (n : WithBot ℕ∞) := le_antisymm hu hl
  rw [hn M inferInstance, hd]
  exact WithBot.coe_natCast n

end DeJongAlterations.Algebra.AffinePrimeDimension
