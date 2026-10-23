import DeJongAlterations.Algebra.AffinePrimeDimensionGeneric

/-!
# The genuine finite-type field prime dimension formula

Lift the actual Noether normalization of the original quotient and
localize at its nonzero coefficient polynomials. The genuine generic
tensor quotient is a field; its native maximal height gives the whole
original prime height. Additivity of actual transcendence degree then
proves the dimension formula, without a catenarity certificate.
-/

noncomputable section

open scoped TensorProduct

namespace DeJongAlterations.Algebra.AffinePrimeDimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (k A : Type u) [Field k] [CommRing A] [IsDomain A]
  [Algebra k A] [Algebra.FiniteType k A] (p : Ideal A) [p.IsPrime]

omit [IsDomain A] [Algebra.FiniteType k A] [p.IsPrime] in
/-- The original polynomial map into a quotient genuinely lifts to the original ring. -/
theorem exists_polynomial_lift {n : ℕ} (α : MvPolynomial (Fin n) k →ₐ[k] A ⧸ p) :
    ∃ β : MvPolynomial (Fin n) k →ₐ[k] A,
      (Ideal.Quotient.mkₐ k p).comp β = α := by
  choose x hx using fun i : Fin n => Ideal.Quotient.mk_surjective (α (MvPolynomial.X i))
  refine ⟨MvPolynomial.aeval x, ?_⟩
  ext i
  simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk] using hx i

include k in
set_option maxHeartbeats 800000 in
/-- The actual prime height plus the actual original quotient dimension is the domain dimension. -/
theorem height_add_quotient_dimension :
    (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) = ringKrullDim A := by
  obtain ⟨n, α, hα, hfin⟩ := exists_finite_inj_algHom_of_fg k (A ⧸ p)
  obtain ⟨β, hβ⟩ := exists_polynomial_lift k A p α
  let P := MvPolynomial (Fin n) k
  let F := FractionRing P
  let K := FractionRing A
  let : Algebra P A := β.toRingHom.toAlgebra
  let : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' β.comp_algebraMap.symm
  let : Algebra.FiniteType P A := Algebra.FiniteType.of_restrictScalars_finiteType k P A
  let : Module.Finite P (A ⧸ p) := by
    change ((Ideal.Quotient.mkₐ k p).comp β).Finite
    rw [hβ]
    exact hfin
  have hcoeff : Function.Injective (algebraMap P (A ⧸ p)) := by
    change Function.Injective ((Ideal.Quotient.mkₐ k p).comp β)
    rw [hβ]
    exact hα
  have hPA : Function.Injective (algebraMap P A) := by
    intro a b h
    apply hcoeff
    exact congrArg (algebraMap A (A ⧸ p)) h
  let : Algebra.IsIntegral P (A ⧸ p) := Algebra.IsIntegral.of_finite P (A ⧸ p)
  have hQdim : ringKrullDim (A ⧸ p) = n := by
    have hu := FunctionFieldDimension.ringKrullDim_le_of_isIntegral
      (algebraMap P (A ⧸ p)) (algebraMap_isIntegral_iff.mpr inferInstance)
    have hl := FunctionFieldDimension.ringKrullDim_le_of_isIntegral_of_injective
      (algebraMap P (A ⧸ p)) (algebraMap_isIntegral_iff.mpr inferInstance) hcoeff
    have hPdim : ringKrullDim P = n := by
      simp only [P, MvPolynomial.ringKrullDim_of_isNoetherianRing,
        Nat.card_eq_fintype_card, Fintype.card_fin, ringKrullDim_eq_zero_of_field, zero_add]
    exact (le_antisymm hu hl).trans hPdim
  let : IsScalarTower P A K := inferInstance
  let : IsScalarTower k P K := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap k K a = algebraMap A K (β (algebraMap k P a))
    rw [β.commutes]
    exact IsScalarTower.algebraMap_apply k A K a
  let := FunctionFieldDimension.coefficientFractionAlgebra P A F K hPA
  let := FunctionFieldDimension.coefficientFractionScalarTower P A F K hPA
  let : IsScalarTower k F K := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k P F,
      ← IsScalarTower.algebraMap_apply P F K,
      ← IsScalarTower.algebraMap_apply k P K]
  let B := F ⊗[P] A
  let : IsDomain B := FunctionFieldDimension.genericTensor_isDomain P A F hPA
  let := FunctionFieldDimension.genericTensorAlgebra P A F K hPA
  let := FunctionFieldDimension.genericTensorScalarTowerLeft P A F K hPA
  let : IsFractionRing B K := FunctionFieldDimension.genericTensor_isFractionRing P A F K hPA
  obtain ⟨m, hBdim, hrel⟩ := FunctionFieldDimension.exists_dimension_and_trdeg F B K
  have hpheight : (p.height : WithBot ℕ∞) = m :=
    (genericTensor_dimension_eq_height P A F p hcoeff).symm.trans hBdim
  have hF : Algebra.trdeg k F = n := by
    let : Algebra.IsAlgebraic P F := IsLocalization.isAlgebraic F (nonZeroDivisors P)
    let : FaithfulSMul P F :=
      (faithfulSMul_iff_algebraMap_injective P F).mpr (IsFractionRing.injective P F)
    have ht := FunctionFieldDimension.trdeg_eq_of_isAlgebraic k P F
    simpa only [P, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype,
      Fintype.card_fin, Cardinal.lift_natCast] using ht.symm
  obtain ⟨d, hAdim, hK⟩ := FunctionFieldDimension.exists_dimension_and_trdeg k A K
  have hsum := trdeg_add_eq k F (A := K)
  rw [hF, hrel, hK] at hsum
  have hnat : n + m = d := by exact_mod_cast hsum
  rw [hpheight, hQdim, hAdim, ← hnat]
  exact_mod_cast Nat.add_comm m n

include k in
/-- The height-one component bound needed by the actual nonflat Cartier boundary. -/
theorem dimension_le_quotient_dimension_add_one (hp : p.height ≤ 1) :
    ringKrullDim A ≤ ringKrullDim (A ⧸ p) + 1 := by
  rw [← height_add_quotient_dimension k A p]
  have hh : (p.height : WithBot ℕ∞) ≤ 1 := by exact_mod_cast hp
  calc
    (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) ≤ 1 + ringKrullDim (A ⧸ p) :=
      add_le_add hh le_rfl
    _ = _ := add_comm _ _

end DeJongAlterations.Algebra.AffinePrimeDimension
