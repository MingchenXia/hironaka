/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalActualHSConvolution
import Hironaka.Resolution.HironakaRelativeNormalMonomialBasis

/-! Whole original product ideals and genuine coefficient quotient coordinates.
The cutoff is the actual free-coordinate ideal power, before mixed ambient HS.
-/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualProductTruncatedQuotient
noncomputable section

section OriginalAlgebra
variable {B R : Type*} [CommRing B] [CommRing R] [Algebra B R]

/-- The whole original extended ideal acts by its actual original scalar action in the true quotient. -/
theorem actualExtendedIdealImage (I : Ideal B) (K : Ideal R) :
    (Ideal.map (Ideal.Quotient.mk K) (Ideal.map (algebraMap B R) I)).restrictScalars B =
      I • (⊤ : Submodule B (R ⧸ K)) := by
  have hm : Ideal.map (Ideal.Quotient.mk K) (Ideal.map (algebraMap B R) I) =
      Ideal.map (algebraMap B (R ⧸ K)) I := by
    rw [Ideal.map_map]
    rfl
  rw [hm]
  simp

/-- Genuine whole extension-ideal quotient, retaining both actual quotient projections. -/
def actualExtendedIdealQuotientEquiv (I : Ideal B) (K : Ideal R) :
    (R ⧸ (Ideal.map (algebraMap B R) I ⊔ K)) ≃ₗ[B]
      ((R ⧸ K) ⧸ (I • (⊤ : Submodule B (R ⧸ K)))) := by
  let J := Ideal.map (Ideal.Quotient.mk K) (Ideal.map (algebraMap B R) I)
  let e : (((R ⧸ K) ⧸ (I • (⊤ : Submodule B (R ⧸ K))))) ≃+
      ((R ⧸ K) ⧸ J) :=
    (Submodule.quotEquivOfEq _ _ (actualExtendedIdealImage I K).symm).toAddEquiv
  let E : (((R ⧸ K) ⧸ (I • (⊤ : Submodule B (R ⧸ K))))) ≃ₗ[B]
      ((R ⧸ K) ⧸ J) := by
    refine { e with map_smul' := ?_ }
    intro b z
    obtain ⟨g,rfl⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule B (R ⧸ K))) z
    change Ideal.Quotient.mk J (b • g) = b • Ideal.Quotient.mk J g
    exact (Ideal.Quotient.mkₐ B J).toLinearMap.map_smul b g
  exact (Ideal.quotientEquivAlgOfEq B (sup_comm (Ideal.map (algebraMap B R) I) K)).toLinearEquiv.trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ B K (Ideal.map (algebraMap B R) I)).toLinearEquiv.symm.trans E.symm)

/-- Every actual original numerator retains its same true double-quotient class. -/
theorem actualExtendedIdealQuotientEquiv_mk (I : Ideal B) (K : Ideal R) (g : R) :
    actualExtendedIdealQuotientEquiv I K
      (Ideal.Quotient.mk (Ideal.map (algebraMap B R) I ⊔ K) g) =
        Submodule.Quotient.mk (Ideal.Quotient.mk K g) := by
  rfl
end OriginalAlgebra

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalActualHSConvolution

section ActualProduct
variable (d t s : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t
local instance : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  IsScalarTower.of_algHom (tangentPullback d t)
local instance : Fintype (normalExponentIndex t s) := normalExponentFintype t s

/-- The genuine product coefficient dictionary preserves the entire original scalar-ideal multiple. -/
theorem actualNormalPowerCoefficientIdeal (I : Ideal (HolGerm (ComplexModel d))) :
    (I • (⊤ : Submodule (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t ^ s))).map
        (normalPowerLinearEquiv d t s).symm.toLinearMap =
      Submodule.pi Set.univ (fun _ : normalExponentIndex t s => I) := by
  rw [Submodule.map_smul'',Submodule.map_top,LinearEquiv.range,actualCoefficientIdeal]

/-- The whole original product truncation uses exactly the true original coefficient quotients. -/
def actualProductTruncationEquiv (I : Ideal (HolGerm (ComplexModel d))) :
    (HolGerm (ComplexModel (d+t)) ⧸
      (Ideal.map (tangentPullback d t).toRingHom I ⊔ normalIdeal d t ^ s)) ≃ₗ[HolGerm (ComplexModel d)]
        (normalExponentIndex t s → HolGerm (ComplexModel d) ⧸ I) :=
  (actualExtendedIdealQuotientEquiv I (normalIdeal d t ^ s)).trans
    ((Submodule.Quotient.equiv _ _ (normalPowerLinearEquiv d t s).symm
      (actualNormalPowerCoefficientIdeal d t s I)).trans (Submodule.quotientPi (fun _ : normalExponentIndex t s => I)))

/-- Every original finite polynomial keeps exactly its actual whole coefficient quotient classes. -/
theorem actualProductTruncationEquiv_monomial_sum (I : Ideal (HolGerm (ComplexModel d)))
    (a : normalExponentIndex t s → HolGerm (ComplexModel d)) :
    actualProductTruncationEquiv d t s I
      (Ideal.Quotient.mk (Ideal.map (tangentPullback d t).toRingHom I ⊔ normalIdeal d t ^ s)
        (normalPolynomialEval d t (∑ α : normalExponentIndex t s, MvPolynomial.monomial α.val (a α)))) =
      fun α => Ideal.Quotient.mk I (a α) := by
  change (Submodule.quotientPi (fun _ : normalExponentIndex t s => I))
    (Submodule.Quotient.mk ((normalPowerLinearEquiv d t s).symm
      (Ideal.Quotient.mk (normalIdeal d t ^ s)
        (normalPolynomialEval d t (∑ α : normalExponentIndex t s, MvPolynomial.monomial α.val (a α)))))) = _
  rw [← normalMonomialCombination_apply]
  change (Submodule.quotientPi (fun _ : normalExponentIndex t s => I))
    (Submodule.Quotient.mk ((normalPowerLinearEquiv d t s).symm ((normalPowerLinearEquiv d t s) a))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- BOTH genuine original whole coefficient directions characterize the actual product ideal. -/
theorem actualProductPolynomial_mem_iff (I : Ideal (HolGerm (ComplexModel d)))
    (a : normalExponentIndex t s → HolGerm (ComplexModel d)) :
    normalPolynomialEval d t (∑ α : normalExponentIndex t s, MvPolynomial.monomial α.val (a α)) ∈
      Ideal.map (tangentPullback d t).toRingHom I ⊔ normalIdeal d t ^ s ↔ ∀ α, a α ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem,← (actualProductTruncationEquiv d t s I).map_eq_zero_iff,
    actualProductTruncationEquiv_monomial_sum]
  constructor
  · intro h α
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun h α)
  · intro h
    funext α
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h α)

/-- The literal product cutoff quotient has the true original complex dimension. -/
theorem actualProductTruncationDimension (I : Ideal (HolGerm (ComplexModel d)))
    [Module.Finite ℂ (HolGerm (ComplexModel d) ⧸ I)] :
    Module.finrank ℂ (HolGerm (ComplexModel (d+t)) ⧸
      (Ideal.map (tangentPullback d t).toRingHom I ⊔ normalIdeal d t ^ s)) =
        Fintype.card (normalExponentIndex t s) * Module.finrank ℂ (HolGerm (ComplexModel d) ⧸ I) := by
  rw [((actualProductTruncationEquiv d t s I).restrictScalars ℂ).finrank_eq,
    Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  simp only [Nat.cast_id]

/-- The genuine whole complex quotient is finite because its actual coefficient factors are finite. -/
theorem actualProductTruncationFinite (I : Ideal (HolGerm (ComplexModel d)))
    [Module.Finite ℂ (HolGerm (ComplexModel d) ⧸ I)] :
    Module.Finite ℂ (HolGerm (ComplexModel (d+t)) ⧸
      (Ideal.map (tangentPullback d t).toRingHom I ⊔ normalIdeal d t ^ s)) :=
  FiniteDimensional.of_injective ((actualProductTruncationEquiv d t s I).restrictScalars ℂ).toLinearMap
    (actualProductTruncationEquiv d t s I).injective

end ActualProduct
end
end Hironaka.HironakaActualProductTruncatedQuotient
