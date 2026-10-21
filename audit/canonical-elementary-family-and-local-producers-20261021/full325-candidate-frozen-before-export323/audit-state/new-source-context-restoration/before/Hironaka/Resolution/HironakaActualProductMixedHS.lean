/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualProductTruncatedQuotient

/-! Genuine free-coordinate monomials retain the whole normal filtration and mixed ambient jets. -/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualProductMixedHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalActualHSConvolution HironakaActualProductTruncatedQuotient
  HironakaRelativeNormalMixedTangentPowers HironakaRelativeNormalActualWeightedTruncations
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets

/-- Every actual original free-coordinate monomial belongs to its genuine full degree power. -/
theorem actualNormalMonomial_mem_power (d t : ℕ) (α : Fin t →₀ ℕ) :
    normalExponentMonomial d t α ∈ normalIdeal d t ^ normalExponentDegree α := by
  have hp : ∀ S : Finset (Fin t),
      (∏ i ∈ S, normalCoordinate d t i ^ α i) ∈ normalIdeal d t ^ (∑ i ∈ S, α i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi,Finset.sum_insert hi,pow_add]
      have hc : normalCoordinate d t i ∈ normalIdeal d t := Ideal.subset_span ⟨i,rfl⟩
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hc (α i)) ih
  exact hp Finset.univ

section ActualCoordinates
variable (d t s : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t
local instance : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  IsScalarTower.of_algHom (tangentPullback d t)
local instance : Fintype (normalExponentIndex t s) := normalExponentFintype t s

/-- Actual degree-at-least-r coordinates in the SAME genuine original monomial family. -/
def actualProductNormalTail (r : ℕ) :
    Submodule (HolGerm (ComplexModel d)) (normalExponentIndex t s → HolGerm (ComplexModel d)) where
  carrier := {a | ∀ α, normalExponentDegree α.val < r → a α = 0}
  zero_mem' := by intro α _; rfl
  add_mem' := by intro a b ha hb α hα; change a α+b α=0; rw [ha α hα,hb α hα,add_zero]
  smul_mem' := by intro b a ha α hα; change b*a α=0; rw [ha α hα,mul_zero]

/-- True original coefficient separation and monomial powers identify EVERY actual normal filtration image. -/
theorem actualNormalPowerImage_coordinates (r : ℕ) (hr : r ≤ s) :
    (((normalIdeal d t ^ r).restrictScalars (HolGerm (ComplexModel d))).map
      (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ s)).toLinearMap).map
        (normalPowerLinearEquiv d t s).symm.toLinearMap = actualProductNormalTail d t s r := by
  ext a
  constructor
  · rintro ⟨q,⟨g,hg,hgq⟩,hqa⟩ α hα
    have he : (normalPowerLinearEquiv d t s) a = q := by
      rw [← hqa]
      exact (normalPowerLinearEquiv d t s).apply_symm_apply q
    have hclass : Ideal.Quotient.mk (normalIdeal d t ^ s)
        (normalPolynomialEval d t (∑ β : normalExponentIndex t s, MvPolynomial.monomial β.val (a β))) =
          Ideal.Quotient.mk (normalIdeal d t ^ s) g := by
      rw [← normalMonomialCombination_apply]
      change (normalPowerLinearEquiv d t s) a = _
      rw [he]
      exact hgq.symm
    have hrem : normalPolynomialEval d t
        (∑ β : normalExponentIndex t s, MvPolynomial.monomial β.val (a β)) - g ∈ normalIdeal d t ^ r :=
      Ideal.pow_le_pow_right hr (Ideal.Quotient.eq.mp hclass)
    have hp : normalPolynomialEval d t
        (∑ β : normalExponentIndex t s, MvPolynomial.monomial β.val (a β)) ∈ normalIdeal d t ^ r := by
      simpa only [sub_add_cancel] using (normalIdeal d t ^ r).add_mem hrem hg
    have hc := coefficient_eq_zero_of_normalPolynomialEval_mem d t r _ α.val hα hp
    rwa [coefficient_normalMonomialCombination_polynomial] at hc
  · intro ha
    let P := normalPolynomialEval d t
      (∑ α : normalExponentIndex t s, MvPolynomial.monomial α.val (a α))
    have hP : P ∈ normalIdeal d t ^ r := by
      dsimp only [P]
      rw [map_sum]
      apply Ideal.sum_mem
      intro α _
      rw [normalPolynomialEval_monomial]
      by_cases hα : normalExponentDegree α.val < r
      · rw [ha α hα,map_zero,zero_mul]
        exact Ideal.zero_mem _
      · exact Ideal.mul_mem_left _ _
          (Ideal.pow_le_pow_right (by omega : r ≤ normalExponentDegree α.val)
            (actualNormalMonomial_mem_power d t α.val))
    refine ⟨Ideal.Quotient.mk (normalIdeal d t ^ s) P,⟨P,hP,rfl⟩,?_⟩
    change (normalPowerLinearEquiv d t s).symm (Ideal.Quotient.mk (normalIdeal d t ^ s) P) = a
    change (normalPowerLinearEquiv d t s).symm (Ideal.Quotient.mk (normalIdeal d t ^ s)
      (normalPolynomialEval d t (∑ α : normalExponentIndex t s, MvPolynomial.monomial α.val (a α)))) = a
    rw [← normalMonomialCombination_apply]
    exact (normalPowerLinearEquiv d t s).symm_apply_apply a

/-- The exact original mixed-power coordinate weights in the genuine finite monomial family. -/
def actualProductMixedCoordinates (K : Ideal (HolGerm (ComplexModel d))) :
    Submodule (HolGerm (ComplexModel d)) (normalExponentIndex t s → HolGerm (ComplexModel d)) :=
  Submodule.pi Set.univ (fun α => K ^ (s-normalExponentDegree α.val))

/-- The true finite mixed sum of whole normal tails has exactly the actual coordinate weights. -/
theorem actualProductMixedTailSum_eq_coordinates (K : Ideal (HolGerm (ComplexModel d))) :
    (⨆ r : Fin (s+1), K ^ (s-r.val) • actualProductNormalTail d t s r.val) =
      actualProductMixedCoordinates d t s K := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro r
    apply Submodule.smul_le.mpr
    intro b hb a ha α _
    change b*a α ∈ K ^ (s-normalExponentDegree α.val)
    by_cases hα : normalExponentDegree α.val < r.val
    · rw [ha α hα,mul_zero]
      exact Ideal.zero_mem _
    · exact Ideal.mul_mem_right _ _
        (Ideal.pow_le_pow_right (by omega : s-normalExponentDegree α.val ≤ s-r.val) hb)
  · intro a ha
    rw [← LinearMap.sum_single_apply (fun _ : normalExponentIndex t s => HolGerm (ComplexModel d)) a]
    apply Submodule.sum_mem
    intro α _
    have htail : (Pi.single α 1 : normalExponentIndex t s → HolGerm (ComplexModel d)) ∈
        actualProductNormalTail d t s (normalExponentDegree α.val) := by
      intro β hβ
      by_cases he : β=α
      · subst β
        omega
      · simp [Ne.symm he]
    have hs : Pi.single α (a α) = (a α) •
        (Pi.single α 1 : normalExponentIndex t s → HolGerm (ComplexModel d)) := by
      ext β
      by_cases he : β=α <;> simp [he]
    rw [hs]
    exact (le_iSup (fun r : Fin (s+1) => K ^ (s-r.val) • actualProductNormalTail d t s r.val)
      ⟨normalExponentDegree α.val,by have := α.property; omega⟩)
        (Submodule.smul_mem_smul (ha α (mem_univ α)) htail)

/-- The ENTIRE genuine mixed-power image, retaining every true normal degree and original scalar ideal. -/
theorem actualMixedPowerImage_coordinates (K : Ideal (HolGerm (ComplexModel d))) :
    (((actualMixedPower (B := HolGerm (ComplexModel d)) (normalIdeal d t) K s).restrictScalars
      (HolGerm (ComplexModel d))).map
        (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ s)).toLinearMap).map
          (normalPowerLinearEquiv d t s).symm.toLinearMap = actualProductMixedCoordinates d t s K := by
  rw [actualMixedPower_restrictScalars,Submodule.map_iSup,Submodule.map_iSup,
    ← actualProductMixedTailSum_eq_coordinates]
  apply congrArg iSup
  funext r
  rw [Submodule.map_smul'',Submodule.map_smul'',actualNormalPowerImage_coordinates d t s r.val (by omega)]

/-- Genuine finite families retain the sum of the ENTIRE original ideals in each coordinate. -/
theorem actualProductCoordinateIdealSup (I K : Ideal (HolGerm (ComplexModel d))) :
    Submodule.pi Set.univ (fun _ : normalExponentIndex t s => I) ⊔ actualProductMixedCoordinates d t s K =
      Submodule.pi Set.univ (fun α : normalExponentIndex t s => I ⊔ K ^ (s-normalExponentDegree α.val)) := by
  ext a
  constructor
  · intro h
    obtain ⟨b,hb,c,hc,rfl⟩ := Submodule.mem_sup.mp h
    intro α _
    exact Submodule.mem_sup.mpr ⟨b α,hb α (mem_univ α),c α,hc α (mem_univ α),rfl⟩
  · intro ha
    have hdec : ∀ α : normalExponentIndex t s, ∃ b ∈ I, ∃ c ∈ K ^ (s-normalExponentDegree α.val), b+c=a α :=
      fun α => Submodule.mem_sup.mp (ha α (mem_univ α))
    choose b hb c hc he using hdec
    exact Submodule.mem_sup.mpr ⟨b,fun α _ => hb α,c,fun α _ => hc α,funext he⟩

/-- The genuine WHOLE original extended ideal plus mixed power has exactly the actual weighted coefficient ideals. -/
theorem actualProductWholeIdealImage_coordinates (I K : Ideal (HolGerm (ComplexModel d))) :
    (((Ideal.map (tangentPullback d t).toRingHom I ⊔
        actualMixedPower (B := HolGerm (ComplexModel d)) (normalIdeal d t) K s).restrictScalars
      (HolGerm (ComplexModel d))).map
        (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ s)).toLinearMap).map
          (normalPowerLinearEquiv d t s).symm.toLinearMap =
      Submodule.pi Set.univ (fun α : normalExponentIndex t s => I ⊔ K ^ (s-normalExponentDegree α.val)) := by
  have hI : ((Ideal.map (tangentPullback d t).toRingHom I).restrictScalars
      (HolGerm (ComplexModel d))).map
        (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ s)).toLinearMap =
      I • (⊤ : Submodule (HolGerm (ComplexModel d))
        (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t ^ s)) := by
    rw [← actualExtendedIdealImage I (normalIdeal d t ^ s)]
    ext z
    change (∃ g, g ∈ Ideal.map (tangentPullback d t).toRingHom I ∧
      Ideal.Quotient.mk (normalIdeal d t ^ s) g = z) ↔ _
    exact (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).symm
  rw [Submodule.restrictScalars_sup,Submodule.map_sup,Submodule.map_sup,hI,
    actualNormalPowerCoefficientIdeal,actualMixedPowerImage_coordinates,actualProductCoordinateIdealSup]

end ActualCoordinates

section ActualQuotients
variable {B R : Type*} [CommRing B] [CommRing R] [Algebra B R]

/-- The actual ring quotient and the genuine restricted original module quotient have the same original classes. -/
def actualRingIdealModuleQuotientEquiv (J : Ideal R) :
    (R ⧸ J) ≃ₗ[B] (R ⧸ J.restrictScalars B) := by
  refine { (AddEquiv.refl _) with map_smul' := ?_ }
  intro b z
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl
end ActualQuotients

section EntireMixedJets
variable (d t s : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t
local instance : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  IsScalarTower.of_algHom (tangentPullback d t)
local instance : Fintype (normalExponentIndex t s) := normalExponentFintype t s

/-- Every original mixed product jet is genuinely its full weighted original coefficient quotient family. -/
def actualProductMixedJetEquiv (I K : Ideal (HolGerm (ComplexModel d))) :
    (HolGerm (ComplexModel (d+t)) ⧸ (Ideal.map (tangentPullback d t).toRingHom I ⊔
      actualMixedPower (B := HolGerm (ComplexModel d)) (normalIdeal d t) K s)) ≃ₗ[HolGerm (ComplexModel d)]
        (∀ α : normalExponentIndex t s, HolGerm (ComplexModel d) ⧸
          (I ⊔ K ^ (s-normalExponentDegree α.val))) := by
  let L := Ideal.map (tangentPullback d t).toRingHom I ⊔
    actualMixedPower (B := HolGerm (ComplexModel d)) (normalIdeal d t) K s
  let Q := Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ s)
  let J := Ideal.map (Ideal.Quotient.mk (normalIdeal d t ^ s)) L
  have hJ : normalIdeal d t ^ s ≤ L := le_sup_right.trans'
    (actualNormalPower_le_mixed (B := HolGerm (ComplexModel d)) (normalIdeal d t) K s)
  have himage : (L.restrictScalars (HolGerm (ComplexModel d))).map Q.toLinearMap =
      J.restrictScalars (HolGerm (ComplexModel d)) := by
    ext z
    change (∃ g, g ∈ L ∧ Ideal.Quotient.mk (normalIdeal d t ^ s) g = z) ↔ z ∈ J
    exact (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).symm
  have hc : (J.restrictScalars (HolGerm (ComplexModel d))).map
      (normalPowerLinearEquiv d t s).symm.toLinearMap =
        Submodule.pi Set.univ (fun α : normalExponentIndex t s => I ⊔ K ^ (s-normalExponentDegree α.val)) := by
    rw [← himage]
    exact actualProductWholeIdealImage_coordinates d t s I K
  let E0 := ((DoubleQuot.quotQuotEquivQuotSupₐ (HolGerm (ComplexModel d))
    (normalIdeal d t ^ s) L).trans
      (Ideal.quotientEquivAlgOfEq (HolGerm (ComplexModel d)) (sup_eq_right.mpr hJ))).toLinearEquiv.symm
  exact E0.trans ((actualRingIdealModuleQuotientEquiv (B := HolGerm (ComplexModel d)) J).trans
    ((Submodule.Quotient.equiv _ _ (normalPowerLinearEquiv d t s).symm hc).trans
      (Submodule.quotientPi (fun α : normalExponentIndex t s => I ⊔ K ^ (s-normalExponentDegree α.val)))))

/-- Every actual original monomial sum retains its SAME weighted original coefficient classes. -/
theorem actualProductMixedJetEquiv_monomial_sum (I K : Ideal (HolGerm (ComplexModel d)))
    (a : normalExponentIndex t s → HolGerm (ComplexModel d)) :
    actualProductMixedJetEquiv d t s I K
      (Ideal.Quotient.mk (Ideal.map (tangentPullback d t).toRingHom I ⊔
        actualMixedPower (B := HolGerm (ComplexModel d)) (normalIdeal d t) K s)
          (normalPolynomialEval d t (∑ α : normalExponentIndex t s, MvPolynomial.monomial α.val (a α)))) =
      fun α => Ideal.Quotient.mk (I ⊔ K ^ (s-normalExponentDegree α.val)) (a α) := by
  change (Submodule.quotientPi (fun α : normalExponentIndex t s => I ⊔ K ^ (s-normalExponentDegree α.val)))
    (Submodule.Quotient.mk ((normalPowerLinearEquiv d t s).symm
      (Ideal.Quotient.mk (normalIdeal d t ^ s)
        (normalPolynomialEval d t (∑ α : normalExponentIndex t s, MvPolynomial.monomial α.val (a α)))))) = _
  rw [← normalMonomialCombination_apply]
  change (Submodule.quotientPi (fun α : normalExponentIndex t s => I ⊔ K ^ (s-normalExponentDegree α.val)))
    (Submodule.Quotient.mk ((normalPowerLinearEquiv d t s).symm ((normalPowerLinearEquiv d t s) a))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The true original ambient maximal-power quotient, retaining EVERY mixed free-coordinate weight. -/
def actualProductAmbientJetEquiv (I : Ideal (HolGerm (ComplexModel d))) :
    (HolGerm (ComplexModel (d+t)) ⧸ (Ideal.map (tangentPullback d t).toRingHom I ⊔
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s)) ≃ₗ[HolGerm (ComplexModel d)]
        (∀ α : normalExponentIndex t s, HolGerm (ComplexModel d) ⧸
          (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (s-normalExponentDegree α.val))) :=
  (Ideal.quotientEquivAlgOfEq (HolGerm (ComplexModel d))
    (congrArg (fun J => Ideal.map (tangentPullback d t).toRingHom I ⊔ J)
      (originalActualMixedPower_eq_maximalIdeal_power d t s).symm)).toLinearEquiv.trans
    (actualProductMixedJetEquiv d t s I (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))))

/-- The genuine ambient version also retains EVERY original monomial coefficient class. -/
theorem actualProductAmbientJetEquiv_monomial_sum (I : Ideal (HolGerm (ComplexModel d)))
    (a : normalExponentIndex t s → HolGerm (ComplexModel d)) :
    actualProductAmbientJetEquiv d t s I
      (Ideal.Quotient.mk (Ideal.map (tangentPullback d t).toRingHom I ⊔
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s)
          (normalPolynomialEval d t (∑ α : normalExponentIndex t s, MvPolynomial.monomial α.val (a α)))) =
      fun α => Ideal.Quotient.mk
        (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (s-normalExponentDegree α.val)) (a α) :=
  actualProductMixedJetEquiv_monomial_sum d t s I (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) a

end EntireMixedJets

/-- The EXISTING whole original smooth-product HS is the ACTUAL all-order mixed coefficient convolution. -/
theorem actualProductHilbertSamuel_convolution (d t : ℕ) (I : Ideal (HolGerm (ComplexModel d))) (ℓ : ℕ) :
    let := normalExponentFintype t (ℓ+1)
    hilbertSamuelValue (Ideal.map (tangentPullback d t).toRingHom I) ℓ =
      ∑ α : normalExponentIndex t (ℓ+1), hilbertSamuelValue I (ℓ-normalExponentDegree α.val) := by
  let := tangentAlgebra d t
  let : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
    IsScalarTower.of_algHom (tangentPullback d t)
  let := normalExponentFintype t (ℓ+1)
  let : ∀ α : normalExponentIndex t (ℓ+1), Module.Finite ℂ (HolGerm (ComplexModel d) ⧸
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ ((ℓ+1)-normalExponentDegree α.val))) :=
    fun α => finiteDimensional_quotient_sup_maximalIdeal_pow d ((ℓ+1)-normalExponentDegree α.val) I
  change Module.finrank ℂ (HolGerm (ComplexModel (d+t)) ⧸
    (Ideal.map (tangentPullback d t).toRingHom I ⊔
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ (ℓ+1))) = _
  rw [((actualProductAmbientJetEquiv d t (ℓ+1) I).restrictScalars ℂ).finrank_eq,Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro α _
  have hp : ℓ+1-normalExponentDegree α.val = (ℓ-normalExponentDegree α.val)+1 := by
    have := α.property
    omega
  rw [hp]
  rfl
end
end Hironaka.HironakaActualProductMixedHS
