/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualExceptionalFilteredDivision
import Hironaka.Resolution.HironakaActualHomogeneousInitialTangentDerivatives
import Hironaka.Resolution.HironakaActualRelativePointChartFactorization

/-!
# Entire current initial generation of the SAME exceptional family

Actual exceptional filtered representations generate the whole current
homogeneous initial ideal and actual finite homogeneous multiplier bands.
Original canonical point quotients are selected before every current-order
hypothesis. Literal relative-to-point chart composition and analytic domain
cancellation retain each prescribed relative quotient rather than rechoosing
its numerator/family. Image monic witnesses and relative maximal-adic
standardness remain downstream.
Blueprint: `hironaka-actual-exceptional-initial-generation-extension.tex`.
-/

set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace Hironaka.HironakaActualExceptionalInitialGeneration
noncomputable section
open HolGerm HironakaRelativeNormalMonomialBasis
 HironakaActualFormalCoordinatePowerDivision HironakaActualOriginalFormalHSTransfer
 HironakaActualFormalInitialDiagram HironakaActualHomogeneousInitialHS
 HironakaActualHomogeneousInitialTangentDerivatives HironakaActualExceptionalFilteredDivision
 HironakaActualOriginalFormalTaylor HironakaActualOriginalReducedVertexBasis
 HironakaActualPointCentreStrictGenerators HironakaActualRelativePointChartFactorization
 HironakaHolomorphicJetMonomialSpan HironakaActualAnalyticBlowupTaylor
 HironakaActualAnalyticStrictGenerators
variable {n : ℕ} {ι : Type*} [Fintype ι]
local notation "R" => MvPowerSeries (Fin n) ℂ
local notation "𝔪" => actualFormalCoordinateIdeal n univ

private theorem pointIdeal_eq_genuineVariables (n : ℕ) :
    actualFormalCoordinateIdeal n univ=genuineFormalVariables n := by
  simp [actualFormalCoordinateIdeal,genuineFormalVariables]

private theorem power_order (q : ℕ) (F : R) (hF : F∈𝔪^q) : (q : ℕ∞)≤F.order := by
  apply MvPowerSeries.nat_le_order
  intro α hα
  apply (mem_actualFormalCoordinateIdeal_pow_iff univ q F).mp hF α
  simpa [actualCoordinateWeight,Finsupp.weight_eq_sum,Finsupp.degree_eq_sum] using hα

private theorem component_product (H Q : R) (d q : ℕ)
    (hH : H∈𝔪^d) (hQ : Q∈𝔪^(q-d)) :
    MvPowerSeries.homogeneousComponent q (H*Q)=
      if d≤q then MvPowerSeries.homogeneousComponent d H *
        MvPowerSeries.homogeneousComponent (q-d) Q else 0 := by
  split_ifs with hd
  · have he := MvPowerSeries.homogeneousComponent_mul_of_le_order
      (power_order d H hH) (power_order (q-d) Q hQ)
    rwa [Nat.add_sub_of_le hd] at he
  · have hp : H*Q∈𝔪^(q+1) :=
      (𝔪^(q+1)).mul_mem_right Q (Ideal.pow_le_pow_right (by omega) hH)
    apply MvPowerSeries.homogeneousComponent_of_lt_order_eq_zero
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self q) (power_order (q+1) _ hp)

private theorem initial_eq_component_span_of_filtered
    (H : ι → R) (d : ι → ℕ) (hH : ∀i,H i∈𝔪^(d i))
    (hFiltered : ∀q F,F∈Ideal.span (range H)→F∈𝔪^q→
      ∃Q : ι → R,F=(∑i,H i*Q i) ∧∀i,Q i∈𝔪^(q-d i)) :
    actualHomogeneousInitialIdeal (Ideal.span (range H))=
      Ideal.span (range fun i => MvPowerSeries.homogeneousComponent (d i) (H i)) := by
  have hBand (q : ℕ) (F : R) (hFI : F∈Ideal.span (range H)) (hFq : F∈𝔪^q) :
      MvPowerSeries.homogeneousComponent q F∈
        Ideal.span (range fun i => MvPowerSeries.homogeneousComponent (d i) (H i)) := by
    obtain ⟨Q,hQ,hQpow⟩ := hFiltered q F hFI hFq
    rw [hQ,map_sum]
    apply Ideal.sum_mem
    intro i _
    rw [component_product _ _ _ _ (hH i) (hQpow i)]
    split_ifs
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_range_self (x := i))
    · exact Ideal.zero_mem _
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro G ⟨F,rfl⟩
    change actualHomogeneousInitialForm F.val F.property.2∈_
    apply hBand _ _ F.property.1
    apply (mem_actualFormalCoordinateIdeal_pow_iff univ _ _).mpr
    intro α hα
    have ho := actualHomogeneousInitialDegree_eq_order F.val F.property.2
    apply MvPowerSeries.coeff_of_lt_order
    rw [←ho]
    exact_mod_cast (show Finsupp.degree α<actualHomogeneousInitialDegree F.val F.property.2 from
      by simpa [actualCoordinateWeight,Finsupp.weight_eq_sum,Finsupp.degree_eq_sum] using hα)
  · apply Ideal.span_le.mpr
    rintro G ⟨i,rfl⟩
    apply homogeneousComponent_mem_actual_initial_of_mem_power _ _ _ (Ideal.mem_span_range_self (x := i))
    rw [←pointIdeal_eq_genuineVariables]
    exact hH i

/-- Natural exceptional regularity, actual orders and literal homogeneous shadows produce the whole current initial span. -/
theorem actualHomogeneousInitialIdeal_eq_exceptional_component_span
    (H : ι → R) (d : ι → ℕ) (e : Fin n)
    (hH : ∀i,H i∈𝔪^(d i))
    (hShadow : ∀i,(pivotZeroProjection e (H i)).IsHomogeneous (d i))
    (hReg : ∀F : R,MvPowerSeries.X e*F∈Ideal.span (range H)→F∈Ideal.span (range H)) :
    actualHomogeneousInitialIdeal (Ideal.span (range H))=
      Ideal.span (range fun i => MvPowerSeries.homogeneousComponent (d i) (H i)) :=
  initial_eq_component_span_of_filtered H d hH
    (fun q F hFI hFq => exists_exceptional_filtered_representation H d e hH hShadow hReg q F hFI hFq)


private theorem homogeneous_power (q : ℕ) (F : R) (hF : F.IsHomogeneous q) : F∈𝔪^q := by
  apply (mem_actualFormalCoordinateIdeal_pow_iff univ q F).mpr
  intro α hα
  apply hF.coeff_eq_zero
  have hdeg : α.degree<q := by
    simpa [actualCoordinateWeight,Finsupp.weight_eq_sum,Finsupp.degree_eq_sum] using hα
  omega

private theorem homogeneous_truncation (q : ℕ) (F : R) (hF : F.IsHomogeneous q) :
    (MvPowerSeries.truncTotal (q+1) F : R)=F := by
  apply MvPowerSeries.ext
  intro α
  rw [MvPolynomial.coeff_coe,MvPowerSeries.coeff_truncTotal_eq_ite]
  split_ifs with hα
  · rfl
  · symm
    exact hF.coeff_eq_zero (by omega)

/-- The whole current initial member has actual finite homogeneous coefficient bands, not a supplied representation. -/
theorem exists_exceptional_initial_homogeneous_bands
    (H : ι → R) (d : ι → ℕ) (e : Fin n)
    (hH : ∀i,H i∈𝔪^(d i))
    (hShadow : ∀i,(pivotZeroProjection e (H i)).IsHomogeneous (d i))
    (hReg : ∀F : R,MvPowerSeries.X e*F∈Ideal.span (range H)→F∈Ideal.span (range H))
    (q : ℕ) (P : R) (hP : P.IsHomogeneous q)
    (hPI : P∈actualHomogeneousInitialIdeal (Ideal.span (range H))) :
    ∃A : ι → R,
      P=(∑i,MvPowerSeries.homogeneousComponent (d i) (H i)*A i) ∧
      (∀i,(A i).IsHomogeneous (q-d i)) ∧
      (∀i,q<d i→A i=0) ∧
      ∀i,(MvPowerSeries.truncTotal (q-d i+1) (A i) : R)=A i := by
  rw [actualHomogeneousInitialIdeal_eq_exceptional_component_span H d e hH hShadow hReg] at hPI
  let C : ι → R := fun i => MvPowerSeries.homogeneousComponent (d i) (H i)
  have hC (i : ι) : (C i).IsHomogeneous (d i) :=
    MvPowerSeries.isHomogeneous_homogeneousComponent _ _
  obtain ⟨B,hB,hBpow⟩ := exists_homogeneous_filtered_representation C d hC P hPI q
    (homogeneous_power q P hP)
  let A : ι → R := fun i => if d i≤q then MvPowerSeries.homogeneousComponent (q-d i) (B i) else 0
  have hA (i : ι) : (A i).IsHomogeneous (q-d i) := by
    dsimp [A]
    split_ifs
    · exact MvPowerSeries.isHomogeneous_homogeneousComponent _ _
    · simp
  refine ⟨A,?_,hA,?_,fun i => homogeneous_truncation _ _ (hA i)⟩
  · have he := congrArg (MvPowerSeries.homogeneousComponent q) hB
    rw [←MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp hP,map_sum] at he
    rw [he]
    apply Finset.sum_congr rfl
    intro i _
    rw [component_product _ _ _ _ (homogeneous_power _ _ (hC i)) (hBpow i)]
    rw [←MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp (hC i)]
    dsimp [C,A]
    split_ifs <;> simp only [mul_zero]
  · intro i hi
    simp only [A,if_neg (show ¬d i≤q from by omega)]


private theorem original_point_power (q : ℕ) (g : HolGerm (ComplexModel (0+n)))
    (hg : g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^q) :
    originalTaylorAlgHom n g∈𝔪^q := by
  apply (mem_actualFormalCoordinateIdeal_pow_iff univ q _).mpr
  intro α hα
  apply (mem_original_maximal_pow_iff_formal_coefficients_zero n q g).mp hg α
  simpa [actualCoordinateWeight,Finsupp.weight_eq_sum,normalExponentDegree] using hα

/-- ONE actual original canonical normalized family precedes all current order bounds and its entire initial equality. -/
theorem exists_original_point_canonical_initial_family
    (J : Ideal (HolGerm (ComplexModel (0+n)))) (j : Fin n) (b : Fin (0+n) → ℂ) :
    ∃H : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
        (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)),
      (∀a,coordinateGerm (j.natAdd 0)^normalExponentDegree a.val*H a=
        actualAnalyticBlowupPullback (HironakaActualCoefficientPresentationCentrePower.actualTangentCentreVariables 0 n)
          (j.natAdd 0) b (originalReducedVertexBasis J a)) ∧
      actualAnalyticNormalizedMemberIdeal J
        (HironakaActualCoefficientPresentationCentrePower.actualTangentCentreVariables 0 n) (j.natAdd 0) b=
        Ideal.span (range H) ∧
      ∀(_hOrder : ∀a,H a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^normalExponentDegree a.val),
        actualHomogeneousInitialIdeal (Ideal.span (range fun a => originalTaylorAlgHom n (H a)))=
          Ideal.span (range fun a => MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
            (originalTaylorAlgHom n (H a))) := by
  obtain ⟨H,hH,hNamed,hFiltered⟩ := exists_original_point_canonical_filtered_family J j b
  refine ⟨H,hH,hNamed,?_⟩
  intro hOrder
  apply initial_eq_component_span_of_filtered _ _ (fun a => original_point_power _ _ (hOrder a))
  intro q F hF hFq
  apply hFiltered hOrder q F ?_ hFq
  rw [hNamed,Ideal.map_span,←range_comp]
  exact hF

/-- A prescribed relative SAME-canonical quotient family inherits the literal point-family initial equality after actual tangent scaling. -/
theorem canonical_relative_point_initial_generation
    (J : Ideal (HolGerm (ComplexModel (0+n))))
    (A : Set (Fin (0+n))) (j : Fin n) (b : Fin (0+n) → ℂ)
    (H : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)))
    (hH : ∀a,coordinateGerm (j.natAdd 0)^normalExponentDegree a.val*H a=
      actualAnalyticBlowupPullback A (j.natAdd 0) b (originalReducedVertexBasis J a))
    (hOrder : ∀a,
      actualAnalyticBlowupPullback (actualTangentScalingVariables A (j.natAdd 0)) (j.natAdd 0) (fun _ => 0) (H a)∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^normalExponentDegree a.val) :
    let σ := actualAnalyticBlowupPullback (actualTangentScalingVariables A (j.natAdd 0)) (j.natAdd 0) (fun _ => 0)
    actualHomogeneousInitialIdeal (Ideal.span (range fun a => originalTaylorAlgHom n (σ (H a))))=
      Ideal.span (range fun a => MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
        (originalTaylorAlgHom n (σ (H a)))) := by
  let σ := actualAnalyticBlowupPullback (actualTangentScalingVariables A (j.natAdd 0)) (j.natAdd 0) (fun _ => 0)
  have hVars : HironakaActualCoefficientPresentationCentrePower.actualTangentCentreVariables 0 n=univ := by
    ext i
    constructor
    · intro _;trivial
    · intro _
      refine ⟨⟨i.val,by simpa using i.isLt⟩,?_⟩
      apply Fin.ext
      simp
  obtain ⟨K,hK,_hNamed,hInitial⟩ := exists_original_point_canonical_initial_family J j (actualPointChartDirection A b)
  have hEq (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) : K a=σ (H a) := by
    apply actual_relative_quotient_point_unique A (j.natAdd 0) b _ _ _ _ (hH a)
    simpa only [hVars] using hK a
  have hFun : K=fun a => σ (H a) := funext hEq
  rw [hFun] at hInitial
  exact hInitial hOrder

end
end Hironaka.HironakaActualExceptionalInitialGeneration
