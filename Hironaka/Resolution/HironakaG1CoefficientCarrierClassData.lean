import Hironaka.Resolution.HironakaG1CoefficientBarClassData
import Hironaka.Resolution.HironakaG8ClassStepExp
import Hironaka.Resolution.HironakaG8LocalPower

/-! Actual true-mark coefficient/bar class data for different carriers.
The held equal-dimensional trace-filling theorem is applied to the
actual common whole powers; no carrier-identification packet is assumed.
Blueprint FIRST: hironaka-g1-coefficient-carrier-class-data.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1CoefficientCarrierClassData
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec GermIdealOrder
  DivisorExponentAlong RelativePrincipalizationSpan IdealWeightPowers
  HironakaG8LocalHistory HironakaG8LocalPower HironakaActualPowerBoundaryExponents
  HironakaG8GapNormalizedExponent HironakaG8ClassStepExp HironakaG11InvBMClass
  HironakaG1CoefficientBarClassData HironakaG8CoefficientBoundaryLocal
  HironakaActualInitialNonmonomialCoefficientBoundary HironakaG8HomStable
  HomogenizedIdealAlong StepOneValue

/-- A genuine cosupport trace detects the exact normalized exponents
on different actual equal-dimensional carriers, at the native marks. -/
theorem normalized_exponent_of_trace_sameCarrierDim {n k l : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (A B : MarkedIdeal n X)
    (hA : IsInvDomain k A) (hB : IsInvDomain l B)
    (hL : LocWPEquiv A B) (hDim : SameCarrierDim A B)
    (H : Set X) (hH : H ∈ A.E) (x : X) (hx : x ∈ A.cosupp) (hxH : x ∈ H)
    (hTrace : ∀ᶠ y in 𝓝 x, y ∈ A.N → y ∈ H → y ∈ A.cosupp) :
    B.d * divExpAlong n A.N A.ideal H x = A.d * divExpAlong n B.N B.ideal H x := by
  have hAP := powerMarked_isInvDomain A hA hB.one_le_d
  have hBP := powerMarked_isInvDomain B hB hA.one_le_d
  have hCommon := locEquiv_commonMark (κ := Kinds.wp) rfl hL hA hB
  have hDimP : SameCarrierDim (powerMarked A B.d) (powerMarked B A.d) := by
    intro y hy j
    exact hDim y ((powerMarked_cosupp A hA hB.one_le_d) ▸ hy) j
  have hxP : x ∈ (powerMarked A B.d).cosupp := by
    rw [powerMarked_cosupp A hA hB.one_le_d]
    exact hx
  have hSub : IsDivNearAlong n (powerMarked A B.d).N (powerMarked A B.d).ideal H
      (powerMarked A B.d).d x := by
    filter_upwards [hTrace] with y hy hyN hyH
    change y ∈ (powerMarked A B.d).cosupp
    rw [powerMarked_cosupp A hA hB.one_le_d]
    exact hy hyN hyH
  have hExp := divExpAlong_eq_of_isDivNearAlong_mark hn hCommon.1 hAP hBP hDimP
    hCommon.2.symm hH hxP hxH hSub
  change divExpAlong n A.N (idealPow A.ideal B.d) H x =
    divExpAlong n B.N (idealPow B.ideal A.d) H x at hExp
  rw [divExpAlong_idealPow hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent hB.one_le_d,
    divExpAlong_idealPow hB.isWellFormed.isClosedSubmanifold_N hB.isWellFormed.isCoherent hA.one_le_d] at hExp
  exact hExp

/-- Both actual support gaps supply the trace internally, including the
zero/positive reversed case. Equality of carriers is unnecessary. -/
theorem normalized_exponents_of_gap_sameCarrierDim {n k l : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (A B : MarkedIdeal n X)
    (hA : IsInvDomain k A) (hB : IsInvDomain l B)
    (hL : LocWPEquiv A B) (hDim : SameCarrierDim A B)
    (hGapA : HasCosupportGap A) (hGapB : HasCosupportGap B) :
    ∀ H ∈ A.E, ∀ x ∈ A.cosupp, x ∈ H →
      B.d * divExpAlong n A.N A.ideal H x = A.d * divExpAlong n B.N B.ideal H x := by
  intro H hH x hx hxH
  by_cases hPosA : 0 < divExpAlong n A.N A.ideal H x
  · obtain ⟨i, hi⟩ := List.get_of_mem hH
    have hTrace : ∀ᶠ y in 𝓝 x, y ∈ A.N → y ∈ H → y ∈ A.cosupp := by
      simpa only [hi] using trace_cosupp_of_gap_pos A hA hGapA i (A.cosupp_subset_N hx)
        (hi.symm ▸ hxH) (hi.symm ▸ hPosA)
    exact normalized_exponent_of_trace_sameCarrierDim hn A B hA hB hL hDim H hH x hx hxH hTrace
  · have hZeroA : divExpAlong n A.N A.ideal H x = 0 := by omega
    by_cases hPosB : 0 < divExpAlong n B.N B.ideal H x
    · have hHB : H ∈ B.E := hL.wEquiv.1 ▸ hH
      have hxB : x ∈ B.cosupp := hL.cosupp_eq_base ▸ hx
      have hDimB : SameCarrierDim B A := by
        intro y hy j
        exact (hDim y (hL.cosupp_eq_base.symm ▸ hy) j).symm
      obtain ⟨j, hj⟩ := List.get_of_mem hHB
      have hTrace : ∀ᶠ y in 𝓝 x, y ∈ B.N → y ∈ H → y ∈ B.cosupp := by
        simpa only [hj] using trace_cosupp_of_gap_pos B hB hGapB j (B.cosupp_subset_N hxB)
          (hj.symm ▸ hxH) (hj.symm ▸ hPosB)
      exact (normalized_exponent_of_trace_sameCarrierDim hn B A hB hA hL.symm hDimB H hHB x hxB hxH hTrace).symm
    · have hZeroB : divExpAlong n B.N B.ideal H x = 0 := by omega
      simp only [hZeroA, hZeroB, Nat.mul_zero]

/-- Ordinary local source records of equal carrier dimension supply their
whole true-mark coefficient records and all normalized boundary exponents. -/
theorem coefficient_class_data_sameCarrierDim {n k l : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q) :
    let C := coeffMarkedAlong P
    let D := coeffMarkedAlong Q
    IsInvDomain k C ∧ IsInvDomain l D ∧ C.E = D.E ∧ LocWPEquiv C D ∧ SameCarrierDim C D ∧
      (∀ H ∈ C.E, ∀ x ∈ C.cosupp, x ∈ H →
        D.d * divExpAlong n C.N C.ideal H x = C.d * divExpAlong n D.N D.ideal H x) := by
  let C := coeffMarkedAlong P
  let D := coeffMarkedAlong Q
  have hC : IsInvDomain k C := coefficient_isInvDomain P hP
  have hD : IsInvDomain l D := coefficient_isInvDomain Q hQ
  have hCP := coefficient_local_any_boundary P hP
  have hDQ := coefficient_local_any_boundary Q hQ
  have hCL : LocWPEquiv C D := (hCP.symm.trans hL).trans hDQ
  have hCDim : SameCarrierDim C D := by
    intro x hx j
    exact hDim x (hCP.cosupp_eq_base.symm ▸ hx) j
  refine ⟨hC, hD, hL.wEquiv.1, hCL, hCDim, ?_⟩
  exact normalized_exponents_of_gap_sameCarrierDim hn C D hC hD hCL hCDim
    (coefficient_hasCosupportGap P hP) (coefficient_hasCosupportGap Q hQ)

/-- The SAME actual original bar records retain their full native marks,
boundaries and class data on different equal-dimensional carriers. -/
theorem bar_class_data_sameCarrierDim {n k l : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q) :
    let C := barMarked P
    let D := barMarked Q
    IsInvDomain k C ∧ IsInvDomain l D ∧ C.E = D.E ∧ LocWPEquiv C D ∧ SameCarrierDim C D ∧
      (∀ H ∈ C.E, ∀ x ∈ C.cosupp, x ∈ H →
        D.d * divExpAlong n C.N C.ideal H x = C.d * divExpAlong n D.N D.ideal H x) := by
  have hHP := hom_isInvDomain P hP
  have hHQ := hom_isInvDomain Q hQ
  have hHPQ := hom_local_any_boundary P hP
  have hHQQ := hom_local_any_boundary Q hQ
  have hHL : LocWPEquiv (homMarkedAlong P) (homMarkedAlong Q) :=
    (hHPQ.symm.trans hL).trans hHQQ
  have hHDim : SameCarrierDim (homMarkedAlong P) (homMarkedAlong Q) := by
    intro x hx j
    exact hDim x (hHPQ.cosupp_eq_base.symm ▸ hx) j
  exact coefficient_class_data_sameCarrierDim hn (homMarkedAlong P) (homMarkedAlong Q)
    hHP hHQ hHL hHDim

end
end Hironaka.HironakaG1CoefficientCarrierClassData
