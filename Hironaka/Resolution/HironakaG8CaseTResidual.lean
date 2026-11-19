import Hironaka.Resolution.HironakaG8CaseTActualHistory

/-! # Level-zero residual without a universal order hypothesis -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8CaseTResidual

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen
  Hironaka.DivisorExponentAlong Hironaka.HomogenizedIdealAlong
  Hironaka.MarkedIdealOperationsAlong
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.ContactEquivalenceAlong Hironaka.TangentDirectionAlong
  Hironaka.NormalCrossings Hironaka.GermIdealOrder
  Hironaka.StepOneValue Hironaka.HironakaG11InvBMMask
  Hironaka.HironakaG11InvBMLower Hironaka.HironakaG11InvBMStage
  Hironaka.HironakaG8LocalHistory Hironaka.HironakaG8LocalContact
  Hironaka.HironakaG8DomainExponents Hironaka.CoefficientIdealRestriction
  Hironaka.CoefficientIdealAlongRestrictionTower Hironaka.RestrictedIdealWeight
  Hironaka.BlowupStrictSubmanifold
open Hironaka.HironakaStepOneZeroContactRemainderGlueing (isNonzeroAlongAt_pullback_val_iff)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ExpAgree)
open Hironaka.HironakaG8MixedEquiv (isAdmissibleCentre_congr)
open Hironaka.HironakaG8ClassStep (LowerPairs)
open Hironaka.RestrictedIdealExtension (sumIdeal)
open Hironaka.HironakaG8ClassStepResidual (LowerExpResidual)

noncomputable section

universe u

variable {n : ℕ}


open HironakaG8ClassStepHistory HironakaG8CaseTActualHistory

variable {X : CMfd.{0} n}

theorem expAgreeBelowAt_lowerIdealBM_zero_actual
    (hn : 0 < n) {k k' : ℕ} {A B : MarkedIdeal n X} (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d) (h : LocWPEquiv A B)
    (hd : A.d = B.d) (hE : A.E = B.E) (hdim : SameCarrierDim A B) {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (barMarked A) T₀) {y₀ : Y₀} (hy₀ : y₀ ∈ (geoTransformAlong (barMarked A) T₀).cosupp)
    (O : Opens Y₀) (hOA : O ≤ maskBM A 0 T₀ y₀) (hOB : O ≤ maskBM B 0 T₀ y₀) {r r' : ℕ}
    (hdA : IsInvDomain r (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM A 0 T₀ y₀)))
    (hdB : IsInvDomain r' (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM B 0 T₀ y₀)))
    {y : Y₀} (hyO : y ∈ O) :
    ExpAgreeBelowAt (lowerIdealBM A 0 T₀ y₀) (lowerIdealBM B 0 T₀ y₀) y := by
  have hWA : WEquiv (barMarked A) A := StepOneBridge.barMarked_wEquiv A hA
  have hWB : WEquiv (barMarked B) B := StepOneBridge.barMarked_wEquiv B hB
  have hW : WEquiv A B := LocEquiv.wEquiv h
  have hTA : IsGeoTestTower A T₀ := (hWA.2 T₀).1.mp hT₀
  have hTB : IsGeoTestTower B T₀ := (hW.2 T₀).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) T₀ := (hWB.2 T₀).1.mpr hTB
  have hyA : y₀ ∈ (geoTransformAlong A T₀).cosupp := (hWA.2 T₀).2 hT₀ ▸ hy₀
  have hyB : y₀ ∈ (geoTransformAlong (barMarked B) T₀).cosupp := by
    rw [(hWB.2 T₀).2 hTJB, ← (hW.2 T₀).2 hTA]
    exact hyA
  obtain ⟨-, hwA⟩ := StepOneLowerDomain.tangentChoice_spec A
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp A hA.isWellFormed hA.one_le_d hmA T₀ hT₀ hy₀)
  obtain ⟨-, hwB⟩ := StepOneLowerDomain.tangentChoice_spec B
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp B hB.isWellFormed hB.one_le_d hmB T₀ hTJB hyB)
  let W : Opens X := ⟨(tangentChoice A (T₀.proj y₀)).1 ∩ (tangentChoice B (T₀.proj y₀)).1, hwA.isOpen.inter hwB.isOpen⟩
  have hcL := HironakaG11InvBMRebase.isCoherent_lowerIdealBM A hA.isWellFormed hA.one_le_d hn T₀ hT₀ y₀ 0
  have hcL' := HironakaG11InvBMRebase.isCoherent_lowerIdealBM B hB.isWellFormed hB.one_le_d hn T₀ hTJB y₀ 0
  have hloc := HironakaG8ClassStepLower.locWPEquiv_lowerIdealBM_zero hn hA hB hmA hmB h hE T₀ hT₀ hy₀ O hOA hOB
  intro H hH hy hyH
  let p : O := ⟨y, hyO⟩
  have hpO : p ∈ (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM A 0 T₀ y₀)).cosupp := by
    rw [cosupp_pullback_val _ (hol_of_isCoherent hcL) O]
    exact hy
  have hpO' := hloc.cosupp_eq_base ▸ hpO
  have nz1 : IsNonzeroAlongAt (lowerIdealBM A 0 T₀ y₀).N (lowerIdealBM A 0 T₀ y₀).ideal y :=
    (isNonzeroAlongAt_pullback_val_iff hcL O p).mp (hdA.isNonzeroAlongAt _ (MarkedIdeal.cosupp_subset_N _ hpO))
  have nz2 : IsNonzeroAlongAt (lowerIdealBM B 0 T₀ y₀).N (lowerIdealBM B 0 T₀ y₀).ideal y :=
    (isNonzeroAlongAt_pullback_val_iff hcL' O p).mp (hdB.isNonzeroAlongAt _ (MarkedIdeal.cosupp_subset_N _ hpO'))
  have hpW : y ∈ openPreimage T₀ W := ⟨(interior_subset (hOA hyO)).1, (interior_subset (hOB hyO)).1⟩
  exact expAgreeBelowAt_contactCoeffBM_actual hA hB h hd hE hdim hwA hwB W (fun _ hx => hx.1) (fun _ hx => hx.2) T₀ hTA hpW
    nz1 nz2 H hH hy hyH


theorem lowerExpResidual_of_succ_actual
    (hn : 0 < n) {k k' : ℕ} {A B : MarkedIdeal n X} (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d) (h : LocWPEquiv A B)
    (hd : A.d = B.d) (hE : A.E = B.E) (hdim : SameCarrierDim A B) (hres : LowerExpResidualSucc A B) :
    LowerExpResidual A B := by
  intro Y₀ T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r' hdA hdB y hyO H hH hy hyH hbelow h0 hs
  cases s with
  | zero =>
    have hagree := expAgreeBelowAt_lowerIdealBM_zero_actual hn hA hB hmA hmB h hd hE hdim T₀ hT₀ hy₀ O hOA hOB hdA hdB hyO
      H hH hy hyH
    have hcL := HironakaG11InvBMRebase.isCoherent_lowerIdealBM A hA.isWellFormed hA.one_le_d hn T₀ hT₀ y₀ 0
    have hlt : divExpAlong n (lowerIdealBM A 0 T₀ y₀).N (lowerIdealBM A 0 T₀ y₀).ideal H y <
        (lowerIdealBM A 0 T₀ y₀).d := by
      by_contra hge
      push Not at hge
      exact hbelow ((isDivNearAlong_divExpAlong (hol_of_isCoherent hcL) y).mono hge)
    omega
  | succ s =>
    exact hres T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r' hdA hdB y hyO H hH hy hyH hbelow (hs (Nat.succ_pos s))


theorem lowerExpResidualStepBM_of_succ_actual
    (hn : 0 < n) {k : ℕ} (h : LowerExpResidualSuccStepBM n k) : HironakaG8ClassStepBridge.LowerExpResidualStepBM n k :=
  fun A B hA hB hmA hmB hAB hd hE hdim h0 =>
    lowerExpResidual_of_succ_actual hn hA hB hmA hmB hAB hd hE hdim (h A B hA hB hmA hmB hAB hd hE hdim h0)

end
end Hironaka.HironakaG8CaseTResidual
