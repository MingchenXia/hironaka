import Hironaka.Resolution.HironakaG8ResidualPositiveMixed
import Hironaka.Resolution.HironakaG8CaseTResidual
import Hironaka.Resolution.HironakaG11ActualPositiveMixedTrace

/-! # The successor residual and the lower-exponent step -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ResidualSuccClosure
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen HomogenizedGlueingTower GermIdealOrder DivisorExponentAlong
  HironakaG8LocalHistory HironakaG8ClassStepCut HironakaG8ClassStepHistory HironakaG8CaseTResidual
  HironakaG8ResidualPositiveMixed HironakaG11ActualPositiveMixedTrace
  HironakaG11InvBMLower HironakaG11InvBMMask StepOneValue ResolutionInvariantSpec HomogenizedIdealAlong
  MarkedIdealOperationsAlong.MarkedIdeal
open HironakaG11InvBMClass (SameCarrierDim ExpAgree)

/-- The actual positive mixed trace completes the successor residual. -/
theorem lowerExpResidualSucc_actual
    {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n} {A B : MarkedIdeal n X} {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hd : A.d = B.d) (hE : A.E = B.E) (hdim : SameCarrierDim A B) :
    LowerExpResidualSucc A B := by
  intro Y T hT s a ha hreg O hOA hOB r r' hdA hdB y hyO H hH hy hyH hbelow hdiv
  have hWA := StepOneBridge.barMarked_wEquiv A hA
  have hWB := StepOneBridge.barMarked_wEquiv B hB
  have hTA : IsGeoTestTower A T := (hWA.2 T).1.mp hT
  have hTB : IsGeoTestTower B T := (h.wEquiv.2 T).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) T := (hWB.2 T).1.mpr hTB
  have hCA := HironakaG11InvBMRebase.isCoherent_lowerIdealBM A hA.isWellFormed hA.one_le_d hn T hT a (s+1)
  have hloc := locWPEquiv_lowerIdealBM_succ hn hA hB hmA hmB h hE T hT ha s O hOA hOB
  have hypA : (⟨y,hyO⟩ : O) ∈ (MarkedIdeal.pullback (Subtype.val : O → Y) (lowerIdealBM A (s+1) T a)).cosupp := by
    rw [cosupp_pullback_val _ (hol_of_isCoherent hCA) O]
    exact hy
  have hypB := hloc.cosupp_eq_base ▸ hypA
  have hyB : y ∈ (lowerIdealBM B (s+1) T a).N :=
    (MarkedIdeal.pullback (Subtype.val : O → Y) (lowerIdealBM B (s+1) T a)).cosupp_subset_N hypB
  have hyA := (lowerIdealBM A (s+1) T a).cosupp_subset_N hy
  apply actual_successor_exp_eq_of_positive_mixed_trace hn hA hB hmA hmB h hd hE hdim
    T hT ha s hreg O hOA hOB hdA hdB hyO hH hy hyH hbelow hdiv
  intro hnzA hnzB hposA hposB _
  exact actual_positive_mixed_trace_iff hn hA hB hmA hmB h hd hE hdim T hT ha s hreg O hOA hOB
    hyO hH hyA hyB hyH hdiv hnzA hnzB hposA hposB

/-- The successor residual holds at every invariant-domain level. -/
theorem lowerExpResidualSuccStepBM_actual {n : ℕ} (hn : 0 < n) (k : ℕ) : LowerExpResidualSuccStepBM n k := by
  intro X A B hA hB hmA hmB h hd hE hdim _
  exact lowerExpResidualSucc_actual hn hA hB hmA hmB h hd hE hdim

/-- The level-zero and successor arguments together discharge the lower
exponent residual step in every positive ambient dimension. -/
theorem lowerExpResidualStepBM_actual {n : ℕ} (hn : 0 < n) (k : ℕ) :
    HironakaG8ClassStepBridge.LowerExpResidualStepBM n k :=
  lowerExpResidualStepBM_of_succ_actual hn (lowerExpResidualSuccStepBM_actual hn k)

end
end Hironaka.HironakaG8ResidualSuccClosure
