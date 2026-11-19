import Hironaka.Resolution.HironakaG1ActualLaterOrderRun
import Hironaka.Invariant.ContactRepresentative

/-! Reading the initial order companion on the literal marked restriction. -/

set_option autoImplicit false

open Set TopologicalSpace

namespace Hironaka.HironakaG1SameMarkInitialStepOne

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealOperationsAlong.MarkedIdeal RelativePrincipalizationSpan RestrictedIdealExtension
  ResolutionInvariantSpec CanonicalCentres GeneralValue HomogenizedIdealAlong StepOneRegime
  CompanionRebase CompanionReductionAlong NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime
  InvDomainCompanion InvDomainTowerAlong InvDomainRebase
  HironakaG1InitialPositiveGeneralRead HironakaG1ActualLaterOrderRun

set_option maxHeartbeats 1300000 in
/-- A full order run at the true mark whose companion only restricts the
ideal to its carrier reads the original Step One invariant of the literal
marked restriction. This retains the actual order mask, tower, and mark. -/
theorem same_mark_initial_stepOne_read {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K : MarkedIdeal n X) (hK : IsInvDomain (k + 1) K)
    (hEq : companionOf n K K.d = (⟨K.N, K.E, restrictOn n K.N K.ideal, K.d⟩ : MarkedIdeal n X))
    (T : BlowupTower X Y) (hCan : IsCanonical K ((invFamily hn (k + 1)).inv K) T)
    (y : Y) (hy : y ∈ (geoTransformAlong K T).cosupp)
    (hOrd : nmOrd (geoTransformAlong K T) y = K.d)
    (hRun : regimeRun (OrdRegime K K.d) T y = T.length) :
    let O := ordMask K K.d
    let A := CMfd.of (n := n) O
    let P : MarkedIdeal n A := MarkedIdeal.pullback (Subtype.val : O → X) K
    let V := restrict O T
    ∃ hp : T.proj y ∈ O,
      let z : openPreimage T O := ⟨y, hp⟩
      IsInvDomain (k + 1) P ∧ IsMaximalOrderAlong P.N P.ideal P.d ∧
      IsCanonical P (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) P) V ∧
      z ∈ (geoTransformAlong P V).cosupp ∧
      (invFamily hn (k + 1)).inv K T y = positiveSuccessorRead K.d
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) P V z) := by
  intro O A P V
  let R := invFamily hn k
  let J : MarkedIdeal n A := compAt K K.d (.refl : BlowupTower X X)
  obtain ⟨_, hp, hJ, hMaxJ, hCanJ, hzJ, hRead⟩ :=
    original_positive_initial_order_companion hn K hK T hCan y hy K.d hOrd hK.one_le_d hRun
  let z : openPreimage T O := ⟨y, hp⟩
  let C := companionOf n K K.d
  have hC : IsInvDomain (k + 1) C := isInvDomain_companionAlong hn hK hK.one_le_d
  have hCK : RestrictEquiv C K := by
    unfold C
    rw [hEq]
    exact ⟨rfl, rfl, rfl, restrictLe_restrictOn, restrictLe_self_restrictOn hK.isWellFormed.isCoherent⟩
  have hJPEq : RestrictEquiv (M := O) J P := by
    have hJPull : J = MarkedIdeal.pullback (M' := A) (Subtype.val : O → X) C :=
      GeneralCompare.compAt_eq_pullback hn K.d (.refl : BlowupTower X X) hK
    rw [hJPull]
    exact ContactRepresentative.restrictEquiv_pullback_val O hCK
      hC.isWellFormed.isCoherent hK.isWellFormed.isCoherent
  have hP : IsInvDomain (k + 1) P := isInvDomain_pullback_val O hK
  have hMaxP : IsMaximalOrderAlong P.N P.ideal P.d := by
    intro x hx
    rw [← hJPEq.N_eq] at hx
    have hx' := MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe hJPEq.le (P.d + 1) hx
    rw [← hJPEq.d_eq] at hx'
    exact hMaxJ x hx'
  have hM := StepOneSeq.isMaxOrderValue_stepOneInvM (k := k + 1) R hn
  have hCanP := hM.isCanonical_of_restrictEquiv (X := A) hJ hMaxJ hP hMaxP hJPEq V hCanJ
  have hCos := (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong
    hJPEq hJ.isWellFormed.isClosedSubmanifold_N.1 hJ.isWellFormed.isCoherent hP.isWellFormed.isCoherent V).1
  have hVal := hM.representative (X := A) J P hJ hMaxJ hP hMaxP hJPEq V hCanJ z hzJ
  exact ⟨hp, hP, hMaxP, hCanP, hCos ▸ hzJ, hRead.trans (congrArg (positiveSuccessorRead K.d) hVal)⟩

end

end Hironaka.HironakaG1SameMarkInitialStepOne
