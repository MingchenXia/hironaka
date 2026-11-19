import Hironaka.Resolution.HironakaG1LocalizedBornWindowRestriction
import Hironaka.Resolution.HironakaG1AdvancingSupportedBornContact
import Hironaka.Resolution.HironakaG1NestedBareContactTransport
import Hironaka.Resolution.HironakaG1CompanionZeroBranchRecognition
import Hironaka.Resolution.HironakaG1ActualLaterOrderRun

/-! The finite zero clock of the second true-mark companion after a positive restart. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1RestartedSecondCompanionZero
noncomputable section
open Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres GeneralValue CompanionRebase CompanionReductionAlong GeneralCompare
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime
  StepOneValue StepOneValueMasked StepOneRegime InvDomainMemberRestriction InvDomainRebase InvDomainTowerAlong
  HomogenizedIdealAlong CoefficientIdealRestriction TangentDirectionAlong RestrictedIdealExtension
  ContactRepresentative MarkedIdealOperationsAlong.MarkedIdeal
  HironakaG1LocalizedBornWindowRestriction HironakaG1RecursiveMemberValueTransport
  HironakaG1AdvancingSupportedBornContact HironakaG1NestedBareContactTransport
  HironakaG1CompanionZeroBranchRecognition HironakaG1ActualLaterOrderRun HironakaG1LocalizedBornNormalHistory
  HironakaG8LocalHistory HironakaG8LocalRestrictEquiv

private theorem positive_refl_selected_avoids_anchor {n : ℕ} {X : CMfd.{0} n}
    (P : MarkedIdeal n X) (a : X) (W : Opens X) (ha : a ∈ W) :
    ∀ D ∈ (positiveMemberOn P (.refl (X := X)) a W).E, (⟨a, ha⟩ : W) ∉ D := by
  classical
  let B := barMarked (X := X) P
  have hOld : origMembers P (.refl (X := X)) = B.E := List.take_length
  intro D hD hInc
  change D ∈ (memberRestrict B (membersThrough B.E (origMembers P (.refl (X := X))) a)).E.map
    ((Subtype.val : W → X) ⁻¹' ·) at hD
  rw [memberRestrict_membersThrough_E] at hD
  obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hD
  obtain ⟨hIn, hKeep⟩ := List.mem_filter.mp hF
  exact (of_decide_eq_true hKeep) ⟨hOld.symm ▸ hIn, hInc⟩

private theorem off_mapped_slots {X Y : Type*} (f : Y → X) (E : List (Set X)) (y : Y)
    (h : ∀ D ∈ E, f y ∉ D) : ∀ D ∈ E.map (f ⁻¹' ·), y ∉ D := by
  intro D hD
  obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hD
  exact h F hF

set_option maxHeartbeats 1600000 in
/-- The actual companion of the restarted positive selection has a finite
zero letter and its run starts at the actual order-mask source. The paired
bare contact data provide the strict supported trace on that same mask.
The order bounds and original canonicality are those of the literal
selected history. -/
theorem restarted_second_true_mark_companion_zero {n k l : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (P R : MarkedIdeal n X) (a : X) (u : X → ℂ) (W : Opens X)
    (ha : a ∈ W) (hPair : LocalizedBornWindowData (k := k+2) (l := l) hn P R a u W) :
    let A := CMfd.of (n := n) W
    let K := positiveMemberOn P (.refl (X := X)) a W
    let F := positiveMemberOn R (.refl (X := X)) a W
    let C := ordMask K K.d
    let B := CMfd.of (n := n) C
    let J := compAt K K.d (.refl (X := A))
    let Fc := MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) F
    let v : C → ℂ := fun x => u x.val.val
    (∀ x ∈ K.cosupp, nmOrd K x = K.d) →
    companionOf n K K.d =
      (⟨K.N, K.E, restrictOn n K.N K.ideal, K.d⟩ : MarkedIdeal n A) →
    ∀ {Y : CMfd.{0} n} (T : BlowupTower A Y),
      IsCanonical K ((invFamily hn (k+1)).inv K) T →
      ∀ y ∈ (geoTransformAlong K T).cosupp,
      T.proj y = (⟨a, ha⟩ : W) →
      ∃ hp : T.proj y ∈ C,
        let V := restrict C T
        let z : openPreimage T C := ⟨y, hp⟩
        IsInvDomain (k+1) J ∧ IsInvDomain (l-1) Fc ∧ LocWPEquiv (X := B) J Fc ∧
        (J.N ∩ {x : C | v x = 0} = Fc.N) ∧
        IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) V ∧
        z ∈ (geoTransformAlong J V).cosupp ∧
        stepRegime J 0 V z ∧ regimeRun (stepRegime J 0) V z = V.length := by
  intro A K F C B J Fc v hBase hEq Y T hCan y hy hyA
  let w : W → ℂ := u ∘ (Subtype.val : W → X)
  let Cut := withN (coeffMarkedAlong K) (K.N ∩ {x : W | w x = 0})
  obtain ⟨hK, hu, hTrace, _, hLoc, _, _, _, hCut, hF, _, _⟩ := hPair
  have hk : k + 2 - 1 = k + 1 := by omega
  have hDomK : IsInvDomain (k+1) K := hk ▸ hK
  have ht : IsTangentDirectionAlong K.N K.ideal K.d univ w := hu
  have hNF : K.N ∩ {x : W | w x = 0} = F.N := hTrace
  have hKF : LocWPEquiv (X := A) K F :=
    supported_contact_local_class K F hDomK w ht hNF hF.isWellFormed.isClosedSubmanifold_N hLoc
  obtain ⟨hDomJ, hv, _, _⟩ := nested_initial_bare_contact_data (l := l-1) hn K hDomK w ht hEq hCut
  let Kc := MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) K
  let Kcomp := companionOf n K K.d
  have hDomKcomp : IsInvDomain (k+1) Kcomp :=
    InvDomainCompanion.isInvDomain_companionAlong (X := A) (𝔪 := K) hn hDomK hDomK.one_le_d
  have hKcompJ : MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) Kcomp = J :=
    pullback_val_companionOf hn hDomK.isWellFormed hDomK.isNonzeroAlongAt C K.d
  have hKRE : RestrictEquiv K Kcomp := by
    rw [show Kcomp = _ from hEq]
    exact ⟨rfl, rfl, rfl, restrictLe_self_restrictOn hDomK.isWellFormed.isCoherent, restrictLe_restrictOn⟩
  have hKcRE : RestrictEquiv Kc J := by
    rw [← hKcompJ]
    exact restrictEquiv_pullback_val C hKRE hDomK.isWellFormed.isCoherent hDomKcomp.isWellFormed.isCoherent
  have hDomKc := isInvDomain_pullback_val C hDomK
  have hDomFc : IsInvDomain (l-1) Fc := isInvDomain_pullback_val C hF
  have hJF : LocWPEquiv (X := B) J Fc :=
    (locWPEquiv_of_restrictEquiv hDomKc hDomJ hKcRE).symm.trans (hKF.restrict C)
  have hTraceC : J.N ∩ {x : C | v x = 0} = Fc.N := by
    rw [← hKcRE.N_eq]
    change ((Subtype.val : C → W) ⁻¹' K.N) ∩ {x : C | w x.val = 0} =
      (Subtype.val : C → W) ⁻¹' F.N
    rw [← hNF]
    rfl
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical hDomK T hCan
  have hOrders {Z : CMfd.{0} n} (U : BlowupTower A Z) (hU : IsGeoTestTower K U) :
      ∀ z ∈ (geoTransformAlong K U).cosupp, nmOrd (geoTransformAlong K U) z = K.d :=
    (same_mark_test_order_and_strict_contact hn K hDomK w ht hBase hEq U hU).1
  have hRun := order_run_of_all_test_orders K hDomK K.d (fun U => hOrders U) T hT y hy
  obtain ⟨hBoundary, hp, _, hMaxJ, hCanJ, hz, _⟩ :=
    original_positive_initial_order_companion hn K hDomK T hCan y hy K.d
      (hOrders T hT y hy) hDomK.one_le_d hRun
  let V := restrict C T
  let z : openPreimage T C := ⟨y, hp⟩
  have hV := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (X := B) (k := k+1)
    (invFamily hn k) J hDomJ hMaxJ hn V hCanJ).2.1
  have hProj : ((V.proj z : C).val : W) = (⟨a, ha⟩ : W) := (proj_restrict C T z).trans hyA
  have hOffK : ∀ D ∈ K.E, (V.proj z : C).val ∉ D := by
    intro D hD
    rw [hProj]
    exact positive_refl_selected_avoids_anchor P a W ha D hD
  have hOffJ : ∀ D ∈ J.E, V.proj z ∉ D :=
    hBoundary.symm ▸ off_mapped_slots (Subtype.val : C → A) K.E (V.proj z) hOffK
  have hZero := zero_step_regime_of_strict_supported_trace J Fc hDomJ hDomFc hJF v hv hTraceC V hV z hOffJ
  exact ⟨hp, hDomJ, hDomFc, hJF, hTraceC, hCanJ, hz, hZero⟩

end
end Hironaka.HironakaG1RestartedSecondCompanionZero
