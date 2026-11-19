import Hironaka.Resolution.HironakaG1ChronologicalCompanionSuffix

/-! The actual upper order companion read through its chronological next positive suffix. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace Classical
open scoped Manifold ContDiff Topology

namespace Hironaka.HironakaG1ActualChronologicalNext

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres ResolutionInvariantExt
  StepOneValue StepOneValueMasked StepOneRegime HomogenizedIdealAlong BoundaryCount
  InvDomainRebase InvDomainMemberRestriction InvDomainTowerAlong MemberInterTowerAlong
  HironakaG1RecursiveMemberValueTransport HironakaG8LocalHistory HironakaG8HomStable
  HironakaG1LaterContactFieldExistence HironakaG1LaterSelectedNormalTangent
  HironakaCoherentTransformExtension TangentDirectionAlong ContactEquivalenceAlong
  RelativePrincipalizationSpan GiraudAlong
open HomogenizedGlueingTower (strictAlong)

open HironakaG1ChronologicalCompanionSuffix

open HironakaG1ActualCompanionWindowRead

/-- The ordinary inherited tangent directly supplies the next selected
canonical suffix and its supported contact, even when the positive run
begins at an interior head of the companion test. -/
theorem next_positive_of_ordinary_supported_tangent {n k l b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J R : MarkedIdeal n X) (hJ : IsInvDomain (k+1) J)
    (hR : IsInvDomain l R) (hClass : LocWPEquiv J R)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) T)
    (y : Y) (hy : y ∈ (geoTransformAlong J T).cosupp)
    (hLevel : level J T y = b+1) (hNS : ¬ IsSpecial J T y)
    (u : X → ℂ) (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (hTrace : J.N ∩ {x | u x = 0} = R.N)
    (hAnchor : T.proj y ∈ R.N) :
    ∃ (D F : CMfd.{0} n) (K C G : MarkedIdeal n D) (S : BlowupTower D F) (z : F),
      IsInvDomain k K ∧ IsCanonical K ((invFamily hn k).inv K) S ∧
      IsGeoTestTower K S ∧ z ∈ (geoTransformAlong K S).cosupp ∧
      C.N = G.N ∧ C.E = G.E ∧ LocWPEquiv C G ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J T y =
        toLex (b+1, ((invFamily hn k).inv K S z : WithTop (ValTy k))) := by
  obtain ⟨W, hp, huW, hTraceW⟩ :=
    exists_companion_source_bar_tangent_window hn J R hJ hR hClass.wEquiv.1
      (T.proj y) hAnchor u hu hTrace
  let A := CMfd.of (n := n) W
  let Jw : MarkedIdeal n A := MarkedIdeal.pullback (Subtype.val : W → X) J
  let Rw : MarkedIdeal n A := MarkedIdeal.pullback (Subtype.val : W → X) R
  let V := restrict W T
  let x : openPreimage T W := ⟨y, hp⟩
  obtain ⟨hJw, hMaxW, hCanW, hx, hVal, hl, hs, _, _⟩ :=
    step_one_open_window_history hn J hJ hMax T hCan W x hy
  have hRw : IsInvDomain l Rw := isInvDomain_pullback_val W hR
  have hClassW : LocWPEquiv Jw Rw := hClass.restrict W
  obtain ⟨U, v, _, _, _, _, _, hN, hE, _, _, hCW, hU, hK, hCanK, hTestK, hz, hRead⟩ :=
    positive_companion_chronological_tangent (b := b) hn Jw Rw hJw hRw hClassW
      hMaxW V hCanW x hx (hl.trans hLevel) (fun h => hNS (hs.mp h)) _ huW hTraceW
  exact ⟨_, _, _, _, _, _, _, hK, hCanK, hTestK, hz, hN, hE, hCW, hVal.symm.trans hRead⟩

open BlowupTowerSplit GeneralValue NonmonomialOrderTail
  HironakaG8LocalHistory TangentDirectionAlong
  HironakaG1InitialPositiveGeneralRead HironakaG1ActualLaterCommonTangent
  HironakaG1LaterPositiveSuccessorRead HironakaG1PositiveNormalPhase
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaActualOpenZeroSectionDifferentials HironakaG1LocalizedLaterBornCanonical
  HironakaG1LocalizedBornFullZeroRead HironakaG1AdvancingSupportedBornContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG1RecursiveMemberValueTransport

open HironakaG1ActualCompanionWindowRead HironakaG1ActualLaterOrderRun

set_option maxHeartbeats 2400000 in
/-- The actual upper order companion reads its next positive phase at the
literal run head. The retained list is computed against the source slots
of that companion and the new slots keep their chronological places. -/
theorem original_upper_chronological_next_positive {n k s b : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 2) Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 2)) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let r := regimeRun (stepRegime P (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA P H p
    let A := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X) P (s + 1) H p
    let C := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) L.d
    let B := CMfd.of (n := n + 1) C
    let J := compAt L L.d (.refl : BlowupTower A A)
    let _R := MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) (positiveMemberOn Sec H p O)
    (¬ IsSpecial Sec H p) →
    let V := restrict O S
    let U₀ := restrict C V
    (∀ z : openPreimage V C, z.val.val = y →
      level J U₀ z = b + 1 ∧ ¬ IsSpecial J U₀ z) →
    ∃ (D F : CMfd.{0} (n+1)) (K Cut R' : MarkedIdeal (n+1) D)
      (U' : BlowupTower D F) (w : F),
      IsInvDomain (k+1) K ∧
      IsCanonical K ((invFamily (Nat.succ_pos n) (k+1)).inv K) U' ∧
      IsGeoTestTower K U' ∧ w ∈ (geoTransformAlong K U').cosupp ∧
      Cut.N = R'.N ∧ Cut.E = R'.E ∧ LocWPEquiv Cut R' ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k+2)) P T y =
          toLex (s+1, (positiveSuccessorRead L.d
            (toLex (b+1, ((invFamily (Nat.succ_pos n) (k+1)).inv K U' w :
                WithTop (ValTy (k+1))))) : WithTop (ValTy (k+2)))) := by
  intro X P Sec r H S p O A L C B J R hNSS V U₀ hPhase
  let hn : 0 < n+1 := Nat.succ_pos n
  obtain ⟨hp, _, _, hInitial⟩ :=
    original_upper_positive_successor_at_initial_order_companion (k := k+1)
      Q hQ T hCan y hy hLevel hNS
  obtain ⟨hq, hJ, hMax, hCanJ, hz, hOuter⟩ := hInitial
  let z : openPreimage V C := ⟨⟨y, hp⟩, hq⟩
  obtain ⟨hl, hs⟩ := hPhase z rfl
  obtain ⟨a, O₀, u, haO, ha, hJ₀, hR₀, hClass, hTan, hTrace, haR, _, _, _⟩ :=
    exists_actual_later_common_supported_tangent (k := k+1) Q hQ T hCan y hy hLevel hNS hNSS
  have hproj : (U₀.proj z).val.val = p := by
    change ((restrict C V).proj z).val.val = _
    rw [show ((restrict C V).proj z).val = V.proj z.val from proj_restrict C V z]
    exact proj_restrict O S z.val
  have haEq : U₀.proj z = a := Subtype.ext (Subtype.ext (hproj.trans ha.symm))
  let B₀ := CMfd.of (n := n+1) O₀
  let J₀ : MarkedIdeal (n+1) B₀ := MarkedIdeal.pullback (Subtype.val : O₀ → B) J
  let R₀ : MarkedIdeal (n+1) B₀ := MarkedIdeal.pullback (Subtype.val : O₀ → B) R
  let a₀ : O₀ := ⟨a, haO⟩
  let T₀ := restrict O₀ U₀
  have hzO₀ : U₀.proj z ∈ O₀ := haEq.symm ▸ haO
  let z₀ : openPreimage U₀ O₀ := ⟨z, hzO₀⟩
  have hz₀Proj : T₀.proj z₀ = a₀ := Subtype.ext ((proj_restrict O₀ U₀ z₀).trans haEq)
  have hAnchor : T₀.proj z₀ ∈ R₀.N := Eq.mpr (congrArg (fun x : B₀ => x ∈ R₀.N) hz₀Proj) haR
  obtain ⟨_, hMax₀, hCan₀, hz₀, hVal₀, hl₀, hs₀, _, _⟩ :=
    step_one_open_window_history (k := k+1) hn J hJ hMax U₀ hCanJ O₀ z₀ hz
  obtain ⟨D, F, K, Cut, G, V', w, hK, hCanK, hTestK, hCosK, hN, hE, hCut, hRead⟩ :=
    next_positive_of_ordinary_supported_tangent (b := b) hn J₀ R₀ hJ₀ hR₀ hClass
      hMax₀ T₀ hCan₀ z₀ hz₀ (hl₀.trans hl) (fun h => hs (hs₀.mp h)) u hTan hTrace hAnchor
  refine ⟨D, F, K, Cut, G, V', w, hK, hCanK, hTestK, hCosK, hN, hE, hCut, ?_⟩
  exact hOuter.trans (congrArg (fun q : ℕ ×ₗ WithTop (ValTy (k+1)) =>
    toLex (s+1, (positiveSuccessorRead L.d q : WithTop (ValTy (k+2)))))
      (hVal₀.symm.trans hRead))

#print axioms next_positive_of_ordinary_supported_tangent
#print axioms original_upper_chronological_next_positive

end Hironaka.HironakaG1ActualChronologicalNext
