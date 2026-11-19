import Hironaka.Resolution.HironakaG1LocalizedBornFullZeroRead
import Hironaka.Resolution.HironakaG1ActualLaterOrderRun
import Hironaka.Resolution.HironakaG1ActualLaterCommonTangent
import Hironaka.Resolution.HironakaG3RRawStepOneLocality

/-! The literal Step One order-companion history on a common open window. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1ActualCompanionWindowRead

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  ResolutionInvariantSpec CanonicalCentres HomogenizedIdealAlong
  StepOneValue StepOneValueMasked StepOneRegime
  HironakaG3RRawStepOneLocality HironakaG3RRawRegimeLocality
  HironakaG1ActualLaterOrderRun InvDomainTowerAlong RelativePrincipalizationSpan

/-- A literal open restriction preserves the canonical companion history,
its value and its own Step One phase clock at every surviving point. -/
theorem step_one_open_window_history {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J : MarkedIdeal n X) (hJ : IsInvDomain (k + 1) J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d)
    (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) T)
    (W : Opens X) (z : openPreimage T W)
    (hz : z.val ∈ (geoTransformAlong J T).cosupp) :
    let A := CMfd.of (n := n) W
    let K := MarkedIdeal.pullback (M' := A) (Subtype.val : W → X) J
    let S := restrict W T
    let I := invFamily hn k
    IsInvDomain (k + 1) K ∧ IsMaximalOrderAlong K.N K.ideal K.d ∧
      IsCanonical K (Seq.StepOneValueMasked.stepOneInvM I K) S ∧
      z ∈ (geoTransformAlong K S).cosupp ∧
      Seq.StepOneValueMasked.stepOneInvM I K S z =
        Seq.StepOneValueMasked.stepOneInvM I J T z.val ∧
      level K S z = level J T z.val ∧
      (IsSpecial K S z ↔ IsSpecial J T z.val) ∧
      (∀ b, regimeRun (stepRegime K b) S z = regimeRun (stepRegime J b) T z.val) ∧
      S.length = T.length := by
  intro A K S I
  have hHol : ∀ x f, J.ideal.mem x f → HolomorphicAt n f x :=
    fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hJ.isWellFormed.isCoherent h
  have hK : IsInvDomain (k + 1) K := isInvDomain_pullback_val W hJ
  have hMaxK : IsMaximalOrderAlong K.N K.ideal K.d := by
    intro a ha
    have hEq := cosupp_pullback_val (⟨J.N,J.E,J.ideal,J.d+1⟩ : MarkedIdeal n X) hHol W
    have hm : a ∈ (MarkedIdeal.pullback (Subtype.val : W → X)
      (⟨J.N,J.E,J.ideal,J.d+1⟩ : MarkedIdeal n X)).cosupp := ha
    rw [hEq] at hm
    exact hMax a.val hm
  have hBar := (Seq.StepOneBridge.isCanonical_iff I J hJ hMax hn T).mp hCan
  obtain ⟨hBarW, hEval⟩ := Seq.StepOneRestrictOpen.stepOneInvM_restrict (k := k + 1) J W I
    hJ.isWellFormed hJ.one_le_d hn hMax hJ.dimLE T hBar
  have hCanW := (Seq.StepOneBridge.isCanonical_iff I K hK hMaxK hn S).mpr hBarW
  have hzW : z ∈ (geoTransformAlong K S).cosupp := by
    change z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) J) (restrict W T)).cosupp
    rw [cosupp_restrict_raw J hHol W T]
    exact hz
  have hzBar := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical I J hJ hMax hn T hCan).2.2.symm ▸ hz
  have hFacts := (restrict_facts_raw J W hJ.isWellFormed hJ.one_le_d T).2 z
  exact ⟨hK, hMaxK, hCanW, hzW, hEval z hzBar, hFacts.1, hFacts.2.1,
    fun b => regimeRun_stepRegime_restrict_raw J W hJ.isWellFormed hJ.one_le_d b T z,
    length_restrict W T⟩

open scoped Manifold ContDiff

open BlowupTowerSplit GeneralValue NonmonomialOrderTail
  HironakaG8LocalHistory TangentDirectionAlong
  HironakaG1InitialPositiveGeneralRead HironakaG1ActualLaterCommonTangent
  HironakaG1LaterPositiveSuccessorRead HironakaG1PositiveNormalPhase
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaActualOpenZeroSectionDifferentials HironakaG1LocalizedLaterBornCanonical
  HironakaG1LocalizedBornFullZeroRead HironakaG1AdvancingSupportedBornContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG1RecursiveMemberValueTransport

set_option maxHeartbeats 1400000 in
private theorem full_zero_contact_of_window {n k b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J : MarkedIdeal n X) (hJ : IsInvDomain (k+2) J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J) T)
    (W : Opens X) (z : openPreimage T W)
    (hz : z.val ∈ (geoTransformAlong J T).cosupp)
    (hLev : level J T z.val = b+1) (hNS : ¬ IsSpecial J T z.val)
    (hRun : regimeRun (stepRegime J (b+1)) T z.val = T.length)
    (R : MarkedIdeal n (CMfd.of (n := n) W)) (hR : IsInvDomain (k+1) R)
    (u : W → ℂ)
    (a : W) (ha : a ∈ R.N) (hp : (restrict W T).proj z = a)
    (hInitNS : ¬ IsSpecial R (.refl : BlowupTower (CMfd.of (n := n) W) _) a)
    (hCut :
      let K := MarkedIdeal.pullback (Subtype.val : W → X) J
      IsInvDomain (k+2) K ∧ LocWPEquiv K R ∧
        IsTangentDirectionAlong K.N K.ideal K.d univ u ∧
        K.N ∩ {x : W | u x = 0} = R.N ∧
        level K (.refl : BlowupTower (CMfd.of (n := n) W) _) a = b+1) :
    ∃ (wmark : ℕ) (D F : CMfd.{0} n)
      (C₁ C₂ : MarkedIdeal n D) (T₀ : BlowupTower D F) (w : F),
      IsInvDomain k C₁ ∧ IsInvDomain k C₂ ∧ C₁.N = C₂.N ∧ C₁.E = C₂.E ∧
      IsCanonical C₁ ((invFamily hn k).inv C₁) T₀ ∧
      IsCanonical C₂ ((invFamily hn k).inv C₂) T₀ ∧
      w ∈ (geoTransformAlong C₁ T₀).cosupp ∧ w ∈ (geoTransformAlong C₂ T₀).cosupp ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J T z.val =
        toLex (b+1, (positiveSuccessorRead wmark
          (toLex (0, ((invFamily hn k).inv C₁ T₀ w : WithTop (ValTy k)))) :
            WithTop (ValTy (k+1)))) := by
  let D₀ := CMfd.of (n := n) W
  let K : MarkedIdeal n D₀ := MarkedIdeal.pullback (Subtype.val : W → X) J
  let S := restrict W T
  obtain ⟨hK, hClass, hu, hTrace, hInit⟩ := hCut
  obtain ⟨_, hMaxK, hCanK, hzK, hReadW, hLevel, hSpecial, hClock, hlen⟩ :=
    step_one_open_window_history (k := k+1) hn J hJ hMax T hCan W z hz
  have ha' : S.proj z ∈ R.N := Eq.mpr (congrArg (fun v : D₀ => v ∈ R.N) hp) ha
  have hWitness := localized_born_witness_of_supported_nonspecial (k := k+2) (l := k+1)
    hn K R hK hR hClass a ha u hu hTrace hInit hInitNS
  have hWitness' : LocalizedBornWitness (k := k+2) (l := k+1) hn K R (S.proj z) u :=
    Eq.mpr (congrArg (fun v : D₀ => LocalizedBornWitness (k := k+2) (l := k+1)
      hn K R v u) hp) hWitness
  obtain ⟨W', hpW', _, _, _, hpC, _, _, _, _, hpO, hD, hCanD, hCosD,
      hR', hCanR', hCosR', hN, hE, _, _, hRead⟩ :=
    exists_localized_born_full_zero_read (k := k) (b := b) hn K R hK hR hClass hMaxK u hu hTrace
      S hCanK z hzK ha' (hLevel.trans hLev) (fun h => hNS (hSpecial.mp h))
      ((hClock (b+1)).trans (hRun.trans hlen.symm)) hWitness'
  exact ⟨_, _, _, _, _, _, _, hD, hR', hN, hE, hCanD, hCanR', hCosD, hCosR',
    hReadW.symm.trans hRead⟩

set_option maxHeartbeats 4000000 in
/-- The actual initial order companion keeps the original outer letter
when its own full positive phase is read on the actual common tangent
window and its next true-mark phase reaches advancing zero contact. -/
theorem original_upper_born_full_zero_read {n k s b : ℕ}
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
    let R := MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) (positiveMemberOn Sec H p O)
    (¬ IsSpecial Sec H p) →
    let V := restrict O S
    let U₀ := restrict C V
    (∀ z : openPreimage V C, z.val.val = y →
      level J U₀ z = b + 1 ∧ ¬ IsSpecial J U₀ z ∧
        regimeRun (stepRegime J (b + 1)) U₀ z = U₀.length) →
    (∀ (a : C) (W : Opens B) (haW : a ∈ W), a.val.val = p →
      let D := CMfd.of (n := n + 1) W
      let Jw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) J
      let Rw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) R
      level Jw (.refl : BlowupTower D D) ⟨a, haW⟩ = b + 1 ∧
        ¬ IsSpecial Rw (.refl : BlowupTower D D) ⟨a, haW⟩) →
    ∃ (wmark : ℕ) (D A' : CMfd.{0} (n + 1))
      (C₁ C₂ : MarkedIdeal (n + 1) D) (T₀ : BlowupTower D A') (z : A'),
      IsInvDomain k C₁ ∧ IsInvDomain k C₂ ∧ C₁.N = C₂.N ∧ C₁.E = C₂.E ∧
      IsCanonical C₁ ((invFamily (Nat.succ_pos n) k).inv C₁) T₀ ∧
      IsCanonical C₂ ((invFamily (Nat.succ_pos n) k).inv C₂) T₀ ∧
      z ∈ (geoTransformAlong C₁ T₀).cosupp ∧ z ∈ (geoTransformAlong C₂ T₀).cosupp ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 2)) P T y =
        toLex (s + 1, (positiveSuccessorRead L.d
          (toLex (b + 1, (positiveSuccessorRead wmark
            (toLex (0, ((invFamily (Nat.succ_pos n) k).inv C₁ T₀ z : WithTop (ValTy k)))) :
              WithTop (ValTy (k + 1))))) : WithTop (ValTy (k + 2)))) := by
  intro X P Sec r H S p O A L C B J R hNSS V U₀ hPhase hBorn
  let hn : 0 < n + 1 := Nat.succ_pos n
  obtain ⟨hp, _, _, hInitial⟩ :=
    original_upper_positive_successor_at_initial_order_companion (k := k+1)
      Q hQ T hCan y hy hLevel hNS
  obtain ⟨hq, hJ, hMax, hCanJ, hz, hOuter⟩ := hInitial
  let z : openPreimage V C := ⟨⟨y, hp⟩, hq⟩
  obtain ⟨a, W, u, haW, ha, hJw, hRw, hClass, hTan, hTrace, haR, _, _, _⟩ :=
    exists_actual_later_common_supported_tangent (k := k+1) Q hQ T hCan y hy hLevel hNS hNSS
  have hproj : (U₀.proj z).val.val = p := by
    change ((restrict C V).proj z).val.val = _
    rw [show ((restrict C V).proj z).val = V.proj z.val from proj_restrict C V z]
    exact proj_restrict O S z.val
  have hEq : U₀.proj z = a := Subtype.ext (Subtype.ext (hproj.trans ha.symm))
  have hpW : U₀.proj z ∈ W := hEq.symm ▸ haW
  let zw : openPreimage U₀ W := ⟨z, hpW⟩
  obtain ⟨hl₀, hns₀, hr₀⟩ := hPhase z rfl
  obtain ⟨hi, hnsInitial⟩ := hBorn a W haW ha
  let D₀ := CMfd.of (n := n+1) W
  let R₀ : MarkedIdeal (n+1) D₀ := MarkedIdeal.pullback (Subtype.val : W → B) R
  let a₀ : D₀ := ⟨a, haW⟩
  have hBase : (restrict W U₀).proj zw = a₀ :=
    Subtype.ext ((proj_restrict W U₀ zw).trans hEq)
  obtain ⟨m, D, Z, C₁, C₂, T₀, w, hD, hR', hN, hE, hCanD, hCanR', hCosD, hCosR', hRead⟩ :=
    full_zero_contact_of_window (k := k) (b := b) hn J hJ hMax U₀ hCanJ W zw hz hl₀ hns₀ hr₀
      R₀ hRw u a₀ haR hBase hnsInitial ⟨hJw, hClass, hTan, hTrace, hi⟩
  refine ⟨m, D, Z, C₁, C₂, T₀, w, hD, hR', hN, hE, hCanD, hCanR', hCosD, hCosR', ?_⟩
  exact hOuter.trans (congrArg (fun v : ℕ ×ₗ WithTop (ValTy (k+1)) =>
    toLex (s+1, (positiveSuccessorRead L.d v : WithTop (ValTy (k+2)))))
      hRead)

#print axioms step_one_open_window_history
#print axioms original_upper_born_full_zero_read

end Hironaka.HironakaG1ActualCompanionWindowRead
