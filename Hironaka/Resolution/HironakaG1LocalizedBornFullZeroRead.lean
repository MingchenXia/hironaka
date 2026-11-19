import Hironaka.Resolution.HironakaG1RestartedSecondCompanionZero
import Hironaka.Resolution.HironakaG1SupportedGapEmptyEpoch
import Hironaka.Invariant.StepOneEmptyPrefix
import Hironaka.Resolution.HironakaG1LocalizedBornWindowRestriction
import Hironaka.Resolution.HironakaG1LocalizedLaterBornRead
import Hironaka.Resolution.HironakaG1TrueMarkZeroContactRead

/-! The actual next-born window and its advancing zero contact. -/

set_option autoImplicit false

open Set TopologicalSpace

namespace Hironaka.HironakaG1LocalizedBornFullZeroRead

noncomputable section

open Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres HomogenizedIdealAlong ContactStageKept
  GeneralValue NonmonomialOrderTail TangentDirectionAlong StepOneValue StepOneRegime
  HironakaG8LocalHistory HironakaG1InitialPositiveGeneralRead HironakaG1RecursiveMemberValueTransport
  HironakaG1LocalizedLaterBornCanonical HironakaG1LocalizedLaterBornRead
  HironakaG1LocalizedBornNormalOrder HironakaG1LocalizedBornWindowRestriction
  HironakaG1TrueMarkZeroContactRead HironakaG1RestartedSecondCompanionZero
  HironakaG1AdvancingSupportedBornContact HironakaG1SupportedGapEmptyEpoch
  HironakaG1DifferentCarrierMemberClassData HironakaCoherentTransformExtension
  InvDomainMemberRestriction InvDomainTowerAlong RestrictEmptyTower ResolutionInvariantExt
open HomogenizedGlueingTower (strictAlong)
open scoped Manifold ContDiff

set_option maxHeartbeats 2100000 in
/-- A common actual next-born window supports both the prescribed-to-section
comparison and the true-mark read of the original positive branch. The
actual companion has a full finite zero run. Its prescribed contact lies
on the strict transform of the supported selected carrier and gives the
entire original upper letter there. -/
theorem exists_localized_born_full_zero_read {n k b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (P R : MarkedIdeal n X) (hP : IsInvDomain (k + 2) P) (hR : IsInvDomain (k+1) R)
    (hClass : LocWPEquiv P R) (hMax : IsMaximalOrderAlong P.N P.ideal P.d)
    (u : X → ℂ) (hu : IsTangentDirectionAlong P.N P.ideal P.d univ u)
    (hTrace : P.N ∩ {x | u x = 0} = R.N)
    (T : BlowupTower X Y)
    (hCan : IsCanonical P (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k + 1)) P) T)
    (y : Y) (hy : y ∈ (geoTransformAlong P T).cosupp) (ha : T.proj y ∈ R.N)
    (hLevel : level P T y = b + 1) (hNS : ¬ IsSpecial P T y)
    (hRun : regimeRun (stepRegime P (b + 1)) T y = T.length)
    (hWitness : LocalizedBornWitness (k := k + 2) (l := k+1) hn P R (T.proj y) u) :
    let H : BlowupTower X X := .refl
    ∃ (W : Opens X) (hpW : T.proj y ∈ W),
      W ≤ maskA P H (T.proj y) ∧ W ≤ maskA R H (T.proj y) ∧
      LocalizedBornWindowData (k := k + 2) (l := k+1) hn P R (T.proj y) u W ∧
      let A := CMfd.of (n := n) W
      let K := positiveMemberOn P H (T.proj y) W
      let F := positiveMemberOn R H (T.proj y) W
      let U := restrict W T
      let z : openPreimage T W := ⟨y, hpW⟩
      let C := ordMask K K.d
      let B := CMfd.of (n := n) C
      let J := compAt K K.d (.refl : BlowupTower A A)
      let Kc := MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) K
      let Fc := MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) F
      let v : C → ℂ := fun x => u x.val.val
      let V := restrict C U
      ∃ hpC : U.proj z ∈ C,
        let w : openPreimage U C := ⟨z, hpC⟩
        IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) V ∧
        w ∈ (geoTransformAlong J V).cosupp ∧
        stepRegime J 0 V w ∧ regimeRun (stepRegime J 0) V w = V.length ∧
          let r := regimeRun (stepRegime J 0) V w
          let G := head V r
          let S := tail V r
          let p := S.proj w
          let O := maskB J G p
          let D := contactMarkedKept Kc v G O
          let R' := MarkedIdeal.pullback (M' := CMfd.of (n := n) O)
            (Subtype.val : O → (split V r).1) (geoTransformAlong Fc G)
          ∃ hpO : p ∈ O,
            let a : openPreimage S O := ⟨w, hpO⟩
            IsInvDomain k D ∧ IsCanonical D ((invFamily hn k).inv D) (restrict O S) ∧
            a ∈ (geoTransformAlong D (restrict O S)).cosupp ∧
            IsInvDomain k R' ∧ IsCanonical R' ((invFamily hn k).inv R') (restrict O S) ∧
            a ∈ (geoTransformAlong R' (restrict O S)).cosupp ∧
            D.N = R'.N ∧ D.E = R'.E ∧
            D.N = (Subtype.val : O → _) ⁻¹' strictAlong G Fc.N ∧
            D.E = (geoTransformAlong (barMarked J) G).E.map ((Subtype.val : O → _) ⁻¹' ·) ∧
            Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k + 1)) P T y =
              toLex (b + 1, (positiveSuccessorRead K.d
                (toLex (0, ((invFamily hn k).inv D (restrict O S) a : WithTop (ValTy k)))) :
                  WithTop (ValTy (k + 1)))) := by
  intro H
  obtain ⟨V₀, haV₀, hV₀P, hV₀R, hData⟩ := hWitness
  have hData₀ : LocalizedBornWindowData (k := k + 2) (l := k+1) hn P R (T.proj y) u V₀ := hData
  obtain ⟨W, hpW, hWV₀, _, hTan, _, _, hBase, hEq⟩ :=
    exists_localized_born_normal_order_subwindow hn P R hP hR hClass (T.proj y) ha u hu hTrace
      V₀ haV₀ hData₀.1
  have hWP := hWV₀.trans hV₀P
  have hWR := hWV₀.trans hV₀R
  have hPair := localized_born_window_data_restrict hn P R hP hR (T.proj y) u hWV₀ hData₀
  let A := CMfd.of (n := n) W
  let K := positiveMemberOn P H (T.proj y) W
  let F := positiveMemberOn R H (T.proj y) W
  let U := restrict W T
  let z : openPreimage T W := ⟨y, hpW⟩
  let C := ordMask K K.d
  let B := CMfd.of (n := n) C
  let Kc := MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) K
  let Fc := MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) F
  obtain ⟨hK, hCanK, hz, hOuter⟩ :=
    localized_positive_stepOne_finite_read hn P hP hMax T hCan y hy hLevel hNS hRun W hWP hpW
  obtain ⟨hpC, hCanJ, hw, hZero⟩ := true_mark_original_advancing_zero_read hn K hK
    (u ∘ (Subtype.val : W → X)) hTan hBase hEq U hCanK z hz
  have hProj : U.proj z = (⟨T.proj y, hpW⟩ : W) := Subtype.ext (proj_restrict W T z)
  obtain ⟨hpC', _, _, _, _, _, _, hReg, hClock⟩ :=
    restarted_second_true_mark_companion_zero hn P R (T.proj y) u W hpW hPair
      hBase hEq U hCanK z hz hProj
  let J := compAt K K.d (.refl (X := A))
  let V := restrict C U
  let w : openPreimage U C := ⟨z, hpC⟩
  let r := regimeRun (stepRegime J 0) V w
  let G := head V r
  let S := tail V r
  let p := S.proj w
  let O := maskB J G p
  let D := contactMarkedKept Kc (fun x : C => u x.val.val) G O
  let R' := MarkedIdeal.pullback (M' := CMfd.of (n := n) O)
    (Subtype.val : O → (split V r).1) (geoTransformAlong Fc G)
  have hReg' : stepRegime J 0 V w := hReg
  have hClock' : r = V.length := hClock
  obtain ⟨hpO, hD, hCanD, ha', hCarrier, hBoundary, hRead⟩ := hZero hReg'.1 hReg'.2
  have hSelectedTrace : K.N ∩ {x : W | u x.val = 0} = F.N := hPair.2.2.1
  have hMaskTrace : Kc.N ∩ {x : C | u x.val.val = 0} = Fc.N := by
    change ((Subtype.val : C → W) ⁻¹' K.N) ∩ {x : C | u x.val.val = 0} =
      (Subtype.val : C → W) ⁻¹' F.N
    rw [← hSelectedTrace]
    rfl
  have hTraceOnHead :
      (Subtype.val : O → (split V r).1) ⁻¹' strictAlong G (Kc.N ∩ {x : C | u x.val.val = 0}) =
        (Subtype.val : O → (split V r).1) ⁻¹' strictAlong G Fc.N :=
    congrArg (fun F => (Subtype.val : O → (split V r).1) ⁻¹' strictAlong G F) hMaskTrace
  have hF : IsInvDomain k F := by
    have hk : k+1-1 = k := by omega
    exact hk ▸ hPair.2.2.2.2.2.2.2.2.2.1
  have hClass : LocWPEquiv (X := A)
       (CoefficientIdealRestriction.withN (coeffMarkedAlong K) (K.N ∩ {x : W | u x.val = 0})) F :=
    hPair.2.2.2.2.1
  obtain ⟨hpO', hHeadF, _, hDomR', hNR', hER', _, _, _, _, hyR', hCanR'⟩ :=
    actual_zero_head_advances_supported_born hn K F hK hF
      (u ∘ (Subtype.val : W → X)) hTan hSelectedTrace hClass hEq V hCanJ w hw hReg'.1 hReg'.2
  have hEmpty : IsEmptyTower G := by
    let Data (p : Σ Z : CMfd.{0} n, BlowupTower B Z × BlowupTower Z (CMfd.of (n := n) (openPreimage U C))) := IsEmptyTower p.2.1
    change Data (split V r)
    rw [hClock', StepOneEmptyPrefix.split_of_length_le V V.length le_rfl]
    trivial
  let RF := barMarked (X := X) R
  have hRF := isInvDomain_barMarked (X := X) R hR
  have hGapF : HironakaG8GapNormalizedExponent.HasCosupportGap (X := A) F :=
    member_open_hasCosupportGap RF hRF (membersThrough RF.E (origMembers R H) (T.proj y)) W
  have hDomFc : IsInvDomain k Fc := isInvDomain_pullback_val C hF
  have hGapFc := cosupport_gap_pullback_val F hF.isWellFormed.isCoherent hGapF C
  have hGapHead := cosupport_gap_geoTransformAlong_empty Fc hDomFc hGapFc G hEmpty
  have hDomHead := isInvDomain_geoTransformAlong hDomFc G hHeadF
  have hGapR' : HironakaG8GapNormalizedExponent.HasCosupportGap R' :=
    cosupport_gap_pullback_val (geoTransformAlong Fc G) hDomHead.isWellFormed.isCoherent hGapHead O
  refine ⟨W, hpW, hWP, hWR, hPair, hpC, hCanJ, hw, hReg', hClock', hpO, hD, hCanD, ha',
    hDomR', hCanR' hGapR', hyR', hNR', hER', hCarrier.trans hTraceOnHead, hBoundary, ?_⟩
  exact hOuter.trans (congrArg (fun q : ValTy (k+1) => toLex (b+1, (q : WithTop (ValTy (k+1))))) hRead)

end
end Hironaka.HironakaG1LocalizedBornFullZeroRead
