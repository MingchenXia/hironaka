import Hironaka.Resolution.HironakaG1LocalizedBornWindowRestriction
import Hironaka.Resolution.HironakaG1LocalizedLaterBornRead
import Hironaka.Resolution.HironakaG1TrueMarkZeroContactRead

/-! The actual next-born window and its advancing zero contact. -/

set_option autoImplicit false

open Set TopologicalSpace

namespace Hironaka.HironakaG1LocalizedBornZeroContactRead

noncomputable section

open Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres HomogenizedIdealAlong ContactStageKept
  GeneralValue NonmonomialOrderTail TangentDirectionAlong StepOneValue StepOneRegime
  HironakaG8LocalHistory HironakaG1InitialPositiveGeneralRead HironakaG1RecursiveMemberValueTransport
  HironakaG1LocalizedLaterBornCanonical HironakaG1LocalizedLaterBornRead
  HironakaG1LocalizedBornNormalOrder HironakaG1LocalizedBornWindowRestriction
  HironakaG1TrueMarkZeroContactRead
open HomogenizedGlueingTower (strictAlong)

set_option maxHeartbeats 2100000 in
/-- A common actual next-born window supports both the prescribed-to-section
comparison and the true-mark read of the original positive branch. When the
actual companion ends in its finite zero branch, its prescribed contact lies
on the strict transform of the supported selected carrier and gives the
entire original upper letter there. -/
theorem exists_localized_born_zero_contact_read {n k l b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (P R : MarkedIdeal n X) (hP : IsInvDomain (k + 2) P) (hR : IsInvDomain l R)
    (hClass : LocWPEquiv P R) (hMax : IsMaximalOrderAlong P.N P.ideal P.d)
    (u : X → ℂ) (hu : IsTangentDirectionAlong P.N P.ideal P.d univ u)
    (hTrace : P.N ∩ {x | u x = 0} = R.N)
    (T : BlowupTower X Y)
    (hCan : IsCanonical P (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k + 1)) P) T)
    (y : Y) (hy : y ∈ (geoTransformAlong P T).cosupp) (ha : T.proj y ∈ R.N)
    (hLevel : level P T y = b + 1) (hNS : ¬ IsSpecial P T y)
    (hRun : regimeRun (stepRegime P (b + 1)) T y = T.length)
    (hWitness : LocalizedBornWitness (k := k + 2) (l := l) hn P R (T.proj y) u) :
    let H : BlowupTower X X := .refl
    ∃ (W : Opens X) (hpW : T.proj y ∈ W),
      W ≤ maskA P H (T.proj y) ∧ W ≤ maskA R H (T.proj y) ∧
      LocalizedBornWindowData (k := k + 2) (l := l) hn P R (T.proj y) u W ∧
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
        (level J V w = 0 → (¬ IsSpecial J V w) →
          let r := regimeRun (stepRegime J 0) V w
          let G := head V r
          let S := tail V r
          let p := S.proj w
          let O := maskB J G p
          let D := contactMarkedKept Kc v G O
          ∃ hpO : p ∈ O,
            let a : openPreimage S O := ⟨w, hpO⟩
            IsInvDomain k D ∧ IsCanonical D ((invFamily hn k).inv D) (restrict O S) ∧
            a ∈ (geoTransformAlong D (restrict O S)).cosupp ∧
            D.N = (Subtype.val : O → _) ⁻¹' strictAlong G Fc.N ∧
            D.E = (geoTransformAlong (barMarked J) G).E.map ((Subtype.val : O → _) ⁻¹' ·) ∧
            Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k + 1)) P T y =
              toLex (b + 1, (positiveSuccessorRead K.d
                (toLex (0, ((invFamily hn k).inv D (restrict O S) a : WithTop (ValTy k)))) :
                  WithTop (ValTy (k + 1))))) := by
  intro H
  obtain ⟨V₀, haV₀, hV₀P, hV₀R, hData⟩ := hWitness
  have hData₀ : LocalizedBornWindowData (k := k + 2) (l := l) hn P R (T.proj y) u V₀ := hData
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
  have hSelectedTrace : K.N ∩ {x : W | u x.val = 0} = F.N := hPair.2.2.1
  have hMaskTrace : Kc.N ∩ {x : C | u x.val.val = 0} = Fc.N := by
    change ((Subtype.val : C → W) ⁻¹' K.N) ∩ {x : C | u x.val.val = 0} =
      (Subtype.val : C → W) ⁻¹' F.N
    rw [← hSelectedTrace]
    rfl
  have hTraceOnHead {Z : CMfd.{0} n} (G : BlowupTower B Z) (O : Opens Z) :
      (Subtype.val : O → Z) ⁻¹' strictAlong G (Kc.N ∩ {x : C | u x.val.val = 0}) =
        (Subtype.val : O → Z) ⁻¹' strictAlong G Fc.N :=
    congrArg (fun F => (Subtype.val : O → Z) ⁻¹' strictAlong G F) hMaskTrace
  refine ⟨W, hpW, hWP, hWR, hPair, hpC, hCanJ, hw, fun hl hs => ?_⟩
  obtain ⟨hpO, hD, hCanD, ha', hCarrier, hBoundary, hRead⟩ := hZero hl hs
  exact ⟨hpO, hD, hCanD, ha', hCarrier.trans (hTraceOnHead _ _), hBoundary,
    hOuter.trans (congrArg (fun q : ValTy (k + 1) => toLex (b + 1, (q : WithTop (ValTy (k + 1))))) hRead)⟩

end

end Hironaka.HironakaG1LocalizedBornZeroContactRead
