import Hironaka.Resolution.HironakaG1ActualLaterOrderRun
import Hironaka.Resolution.HironakaG1AdvancingOrderZeroContact
import Hironaka.Resolution.HironakaG1AdvancedBornFiniteRead

/-! The exact true-mark successor value on an actual advancing zero branch. -/

set_option autoImplicit false

open Set TopologicalSpace

namespace Hironaka.HironakaG1TrueMarkZeroContactRead

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  HomogenizedIdealAlong CoefficientIdealRestriction RestrictedIdealExtension ContactStageKept
  CompanionRebase GeneralValue NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime
  TangentDirectionAlong StepOneValue StepOneRegime
  HironakaG1ActualLaterOrderRun HironakaG1InitialPositiveGeneralRead HironakaG1LocalizedBornNormalHistory
  HironakaG1AdvancingOrderZeroContact HironakaG1AdvancedBornFiniteRead HironakaG1RecursiveMemberValueTransport
open HomogenizedGlueingTower (strictAlong)

set_option maxHeartbeats 1600000 in
/-- A canonical general history with a true-mark carrier-restricted companion
and a prescribed tangent produces its actual initial companion canonical
history. If the latter reads a finite zero letter, the entire original
successor value reads the prescribed contact on the actual zero suffix.
The phase clocks and the lower canonicality are derived internally. -/
theorem true_mark_original_advancing_zero_read {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K : MarkedIdeal n X) (hK : IsInvDomain (k + 1) K) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hBase : ∀ x ∈ K.cosupp, nmOrd K x = K.d)
    (hEq : companionOf n K K.d =
      (⟨K.N, K.E, restrictOn n K.N K.ideal, K.d⟩ : MarkedIdeal n X))
    (T : BlowupTower X Y) (hCan : IsCanonical K ((invFamily hn (k + 1)).inv K) T)
    (y : Y) (hy : y ∈ (geoTransformAlong K T).cosupp) :
    let C := ordMask K K.d
    let A := CMfd.of (n := n) C
    let J := compAt K K.d (.refl : BlowupTower X X)
    let Kc := MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) K
    let v : C → ℂ := u ∘ Subtype.val
    let V := restrict C T
    ∃ hp : T.proj y ∈ C,
      let z : openPreimage T C := ⟨y, hp⟩
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) V ∧
      z ∈ (geoTransformAlong J V).cosupp ∧
      (level J V z = 0 → (¬ IsSpecial J V z) →
        let r := regimeRun (stepRegime J 0) V z
        let H := head V r
        let S := tail V r
        let p := S.proj z
        let O := maskB J H p
        let D := contactMarkedKept Kc v H O
        ∃ hq : p ∈ O,
          let w : openPreimage S O := ⟨z, hq⟩
          IsInvDomain k D ∧ IsCanonical D ((invFamily hn k).inv D) (restrict O S) ∧
          w ∈ (geoTransformAlong D (restrict O S)).cosupp ∧
          D.N = (Subtype.val : O → _) ⁻¹' strictAlong H (Kc.N ∩ {x | v x = 0}) ∧
          D.E = (geoTransformAlong (barMarked J) H).E.map ((Subtype.val : O → _) ⁻¹' ·) ∧
          (invFamily hn (k + 1)).inv K T y = positiveSuccessorRead K.d
            (toLex (0, ((invFamily hn k).inv D (restrict O S) w : WithTop (ValTy k))))) := by
  intro C A J Kc v V
  have hTest := (invFamily hn (k + 1)).isInvValue.isGeoTestTower_of_isCanonical hK T hCan
  have hOrders {Z : CMfd.{0} n} (U : BlowupTower X Z) (hU : IsGeoTestTower K U) :
      ∀ z ∈ (geoTransformAlong K U).cosupp, nmOrd (geoTransformAlong K U) z = K.d :=
    (same_mark_test_order_and_strict_contact hn K hK u hu hBase hEq U hU).1
  have hRun := order_run_of_all_test_orders K hK K.d (fun U => hOrders U) T hTest y hy
  obtain ⟨_, hp, _, _, hCanJ, hz, hRead⟩ :=
    original_positive_initial_order_companion hn K hK T hCan y hy K.d
      (hOrders T hTest y hy) hK.one_le_d hRun
  refine ⟨hp, hCanJ, hz, fun hLevel hNS => ?_⟩
  obtain ⟨hq, hD, hCanD, hw, _, hCarrier, _, hBoundary, _, hValue⟩ :=
    order_companion_actual_zero_head_contact hn K hK u hu hEq V hCanJ ⟨y, hp⟩ hz hLevel hNS
  exact ⟨hq, hD, hCanD, hw, hCarrier, hBoundary,
    hRead.trans (congrArg (positiveSuccessorRead K.d) hValue)⟩

set_option maxHeartbeats 2000000 in
/-- An original positive Step One letter reads the exact successor value
of the prescribed zero contact whenever its selected subwindow has the
true-mark normal geometry and the actual companion ends in the finite
zero branch. Both canonicalities and both actual splits are recovered. -/
theorem original_positive_advancing_zero_read_on {n k b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (P : MarkedIdeal n X) (hP : IsInvDomain (k + 2) P)
    (hMax : IsMaximalOrderAlong P.N P.ideal P.d) (T : BlowupTower X Y)
    (hCan : IsCanonical P (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k + 1)) P) T)
    (y : Y) (hy : y ∈ (geoTransformAlong P T).cosupp)
    (hLevel : level P T y = b + 1) (hNS : ¬ IsSpecial P T y) :
    let r := regimeRun (stepRegime P (b + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    ∀ (W : Opens (split T r).1), W ≤ maskA P H p → ∀ hpW : p ∈ W,
      let A := CMfd.of (n := n) W
      let K := positiveMemberOn P H p W
      let U := restrict W S
      let z : openPreimage S W := ⟨y, hpW⟩
      let C := ordMask K K.d
      let J := compAt K K.d (.refl : BlowupTower A A)
      let V := restrict C U
      ∀ v : A → ℂ, IsTangentDirectionAlong K.N K.ideal K.d univ v →
        (∀ x ∈ K.cosupp, nmOrd K x = K.d) →
        companionOf n K K.d = (⟨K.N, K.E, restrictOn n K.N K.ideal, K.d⟩ : MarkedIdeal n A) →
        ∃ hpC : U.proj z ∈ C,
          let w : openPreimage U C := ⟨z, hpC⟩
          let Kc := MarkedIdeal.pullback (M' := CMfd.of (n := n) C) (Subtype.val : C → A) K
          IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) V ∧
          w ∈ (geoTransformAlong J V).cosupp ∧
          (level J V w = 0 → (¬ IsSpecial J V w) →
            let r' := regimeRun (stepRegime J 0) V w
            let H' := head V r'
            let S' := tail V r'
            let q := S'.proj w
            let O := maskB J H' q
            let D := contactMarkedKept Kc (v ∘ Subtype.val) H' O
            ∃ hpO : q ∈ O,
              let a : openPreimage S' O := ⟨w, hpO⟩
              IsInvDomain k D ∧ IsCanonical D ((invFamily hn k).inv D) (restrict O S') ∧
              a ∈ (geoTransformAlong D (restrict O S')).cosupp ∧
              D.E = (geoTransformAlong (barMarked J) H').E.map ((Subtype.val : O → _) ⁻¹' ·) ∧
              Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k + 1)) P T y =
                toLex (b + 1, (positiveSuccessorRead K.d
                  (toLex (0, ((invFamily hn k).inv D (restrict O S') a : WithTop (ValTy k)))) :
                    WithTop (ValTy (k + 1))))) := by
  intro r H S p W hW hpW A K U z C J V v hv hBase hEq
  obtain ⟨_, _, _, hSelected⟩ :=
    advanced_positive_stepOne_finite_read hn P hP hMax T hCan y hy hLevel hNS
  obtain ⟨hK, hCanK, hz, _, _, hUpper⟩ := hSelected W hW hpW
  obtain ⟨hpC, hCanJ, hw, hZero⟩ :=
    true_mark_original_advancing_zero_read hn K hK v hv hBase hEq U hCanK z hz
  refine ⟨hpC, hCanJ, hw, fun hL hS => ?_⟩
  obtain ⟨hpO, hD, hCanD, ha, _, hBoundary, hRead⟩ := hZero hL hS
  exact ⟨hpO, hD, hCanD, ha, hBoundary,
    hUpper.trans (congrArg (fun a : ValTy (k + 1) => toLex (b + 1, (a : WithTop (ValTy (k + 1))))) hRead)⟩

end

end Hironaka.HironakaG1TrueMarkZeroContactRead
