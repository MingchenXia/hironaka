import Hironaka.Resolution.HironakaG1AdvancingRefreshedCoefficient
import Hironaka.Resolution.HironakaG1ChronologicalTrueMarkZero

/-! Exact zero-branch reading on the actual inherited companion suffix. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set TopologicalSpace

namespace Hironaka.HironakaG1ChronologicalRefreshedZeroRead

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealOperationsAlong.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres InvDomainTowerAlong
  HomogenizedIdealAlong StepOneValue StepOneValueMasked StepOneRegime TangentDirectionAlong
  CoefficientIdealRestriction ContactStageKept DivisorExponentAlong
  CompanionRebase NonmonomialOrderTail GeneralValue HironakaG8LocalHistory
  HironakaG1InitialPositiveGeneralRead HironakaG1ChronologicalTrueMarkZero
  HironakaG1AdvancingRefreshedCoefficient
open HomogenizedGlueingTower (strictAlong)

/-- The actual true-mark zero read and entire chronological slot list survive
through the same tested suffix; compatibility with current refreshed coefficients
is sufficient for the selected supported record to be canonical there. -/
theorem selected_suffix_true_mark_zero_of_refresh {n k m : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K R : MarkedIdeal n X)
    (hK : IsInvDomain (k+1) K) (hR : IsInvDomain k R) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {x | u x = 0} = R.N)
    (hClass : LocWPEquiv (withN (coeffMarkedAlong K) (K.N ∩ {x | u x = 0})) R)
    (hExp : ∀ F ∈ K.E, ∀ z, divExpAlong n K.N K.ideal F z = 0)
    (T : BlowupTower X Y) (hCan : IsCanonical K ((invFamily hn (k+1)).inv K) T)
    (y : Y) (hy : y ∈ (geoTransformAlong K T).cosupp) :
    let C := ordMask K K.d
    let A := CMfd.of (n := n) C
    let J := compAt K K.d (.refl : BlowupTower X X)
    let Kc := MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) K
    let Rc := MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) R
    let v : C → ℂ := u ∘ Subtype.val
    let V := restrict C T
    J.d = K.d ∧ J.E = K.E.map ((Subtype.val : C → X) ⁻¹' ·) ∧
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
        let B := CMfd.of (n := n) O
        let D := contactMarkedKept Kc v H O
        let R' := MarkedIdeal.pullback (M' := B) (Subtype.val : O → _) (geoTransformAlong Rc H)
        ∃ hq : p ∈ O,
          let w : openPreimage S O := ⟨z, hq⟩
          let G := restrict O S
          IsGeoTestTower Rc H ∧ IsInvDomain k D ∧ IsInvDomain k R' ∧
          D.N = R'.N ∧ D.E = R'.E ∧ R'.d = R.d ∧ LocWPEquiv D R' ∧
          D.N = (Subtype.val : O → _) ⁻¹' strictAlong H Rc.N ∧
          D.E = (J.E.map (strictAlong H) ++
            (geoTransformAlong (barMarked J) H).E.drop J.E.length).map
              ((Subtype.val : O → _) ⁻¹' ·) ∧
          IsCanonical D ((invFamily hn k).inv D) G ∧ IsGeoTestTower R' G ∧
          w ∈ (geoTransformAlong D G).cosupp ∧ w ∈ (geoTransformAlong R' G).cosupp ∧
          (∀ (M : MarkedIdeal n B), IsInvDomain m M → R'.N ⊆ M.N →
            RestrictEquiv R' (withN (coeffMarkedAlong M) R'.N) →
            IsCanonical R' ((invFamily hn k).inv R') G) ∧
          (invFamily hn (k+1)).inv K T y = positiveSuccessorRead K.d
            (toLex (0, ((invFamily hn k).inv D G w : WithTop (ValTy k))))) := by
  intro C A J Kc Rc v V
  obtain ⟨hd,hE,hp,hCanJ,hz,hZero⟩ :=
    selected_suffix_true_mark_zero_contact hn K R hK hR u hu hTrace hClass hExp T hCan y hy
  refine ⟨hd,hE,hp,hCanJ,hz,?_⟩
  intro hLevel hNS r H S p O B D R'
  obtain ⟨hq,hHead,hD,hR',hN,hDE,hRd,hClass',hCarrier,hBoundary,hCanD,hTest,hw,hwR,hFinish,hRead⟩ :=
    hZero hLevel hNS
  refine ⟨hq,hHead,hD,hR',hN,hDE,hRd,hClass',hCarrier,hBoundary,hCanD,hTest,hw,hwR,?_,hRead⟩
  intro M hM hSub hRefresh
  exact hFinish (refreshed_restricted_coefficient_gap M R' hM hSub hRefresh)

#print axioms selected_suffix_true_mark_zero_of_refresh

end Hironaka.HironakaG1ChronologicalRefreshedZeroRead
