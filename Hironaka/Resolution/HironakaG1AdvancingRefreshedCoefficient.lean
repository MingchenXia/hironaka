import Hironaka.Resolution.HironakaG1AdvancingSupportPowerGap

/-! An advancing-head gap can come from a genuine coefficient refresh on the current carrier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set TopologicalSpace

namespace Hironaka.HironakaG1AdvancingRefreshedCoefficient

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec InvDomainTowerAlong MarkedIdealOperationsAlong.MarkedIdeal
  HironakaG8GapNormalizedExponent HironakaG1AdvancingSupportPowerGap
  CanonicalCentres HomogenizedIdealAlong StepOneValue TangentDirectionAlong
  HironakaG1AdvancingSupportedBornContact HironakaG8LocalHistory CoefficientIdealRestriction
  HironakaActualCoefficientDivisorExponentGap GermIdealOrder MarkedIdealBiholomorphism DivisorExponentAlong

/-- A genuine refresh on a current ambient record supplies the zero-gap
criterion for any same-mark restricted representative on the selected carrier. -/
theorem refreshed_restricted_coefficient_gap {n k : ℕ} {A : CMfd.{0} n}
    (M P : MarkedIdeal n A) (hM : IsInvDomain k M) (hSub : P.N ⊆ M.N)
    (hRefresh : RestrictEquiv P (withN (coeffMarkedAlong M) P.N)) :
    HasCosupportGap P := by
  apply cosupport_gap_of_restrictEquiv hRefresh
  intro x _ hx
  change x ∈ cosupport n P.N (coeffMarkedAlong M).ideal (coeffMarkedAlong M).d
  rw [← coefficient_restriction_cosupport_gap M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d P.N hSub]
  exact hx

/-- At the actual advancing head, exact compatibility with a refreshed
coefficient on the current selected carrier supplies the supported gap
and the canonical zero-branch comparison, with all chronological slots kept. -/
theorem advancing_supported_canonical_of_refreshed_coefficient {n k l m : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K P : MarkedIdeal n X)
    (hK : IsInvDomain k K) (hP : IsInvDomain l P) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {z | u z = 0} = P.N)
    (hClass : LocWPEquiv (withN (coeffMarkedAlong K) (K.N ∩ {z | u z = 0})) P)
    (H : BlowupTower X Y) (hH : IsGeoTestTower (barMarked K) H) (O : Opens Y) :
    let A := CMfd.of (n := n) O
    let D := ContactStageKept.contactMarkedKept K u H O
    let P' := MarkedIdeal.pullback (M' := A) (Subtype.val : O → Y) (geoTransformAlong P H)
    ∀ (M : MarkedIdeal n A), IsInvDomain m M → P'.N ⊆ M.N →
      RestrictEquiv P' (withN (coeffMarkedAlong M) P'.N) →
      HasCosupportGap (X := A) P' ∧ D.N = P'.N ∧ D.E = P'.E ∧ P'.d = P.d ∧
      (∀ F ∈ D.E, ∀ z ∈ D.cosupp, z ∈ F →
        P'.d * divExpAlong n D.N D.ideal F z = D.d * divExpAlong n P'.N P'.ideal F z) ∧
      ∀ {Z : CMfd.{0} n} (T : BlowupTower A Z),
        IsCanonical D ((invFamily hn l).inv D) T ↔ IsCanonical P' ((invFamily hn l).inv P') T := by
  intro A D P' M hM hSub hRefresh
  have hGap := refreshed_restricted_coefficient_gap M P' hM hSub hRefresh
  obtain ⟨_,_,_,hN,hE,hd,_,_⟩ :=
    advancing_kept_contact_supported_stage K P hK hP u hu hTrace hClass H hH O
  exact ⟨hGap,hN,hE,hd,advancing_kept_contact_supported_canonical hn K P hK hP u hu hTrace
    hClass H hH O hGap⟩

open BlowupTowerSplit CompanionRebase NonmonomialOrderTail RestrictedIdealExtension
  StepOneValueMasked StepOneRegime ContactStageKept GeneralValue GeneralCompare
  MarkedIdealEquivalence.MarkedIdeal

set_option maxHeartbeats 2200000 in
/-- On the literal chronological zero suffix, refreshed coefficient compatibility
on the current open transports CAN to the advanced supported record. The selected
head, entire ordered boundary, suffix and surviving endpoint are kept. -/
theorem actual_zero_head_advances_supported_of_refresh {n k m : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (K R : MarkedIdeal n X)
    (hK : IsInvDomain (k + 1) K) (hR : IsInvDomain k R) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {z | u z = 0} = R.N)
    (hClass : LocWPEquiv (withN (coeffMarkedAlong K) (K.N ∩ {z | u z = 0})) R)
    (hEq : companionOf n K K.d =
      (⟨K.N, K.E, restrictOn n K.N K.ideal, K.d⟩ : MarkedIdeal n X)) :
    let C := ordMask (geoTransformAlong K (.refl : BlowupTower X X)) K.d
    let A := CMfd.of (n := n) C
    let J := compAt K K.d (.refl : BlowupTower X X)
    let Kc := MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) K
    let Rc := MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) R
    let v : C → ℂ := u ∘ Subtype.val
    ∀ {Y : CMfd.{0} n} (T : BlowupTower A Y),
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) T →
      ∀ y ∈ (geoTransformAlong J T).cosupp,
      level J T y = 0 → (¬ IsSpecial J T y) →
      let r := regimeRun (stepRegime J 0) T y
      let H := head T r
      let S := tail T r
      let p := S.proj y
      let O := maskB J H p
      let Y₀ := (split T r).1
      let B := CMfd.of (n := n) O
      let D := contactMarkedKept Kc v H O
      let R' := MarkedIdeal.pullback (M' := B) (Subtype.val : O → Y₀) (geoTransformAlong Rc H)
      ∃ hp : p ∈ O,
        IsGeoTestTower Rc H ∧ IsInvDomain k D ∧ IsInvDomain k R' ∧
        D.N = R'.N ∧ D.E = R'.E ∧ R'.d = R.d ∧ LocWPEquiv (X := B) D R' ∧
        IsCanonical D ((invFamily hn k).inv D) (restrict O S) ∧
        IsGeoTestTower R' (restrict O S) ∧
        (⟨y, hp⟩ : openPreimage S O) ∈ (geoTransformAlong R' (restrict O S)).cosupp ∧
        ∀ (M : MarkedIdeal n B), IsInvDomain m M → R'.N ⊆ M.N →
          RestrictEquiv R' (withN (coeffMarkedAlong M) R'.N) →
          IsCanonical R' ((invFamily hn k).inv R') (restrict O S) := by
  intro C A J Kc Rc v Y T hCan y hy hl hNS r H S p O Y₀ B D R'
  obtain ⟨hp,hHead,hD,hR',hN,hE,hd,hLoc,hCanD,hTestR,hyR,hFinish⟩ :=
    actual_zero_head_advances_supported_born hn K R hK hR u hu hTrace hClass hEq
      T hCan y hy hl hNS
  refine ⟨hp,hHead,hD,hR',hN,hE,hd,hLoc,hCanD,hTestR,hyR,?_⟩
  intro M hM hSub hRefresh
  exact hFinish (refreshed_restricted_coefficient_gap M R' hM hSub hRefresh)

#print axioms actual_zero_head_advances_supported_of_refresh
#print axioms refreshed_restricted_coefficient_gap
#print axioms advancing_supported_canonical_of_refreshed_coefficient

end Hironaka.HironakaG1AdvancingRefreshedCoefficient
