import Hironaka.Resolution.HironakaG1SupportedGapEmptyEpoch
import Hironaka.Resolution.HironakaActualOriginalPowerTransform
import Hironaka.Resolution.HironakaG8ActualContactBirthRebase
import Hironaka.Resolution.HironakaG1CompanionZeroBranchRecognition
import Hironaka.Resolution.HironakaG1ChronologicalCompanionSuffix

/-! A geometric test preserves the supported gap for whole powers of mark-one records. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1AdvancingSupportPowerGap

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec InvDomainTowerAlong MarkedIdealEquivalence.MarkedIdeal
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealBiholomorphism GermIdealOrder IdealWeightPowers
  HironakaActualOriginalPowerTransform HironakaActualPowerBoundaryExponents
  HironakaG8ActualContactBirthRebase HironakaG8GapNormalizedExponent HironakaG1SupportedGapEmptyEpoch

/-- A same-mark restricted equivalence preserves both the ordinary
positive-order cut and the marked cut, hence preserves their gap. -/
theorem cosupport_gap_of_restrictEquiv {n : ℕ} {X : CMfd.{0} n}
    {P Q : MarkedIdeal n X} (h : RestrictEquiv P Q) (hGap : HasCosupportGap Q) :
    HasCosupportGap P := by
  intro x hx hOne
  have hOneEq : RestrictEquiv ({P with d := 1}) ({Q with d := 1}) :=
    ⟨h.N_eq,h.E_eq,rfl,h.le,h.ge⟩
  have hh : cosupport n P.N P.ideal 1 = cosupport n Q.N Q.ideal 1 := hOneEq.cosupp_eq
  exact h.cosupp_eq.symm ▸ hGap x (h.N_eq ▸ hx) (hh ▸ hOne)

/-- All positive powers of a coherent mark-one record have the gap
on its actual carrier. The ordinary order-one cut is computed sharply. -/
theorem power_mark_one_has_gap {n k : ℕ} {X : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : IsInvDomain k P) (hd : P.d = 1)
    (e : ℕ) (he : 1 ≤ e) : HasCosupportGap (powerMarked P e) := by
  intro x _ hx
  have hSharp := cosupport_idealPow_mul_succ_eq_along hP.isWellFormed.isClosedSubmanifold_N
    hP.isWellFormed.isCoherent he 0
  simp only [Nat.mul_zero, Nat.zero_add] at hSharp
  have hOrd : x ∈ P.cosupp := by
    change x ∈ cosupport n P.N (idealPow P.ideal e) 1 at hx
    rw [hSharp] at hx
    change x ∈ cosupport n P.N P.ideal P.d
    rwa [hd]
  exact (powerMarked_cosupp P hP he).symm ▸ hOrd

/-- A supported record presented on its carrier as a whole positive
power of a mark-one record keeps the gap through every actual controlled
head. Exceptional slots are formed by the genuine test. -/
theorem cosupport_gap_geoTransformAlong_of_mark_one_power {n k l : ℕ}
    {X Y : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q) (hd : P.d = 1)
    (e : ℕ) (he : 1 ≤ e) (hPower : RestrictEquiv Q (powerMarked P e))
    (T : BlowupTower X Y) (hT : IsGeoTestTower Q T) :
    HasCosupportGap (geoTransformAlong Q T) := by
  have hPow := powerMarked_isInvDomain P hP he
  have hTestPow := (((MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hPower) hQ.isWellFormed.isClosedSubmanifold_N.1
    hQ.isWellFormed.isCoherent hPow.isWellFormed.isCoherent).2 T).1.mp hT
  have hPT := (original_power_test_iff P hP he T).mp hTestPow
  have hActual := restrictEquiv_geoTransformAlong_of_test hQ.isWellFormed
    hPow.isWellFormed.isCoherent hPower T hT
  have hStage := (original_power_transform P hP e he T hPT).2
  have hMark : (geoTransformAlong P T).d = 1 := (d_geoTransformAlong P T).trans hd
  apply cosupport_gap_of_restrictEquiv hActual
  apply cosupport_gap_of_restrictEquiv hStage
  exact power_mark_one_has_gap (geoTransformAlong P T)
    (isInvDomain_geoTransformAlong hP T hPT) hMark e he

open CanonicalCentres HomogenizedIdealAlong StepOneValue TangentDirectionAlong
  HironakaG1AdvancingSupportedBornContact HironakaG8LocalHistory CoefficientIdealRestriction

/-- The supported canonicality comparison applies on an actual advancing
head with arbitrarily many genuine centers when the supported source
has a whole mark-one power presentation on the carrier. -/
theorem advancing_supported_canonical_of_mark_one_power {n k l m : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K P Q : MarkedIdeal n X)
    (hK : IsInvDomain k K) (hP : IsInvDomain l P)
    (hQ : IsInvDomain m Q) (hQd : Q.d = 1) (e : ℕ) (he : 1 ≤ e)
    (hPower : RestrictEquiv P (powerMarked Q e)) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {z | u z = 0} = P.N)
    (hClass : LocWPEquiv (withN (coeffMarkedAlong K) (K.N ∩ {z | u z = 0})) P)
    (H : BlowupTower X Y) (hH : IsGeoTestTower (barMarked K) H) (O : Opens Y) :
    let A := CMfd.of (n := n) O
    let D := ContactStageKept.contactMarkedKept K u H O
    let P' := MarkedIdeal.pullback (M' := A) (Subtype.val : O → Y) (geoTransformAlong P H)
    HasCosupportGap (X := A) P' ∧
    ∀ {Z : CMfd.{0} n} (T : BlowupTower A Z),
      IsCanonical D ((invFamily hn l).inv D) T ↔ IsCanonical P' ((invFamily hn l).inv P') T := by
  intro A D P'
  have hPH := (advancing_kept_contact_supported_stage K P hK hP u hu hTrace hClass H hH O).1
  have hGap := cosupport_gap_geoTransformAlong_of_mark_one_power Q P hQ hP hQd e he hPower H hPH
  have hGapO : HasCosupportGap (X := A) P' := cosupport_gap_pullback_val _
    (isInvDomain_geoTransformAlong hP H hPH).isWellFormed.isCoherent hGap O
  exact ⟨hGapO, (advancing_kept_contact_supported_canonical hn K P hK hP u hu hTrace
    hClass H hH O hGapO).2⟩

open BlowupTowerSplit StepOneValueMasked StepOneRegime StepOneLowerDomain
  HironakaG1RecursiveMemberValueTransport HironakaG1LaterPositiveMaskContact
  HironakaG1ChronologicalCompanionSuffix HironakaG8HomStable HironakaG8MemberLoci

set_option maxHeartbeats 1200000 in
/-- Regularity of the supported record at the actual positive anchor gives
a common submask where its selected record has the dropped dimension
bound. This does not require a domain on the whole upper mask. -/
theorem chronological_supported_domain_of_nonspecial_anchor {n k b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J R : MarkedIdeal n X) (hJ : IsInvDomain (k+2) J)
    (hR : IsInvDomain (k+1) R) (hLocal : LocWPEquiv J R)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J) T)
    (y : Y) (hy : y ∈ (geoTransformAlong J T).cosupp)
    (hLevel : level J T y = b+1) (hNS : ¬ IsSpecial J T y) :
    let r := regimeRun (stepRegime J (b+1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA J H p
    ¬ IsSpecial R H p →
    ∃ W : Opens (split T r).1, p ∈ W ∧ W ≤ O ∧ W ≤ maskA R H p ∧
      ∀ V : Opens (split T r).1, V ≤ W →
        IsInvDomain (k+1) (positiveMemberOn J H p V) ∧ IsInvDomain k (positiveMemberOn R H p V) := by
  intro r H S p O hNSR
  let I := invFamily hn (k+1)
  obtain ⟨hT, _, hCos⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical I J hJ hMax hn T hCan
  have hyBar : y ∈ (geoTransformAlong (barMarked J) T).cosupp := hCos.symm ▸ hy
  have hReg := StepOneValueMasked.stepRegime_and_mem_cosupp_head J hJ.isWellFormed T hT hyBar hNS
  rw [hLevel] at hReg
  have hlJ : level J H p = b+1 := hReg.1.1
  have hlR : level R H p = b+1 :=
    (level_eq_of_E_eq hLocal.wEquiv.1 H p).symm.trans hlJ
  obtain ⟨hHead, _, _, _, _, _, hpO, _, _, _, _, _⟩ :=
    positive_companion_chronological_suffix (k := k+1) hn J hJ hMax T hCan y hy hLevel hNS
  have hJH := ((bar_local_any_boundary J hJ).wEquiv.2 H).1.mpr hHead
  have hRH := (hLocal.wEquiv.2 H).1.mp hJH
  have hRB := ((bar_local_any_boundary R hR).wEquiv.2 H).1.mp hRH
  have hpR := mem_maskA R hR.isWellFormed hR.one_le_d hn H hRB
    (show 0 < level R H p by rw [hlR]; omega) hNSR
  let W := O ⊓ maskA R H p
  refine ⟨W, ⟨hpO,hpR⟩, inf_le_left, inf_le_right, fun V hV => ?_⟩
  exact ⟨positive_member_domain_on_subwindow hn J hJ H hHead p hlJ V
      (hV.trans inf_le_left),
    positive_member_domain_on_subwindow hn R hR H hRB p hlR V
      (hV.trans inf_le_right)⟩

open BoundaryCount MemberInterTowerAlong HironakaG1CompanionZeroBranchRecognition
open HomogenizedGlueingTower (strictAlong)

/-- The finite zero branch of an actual companion is exactly absence of
incidence with the strict transforms of every retained source slot.
Its source slots can include divisors born before the companion formed.
The supported trace supplies nonspeciality on the tested endpoint. -/
theorem finite_zero_iff_off_retained_strict_boundary {n k l : ℕ}
    {X Y : CMfd.{0} n} (J R : MarkedIdeal n X) (hJ : IsInvDomain k J)
    (hR : IsInvDomain l R) (hClass : LocWPEquiv J R) (u : X → ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (hTrace : J.N ∩ {x | u x = 0} = R.N)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T) (y : Y) :
    stepRegime J 0 T y ↔ ∀ F ∈ J.E, y ∉ strictAlong T F := by
  classical
  rw [step_regime_zero_iff_level_of_strict_supported_trace J R hJ hR hClass u hu hTrace T hT y]
  have hOrig : origMembers J T = J.E.map (strictAlong T) :=
    take_E_geoTransformAlong (barMarked J) T
  unfold level
  rw [hOrig, boundaryCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h F hF
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_map.mpr ⟨F,hF,rfl⟩ :
      strictAlong T F ∈ J.E.map (strictAlong T))
    rw [← hi]
    exact h (Finset.mem_univ i)
  · intro h i _
    obtain ⟨F,hF,hEq⟩ := List.mem_map.mp (List.get_mem (J.E.map (strictAlong T)) i)
    rw [← hEq]
    exact h F hF

#print axioms cosupport_gap_geoTransformAlong_of_mark_one_power
#print axioms advancing_supported_canonical_of_mark_one_power
#print axioms chronological_supported_domain_of_nonspecial_anchor
#print axioms finite_zero_iff_off_retained_strict_boundary

end Hironaka.HironakaG1AdvancingSupportPowerGap
