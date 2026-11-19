import Hironaka.Resolution.HironakaG1BornSpecialCarrierCriterion
import Hironaka.Resolution.HironakaG1ChronologicalCompanionSuffix
import Hironaka.Resolution.HironakaG1NativeBoundaryCodimension
import Hironaka.Resolution.HironakaG1AdvancingSupportPowerGap

/-! The exact local dimension criterion for regular supported positive anchors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG1ChronologicalSupportDimensionSplit

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres HomogenizedIdealAlong
  StepOneValue StepOneValueMasked StepOneRegime BoundaryCount InvDomainMemberRestriction
  InvDomainTowerAlong HironakaG8LocalHistory HironakaG8HomStable HironakaG8MemberLoci
  HironakaCoherentTransformExtension AnalyticDimensionBasics CodimOneSupportAlong
  HironakaG1BornSpecialCarrierCriterion HironakaG1NativeBoundaryCodimension
  HironakaG1ChronologicalCompanionSuffix
open HomogenizedGlueingTower (N_geoTransformAlong)

/-- On a smooth carrier, the analytic trace of a closed cut has full
local dimension exactly when the trace fills a neighborhood in the carrier. -/
theorem analytic_trace_fills_iff_local_full_dimension {n d : ℕ} {X : CMfd.{0} n}
    {A Z : Set X} {p : X}
    (hA : IsComplexAnalyticSubset (n := n) A)
    (hZ : IsComplexAnalyticSubset (n := n) Z)
    (hReg : RegularAtDim (n := n) A p d) :
    p ∉ closure (A \ Z) ↔ LocDimGE (n := n) (A ∩ Z) p d := by
  classical
  have hNear : p ∉ closure (A \ Z) ↔ ∀ᶠ x in 𝓝 p, x ∈ A → x ∈ Z := by
    rw [mem_closure_iff_frequently, Filter.Frequently, not_not]
    exact eventually_congr (Eventually.of_forall fun x => by simp)
  rw [hNear]
  constructor
  · intro hh
    exact locDimGE_of_regularAtDim_eventually_subset (hA.inter hZ) hReg
      (hh.mono fun x hx hxA => ⟨hxA,hx hxA⟩)
  · intro hh
    have he := CodimOneSupport.eventually_mem_iff_of_regularAtDim_of_locDimGE
      (hA.inter hZ) hReg (Eventually.of_forall fun _ hx => hx.1) hh
    exact he.mono fun x hx hxA => (hx.mpr hxA).2

set_option maxHeartbeats 1000000 in
/-- At the genuine positive anchor, support specialness is exactly the
full dimension of the analytic cut on the selected supported carrier.
The chronological member intersection uses the actual retained old list. -/
theorem supported_positive_anchor_dimension_split {n k l : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J R : MarkedIdeal n X)
    (hJ : IsInvDomain k J) (hR : IsInvDomain l R)
    (hClass : LocWPEquiv J R) (hCar : R.N ⊆ J.N)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T) (p : Y)
    (hPos : 0 < level J T p)
    (hp : p ∈ (geoTransformAlong (barMarked J) T).cosupp) :
    let A := geoTransformAlong (barMarked J) T
    let B := geoTransformAlong (barMarked R) T
    let Q := memberRestrict B (membersThrough B.E (origMembers R T) p)
    ∃ d, RegularAtDim (n := n) Q.N p d ∧
      (IsSpecial R T p ↔ LocDimGE (n := n) (Q.N ∩ A.cosupp) p d) ∧
      (¬ IsSpecial R T p ↔ ¬ LocDimGE (n := n) (Q.N ∩ A.cosupp) p d) := by
  intro A B Q
  have hTB := (hClass.wEquiv.2 T).1.mp hT
  have hTA' := ((bar_local_any_boundary J hJ).wEquiv.2 T).1.mp hT
  have hTB' := ((bar_local_any_boundary R hR).wEquiv.2 T).1.mp hTB
  have hA := isInvDomain_geoTransformAlong (isInvDomain_barMarked J hJ) T hTA'
  have hB := isInvDomain_geoTransformAlong (isInvDomain_barMarked R hR) T hTB'
  have hQ : Q.IsWellFormed := isWellFormed_memberRestrict
    hn
    hB.isWellFormed _
  obtain ⟨_, _, _, hCos, _, _, hRiff, _, _⟩ :=
    positive_special_carrier_criterion J R hJ hR hClass hCar T hT p hPos
  have hpB : p ∈ B.N := B.cosupp_subset_N (hCos ▸ hp)
  have hpQ : p ∈ Q.N := by
    exact ⟨hpB, fun _ hi => (mem_membersThrough.mp hi).2⟩
  obtain ⟨d,hd⟩ := hQ.isClosedSubmanifold_N.2 p hpQ
  have hAnalyticQ := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
    hQ.isClosedSubmanifold_N
  have hAnalyticA := isComplexAnalyticSubset_cosupport_along hA.isWellFormed.isCoherent
    hA.isWellFormed.isClosedSubmanifold_N hA.one_le_d
  have hEq : IsSpecial R T p ↔ LocDimGE (n := n) (Q.N ∩ A.cosupp) p d :=
    (hRiff.trans (and_iff_right hp)).trans
    (analytic_trace_fills_iff_local_full_dimension hAnalyticQ hAnalyticA hd)
  exact ⟨d,hd,hEq,not_congr hEq⟩

open HironakaG1AdvancingSupportPowerGap HironakaG1RecursiveMemberValueTransport

set_option maxHeartbeats 1300000 in
/-- The strict dimension drop on the actual chronological supported cut
is exactly the regular branch with a common positive domain submask.
Full dimension gives the supported special branch at the same anchor.
The prefix is the actual head selected by the original Step One clock. -/
theorem chronological_support_dimension_domain_split {n k b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J R : MarkedIdeal n X) (hJ : IsInvDomain (k+2) J)
    (hR : IsInvDomain (k+1) R) (hClass : LocWPEquiv J R) (hCar : R.N ⊆ J.N)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J) T)
    (y : Y) (hy : y ∈ (geoTransformAlong J T).cosupp)
    (hLevel : level J T y = b+1) (hNS : ¬ IsSpecial J T y) :
    let r := regimeRun (stepRegime J (b+1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let A := geoTransformAlong (barMarked J) H
    let B := geoTransformAlong (barMarked R) H
    let Q := memberRestrict B (membersThrough B.E (origMembers R H) p)
    ∃ d, RegularAtDim (n := n) Q.N p d ∧
      (IsSpecial R H p ↔ LocDimGE (n := n) (Q.N ∩ A.cosupp) p d) ∧
      (¬ LocDimGE (n := n) (Q.N ∩ A.cosupp) p d ↔
        ∃ O : Opens (split T r).1, p ∈ O ∧ O ≤ maskA J H p ∧ O ≤ maskA R H p ∧
          ∀ V : Opens (split T r).1, V ≤ O →
            IsInvDomain (k+1) (positiveMemberOn J H p V) ∧
            IsInvDomain k (positiveMemberOn R H p V)) := by
  intro r H S p A B Q
  obtain ⟨hH, hp, _, _, _, _, _, _, _, _, _, _⟩ :=
    positive_companion_chronological_suffix (k := k+1) hn J hJ hMax T hCan y hy hLevel hNS
  have hJH := ((bar_local_any_boundary J hJ).wEquiv.2 H).1.mpr hH
  let I := invFamily hn (k+1)
  obtain ⟨hT, _, hCos⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical I J hJ hMax hn T hCan
  have hyBar : y ∈ (geoTransformAlong (barMarked J) T).cosupp := hCos.symm ▸ hy
  have hReg := StepOneValueMasked.stepRegime_and_mem_cosupp_head J hJ.isWellFormed T hT hyBar hNS
  rw [hLevel] at hReg
  have hlJ : level J H p = b+1 := hReg.1.1
  have hlR : level R H p = b+1 := (level_eq_of_E_eq hClass.wEquiv.1 H p).symm.trans hlJ
  obtain ⟨d, hd, hFull, hDrop⟩ := supported_positive_anchor_dimension_split hn J R hJ hR
    hClass hCar H hJH p (hlJ.symm ▸ Nat.succ_pos b) hp
  refine ⟨d, hd, hFull, ?_⟩
  constructor
  · intro h
    exact chronological_supported_domain_of_nonspecial_anchor hn J R hJ hR hClass
      hMax T hCan y hy hLevel hNS (hDrop.mpr h)
  · rintro ⟨O,hpO,_,hOR,_⟩
    have h := interior_subset (hOR hpO)
    exact hDrop.mp (fun hSp => h.2 ⟨rfl,hSp⟩)

#print axioms analytic_trace_fills_iff_local_full_dimension
#print axioms supported_positive_anchor_dimension_split
#print axioms chronological_support_dimension_domain_split

end Hironaka.HironakaG1ChronologicalSupportDimensionSplit
