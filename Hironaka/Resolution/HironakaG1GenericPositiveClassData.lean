import Hironaka.Resolution.HironakaG1MemberCoefficientGap
import Hironaka.Resolution.HironakaG1MemberStageLocal
import Hironaka.Resolution.HironakaG8GapNormalizedExponent
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaG1GenericPositiveClassData
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal MarkedIdealBiholomorphism
  BlowupTowers BlowupTowerTransforms ResolutionInvariantSpec StepOneValue StepOneValueMasked
  StepOneBridge HironakaG1OriginalStepSkeleton HironakaG1GenericPositiveMask HironakaG8PowerLowerGeometry
  HironakaG1MemberCoefficientGap HironakaG1MemberStageLocal HironakaG8LocalHistory HironakaG8GapNormalizedExponent
  DivisorExponentAlong InvDomainMemberRestriction HironakaCoherentTransformExtension InvDomainTowerAlong

/-- A pair of locally equivalent native records with the same carrier has
fully locally equivalent positive member records with normalized boundary
exponents, for arbitrary initial boundary and unequal marks. -/
theorem positive_member_class_data {n kA kB : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N = B.N) (hL : LocWPEquiv A B) (T : BlowupTower X Y) (hT : IsGeoTestTower A T)
    (y : Y) (s : ℕ) (hlevel : level A T y = s+1) :
    let O := maskA A T y
    let P := geoTransformAlong (barMarked A) T
    let Q := geoTransformAlong (barMarked B) T
    let A' := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y)
      (memberRestrict P (membersThrough P.E (origMembers A T) y))
    let B' := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y)
      (memberRestrict Q (membersThrough Q.E (origMembers B T) y))
    IsInvDomain (kA-1) A' ∧ IsInvDomain (kB-1) B' ∧ A'.N = B'.N ∧ A'.E = B'.E ∧
      LocWPEquiv A' B' ∧
      (∀ H ∈ A'.E, ∀ x ∈ A'.cosupp, x ∈ H →
        B'.d * divExpAlong n A'.N A'.ideal H x = A'.d * divExpAlong n B'.N B'.ideal H x) := by
  let O := maskA A T y
  let P := geoTransformAlong (barMarked A) T
  let Q := geoTransformAlong (barMarked B) T
  let A' := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y)
    (memberRestrict P (membersThrough P.E (origMembers A T) y))
  let B' := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y)
    (memberRestrict Q (membersThrough Q.E (origMembers B T) y))
  change IsInvDomain (kA-1) A' ∧ IsInvDomain (kB-1) B' ∧ A'.N = B'.N ∧ A'.E = B'.E ∧
    LocWPEquiv A' B' ∧ (∀ H ∈ A'.E, ∀ x ∈ A'.cosupp, x ∈ H →
      B'.d * divExpAlong n A'.N A'.ideal H x = A'.d * divExpAlong n B'.N B'.ideal H x)
  have hTB := (hL.wEquiv.2 T).1.mp hT
  have hTP := ((StepOneBridge.barMarked_wEquiv A hA).2 T).1.mpr hT
  have hTQ := ((StepOneBridge.barMarked_wEquiv B hB).2 T).1.mpr hTB
  have hP := isInvDomain_geoTransformAlong (isInvDomain_barMarked A hA) T hTP
  have hQ := isInvDomain_geoTransformAlong (isInvDomain_barMarked B hB) T hTQ
  have hskel := original_step_skeleton_of_wEquiv hn A B hA hB hN hL.wEquiv T hT y
  have hlevelB : level B T y = s+1 := hskel.1.symm.trans hlevel
  have hMask : maskA A T y = maskA B T y := lowerMask_succ_of_wEquiv hn A B hA hB hN hL.wEquiv T hT y s
  have hA' : IsInvDomain (kA-1) A' :=
    StepOneLowerDomain.isInvDomain_lowerMarked_succ A hA.isWellFormed hA.one_le_d hn T hTP hA.dimLE hlevel
  have hB' : IsInvDomain (kB-1) B' := by
    have hB₀ := StepOneLowerDomain.isInvDomain_lowerMarked_succ B hB.isWellFormed hB.one_le_d hn T hTQ hB.dimLE hlevelB
    have hTransport : ∀ (V : Opens Y), V = maskA B T y →
        IsInvDomain (kB-1) (MarkedIdeal.pullback (M' := CMfd.of (n := n) V) (Subtype.val : V → Y)
          (memberRestrict Q (membersThrough Q.E (origMembers B T) y))) := by
      intro V hV
      subst V
      exact hB₀
    exact hTransport O hMask
  have hE : A.E = B.E := hL.wEquiv.1
  obtain ⟨hNA,hEA⟩ := positive_member_geometry_on_open hN hE T y O
  have hLocal := member_stage_local_of_local hn A B hA hB hN hL T hT O y
  refine ⟨hA',hB',hNA,hEA,hLocal,?_⟩
  intro H hH x hx hxH
  obtain ⟨i,hi⟩ := List.get_of_mem hH
  have hHB : H ∈ B'.E := hEA ▸ hH
  obtain ⟨j,hj⟩ := List.get_of_mem hHB
  have hGapA := member_open_divisor_gap P hP (membersThrough P.E (origMembers A T) y) O H x
  have hGapB := member_open_divisor_gap Q hQ (membersThrough Q.E (origMembers B T) y) O H x
  have hEq : A'.E.get i = B'.E.get j := hi.trans hj.symm
  have hxI : x ∈ A'.E.get i := hi.symm ▸ hxH
  have hga : divExpAlong n A'.N A'.ideal (A'.E.get i) x = 0 ∨
      A'.d ≤ divExpAlong n A'.N A'.ideal (A'.E.get i) x := by simpa only [hi] using hGapA
  have hgb : divExpAlong n B'.N B'.ideal (B'.E.get j) x = 0 ∨
      B'.d ≤ divExpAlong n B'.N B'.ideal (B'.E.get j) x := by simpa only [hj] using hGapB
  have hexp := normalized_exponent_of_numeric_gap hn A' B' hA' hB' hNA hLocal i j hEq
    (A'.cosupp_subset_N hx) hxI hga hgb
  simpa only [hi,hj] using hexp
end
end Hironaka.HironakaG1GenericPositiveClassData
