import Hironaka.Resolution.HironakaG1MemberStageWeak
import Hironaka.Resolution.HironakaG1GenericPositiveMask
import Hironaka.Resolution.HironakaG8PowerLowerGeometry
import Hironaka.Resolution.HironakaG1OriginalStepSkeleton
import Hironaka.Resolution.HironakaG8MemberLoci
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1OriginalMemberStage
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal
  BlowupTowers BlowupTowerTransforms ResolutionInvariantSpec StepOneValue
  HironakaG1OriginalStepSkeleton HironakaG8MemberLoci HironakaG1CoeffCompanionLocal
  HironakaActualOriginalTrueMarkMaskCompanions HironakaEmbeddedAnalytic
  HironakaG1CoeffBarLocal HironakaG1GenericPositiveMask HironakaG8PowerLowerGeometry
  InvDomainMemberRestriction HironakaG8LocalHistory HironakaG1MemberStageWeak HironakaActualProjectionTestRecord
  StepOneValueMasked NonmonomialOrderLocal NonmonomialOrderTail HomogenizedIdealAlong
  CoefficientIdeal IdealWeightPowers CompanionRebase MarkedIdealRestrictOpen MarkedIdealBiholomorphism

/-- The original positive-level member records have common geometry and
controlled/projected test equivalence on the actual common mask. -/
theorem original_positive_member_tests {n k : ℕ} (hn : 0 < n) {A : CMfd.{0} n}
    (Q : MarkedIdeal n A) (hQ : IsInvDomain k Q) (hN : Q.N = univ) (hE : Q.E = [])
    (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d) (W : Set A)
    (hW : IsComplexAnalyticSubset (n := n) W) (hSing : Q.cosupp ⊆ singularSet (n := n) W)
    (a : A) (ha : a ∈ Q.cosupp) :
    ∃ hm : a ∈ maskB Q (.refl : BlowupTower A A) a,
      let V := maskB Q (.refl : BlowupTower A A) a
      let L : MarkedIdeal n (CMfd.of (n := n) V) := lowerMarkedB Q (.refl : BlowupTower A A) a
      let x : V := ⟨a,hm⟩
      let μ := nmOrd L x
      let e := sumExp (fun j => L.d-j) L.d 0
      let U := ordMask L μ
      let P : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → V) L
      let B : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → V) (coeffMarkedAlong L)
      let J := companionOf n P μ
      let K := companionOf n B (e*μ)
      x ∈ U ∧ ∀ {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) U) Y),
        IsGeoTestTower J T → ∀ (y : Y) (s : ℕ),
          let O := maskA J T y
          let D := geoTransformAlong (barMarked J) T
          let F := geoTransformAlong (barMarked K) T
          let D' := memberRestrict D (membersThrough D.E (origMembers J T) y)
          let F' := memberRestrict F (membersThrough F.E (origMembers K T) y)
          lowerMask J (s+1) T y = lowerMask K (s+1) T y ∧
          LocWPEquiv (MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) D)
            (MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) F) ∧
          (MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) D').N =
            (MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) F').N ∧
          (MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) D').E =
            (MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) F').E ∧
          (y ∈ O →
          let DJ := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) D'
          let FK := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) F'
          WEquiv DJ FK ∧ WEquiv (projectionTest DJ) (projectionTest FK)) := by
  obtain ⟨hm,hxU,hLocal⟩ := original_coefficient_companions_local hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hmB,_hxUB,_hBar,hBarStage⟩ := original_coefficient_bars_local hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hmM,_hxUM,hMasks⟩ := original_coefficient_companions_positive_masks hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hmC,_hxUC,_hMask,_hNatural,hJ,hK,_hMaxJ,_hMaxK,hJN,hKN,_hJE,_hKE,_hJd,_hKd,
    _hCompJ,_hCompK,_hWeak,_hUpper⟩ := original_lower_true_mark_companions hn Q hQ hN hE hMax W hW hSing a ha
  refine ⟨hm,hxU,?_⟩
  intro Y T hT y s
  obtain ⟨hNmember,hEmember⟩ := positive_member_geometry_on_open (hJN.trans hKN.symm) (_hJE.trans _hKE.symm) T y (maskA _ T y)
  refine ⟨hMasks T hT y s,hBarStage T hT _,hNmember,hEmember,?_⟩
  intro hy
  exact member_stage_weak_of_local hn _ _ hJ hK (hJN.trans hKN.symm) hLocal T hT _ y hy

end
end Hironaka.HironakaG1OriginalMemberStage
