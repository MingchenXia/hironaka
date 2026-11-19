import Hironaka.Resolution.HironakaG1OriginalMemberStage
import Hironaka.Resolution.HironakaG8MemberIndexedLocal
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaG1MemberStageLocal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec HironakaG1CoeffBarLocal HironakaG8LocalHistory HironakaG8HomStable
  HironakaG8MemberIndexedLocal HironakaG8PowerLowerGeometry HironakaG8MemberLoci
  StepOneValue StepOneValueMasked StepOneBridge InvDomainMemberRestriction InvDomainTowerAlong HironakaCoherentTransformExtension
  MarkedIdealEquivalence.MarkedIdeal MarkedIdealRestrictOpen
  HironakaG1CoeffCompanionLocal HironakaG1GenericPositiveMask HironakaActualOriginalTrueMarkMaskCompanions
  HironakaEmbeddedAnalytic NonmonomialOrderLocal NonmonomialOrderTail HomogenizedIdealAlong
  CoefficientIdeal IdealWeightPowers CompanionRebase

/-- Literal member-restricted bar records remain fully locally equivalent
on every open after every common tested prefix. -/
theorem member_stage_local_of_local {n kA kB : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N = B.N) (hL : LocWPEquiv A B) (T : BlowupTower X Y) (hT : IsGeoTestTower A T)
    (U : Opens Y) (z : Y) :
    let P := geoTransformAlong (barMarked A) T
    let Q := geoTransformAlong (barMarked B) T
    LocWPEquiv (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y)
      (memberRestrict P (membersThrough P.E (origMembers A T) z)))
      (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y)
      (memberRestrict Q (membersThrough Q.E (origMembers B T) z))) := by
  let P := geoTransformAlong (barMarked A) T
  let Q := geoTransformAlong (barMarked B) T
  have hTB := (hL.wEquiv.2 T).1.mp hT
  have hTP := ((bar_local_any_boundary A hA).wEquiv.2 T).1.mp hT
  have hTQ := ((bar_local_any_boundary B hB).wEquiv.2 T).1.mp hTB
  have hPD := isInvDomain_geoTransformAlong (isInvDomain_barMarked A hA) T hTP
  have hQD := isInvDomain_geoTransformAlong (isInvDomain_barMarked B hB) T hTQ
  have hE : A.E = B.E := hL.wEquiv.1
  have hNT : P.N = Q.N := geoTransformAlong_N_eq_of_N_eq (by simpa only [barMarked_N] using hN) T
  have hBar := (bar_local_of_local A B hA hB hL).geoTransformAlong T hTP
  obtain ⟨hSN,hSE⟩ := positive_member_geometry_of_N_E hN hE T z
  have hCut := memberLocal_of_matching_indexed (κ := Kinds.wp) rfl hn hPD.isWellFormed hQD.isWellFormed
    hPD.one_le_d hQD.one_le_d hNT hBar (membersThrough P.E (origMembers A T) z)
    (membersThrough Q.E (origMembers B T) z) hSN hSE
  exact hCut.restrict U

/-- The original given-Q pair's literal positive-level lower member records
are fully locally equivalent on their common Step 1 mask. -/
theorem original_positive_member_local {n k : ℕ} (hn : 0 < n) {A : CMfd.{0} n}
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
      x ∈ U ∧ ∀ {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) U) Y), IsGeoTestTower J T →
        ∀ (y : Y) (s : ℕ),
          let O := maskA J T y
          let D := geoTransformAlong (barMarked J) T
          let F := geoTransformAlong (barMarked K) T
          lowerMask J (s+1) T y = lowerMask K (s+1) T y ∧
          LocWPEquiv (MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y)
            (memberRestrict D (membersThrough D.E (origMembers J T) y)))
            (MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y)
            (memberRestrict F (membersThrough F.E (origMembers K T) y))) := by
  obtain ⟨hm,hxU,hLocal⟩ := original_coefficient_companions_local hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hmM,_hxUM,hMasks⟩ := original_coefficient_companions_positive_masks hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hmC,_hxUC,_hMask,_hNatural,hJ,hK,_hMaxJ,_hMaxK,hJN,hKN,_hJE,_hKE,_hJd,_hKd,
    _hCompJ,_hCompK,_hWeak,_hUpper⟩ := original_lower_true_mark_companions hn Q hQ hN hE hMax W hW hSing a ha
  refine ⟨hm,hxU,?_⟩
  intro Y T hT y s
  exact ⟨hMasks T hT y s,member_stage_local_of_local hn _ _ hJ hK (hJN.trans hKN.symm) hLocal T hT _ y⟩
end
end Hironaka.HironakaG1MemberStageLocal
