import Hironaka.Resolution.HironakaActualCoefficientDivisorExponentGap
import Hironaka.Resolution.HironakaG1OriginalMemberStage
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaG1MemberCoefficientGap
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec HironakaActualCoefficientDivisorExponentGap DivisorExponentAlong
  BoundaryCount InvDomainMemberRestriction HomogenizedIdealAlong CoefficientIdeal CoefficientIdealRestriction
  HironakaG1CoeffCompanionLocal HironakaActualOriginalTrueMarkMaskCompanions HironakaEmbeddedAnalytic
  StepOneValue StepOneValueMasked NonmonomialOrderLocal NonmonomialOrderTail IdealWeightPowers CompanionRebase
  HironakaG8LocalHistory HironakaG8HomStable HironakaCoherentTransformExtension InvDomainTowerAlong

/-- Every literal open member restriction has no positive divisor exponent
strictly below its native coefficient mark. -/
theorem member_open_divisor_gap {n k : ℕ} {X : CMfd.{0} n} (P : MarkedIdeal n X)
    (hP : IsInvDomain k P) (I : Finset (Fin P.E.length)) (U : Opens X) (H : Set U) (x : U) :
    let R := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) (memberRestrict P I)
    divExpAlong n R.N R.ideal H x = 0 ∨ R.d ≤ divExpAlong n R.N R.ideal H x := by
  exact coefficient_open_divisor_exponent_gap P hP.isWellFormed.isClosedSubmanifold_N
    hP.isWellFormed.isCoherent hP.one_le_d (P.N ∩ memberInter P.E I) inter_subset_left U H x

/-- Both actual original positive lower member records have the native
divisor-exponent gap on their common Step 1 open. -/
theorem original_positive_members_divisor_gap {n k : ℕ} (hn : 0 < n) {A : CMfd.{0} n}
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
        ∀ (y : Y),
          let O := maskA J T y
          let D := geoTransformAlong (barMarked J) T
          let F := geoTransformAlong (barMarked K) T
          let DJ := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y)
            (memberRestrict D (membersThrough D.E (origMembers J T) y))
          let FK := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y)
            (memberRestrict F (membersThrough F.E (origMembers K T) y))
          ∀ (H : Set O) (z : O),
            (divExpAlong n DJ.N DJ.ideal H z = 0 ∨ DJ.d ≤ divExpAlong n DJ.N DJ.ideal H z) ∧
            (divExpAlong n FK.N FK.ideal H z = 0 ∨ FK.d ≤ divExpAlong n FK.N FK.ideal H z) := by
  obtain ⟨hm,hxU,hLocal⟩ := original_coefficient_companions_local hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hmC,_hxUC,_hMask,_hNatural,hJ,hK,_hMaxJ,_hMaxK,_hJN,_hKN,_hJE,_hKE,_hJd,_hKd,
    _hCompJ,_hCompK,_hWeak,_hUpper⟩ := original_lower_true_mark_companions hn Q hQ hN hE hMax W hW hSing a ha
  refine ⟨hm,hxU,?_⟩
  intro Y T hT y
  dsimp only
  intro H z
  have hTK := (hLocal.wEquiv.2 T).1.mp hT
  have hTD := ((bar_local_any_boundary _ hJ).wEquiv.2 T).1.mp hT
  have hTF := ((bar_local_any_boundary _ hK).wEquiv.2 T).1.mp hTK
  have hD := isInvDomain_geoTransformAlong (isInvDomain_barMarked _ hJ) T hTD
  have hF := isInvDomain_geoTransformAlong (isInvDomain_barMarked _ hK) T hTF
  exact ⟨member_open_divisor_gap _ hD _ _ H z,member_open_divisor_gap _ hF _ _ H z⟩

end
end Hironaka.HironakaG1MemberCoefficientGap
