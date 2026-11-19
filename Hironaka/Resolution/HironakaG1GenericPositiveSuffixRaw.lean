import Hironaka.Resolution.HironakaG1GenericPositiveClassData
import Hironaka.Resolution.HironakaG8ScaledNonmonomialHistory

/-! Normalized nonmonomial order on actual positive-member controlled suffixes. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1GenericPositiveSuffixRaw
noncomputable section
open MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal MarkedIdealBiholomorphism
  BlowupTowers BlowupTowerTransforms ResolutionInvariantSpec StepOneValue StepOneValueMasked
  InvDomainMemberRestriction NonmonomialOrderLocal
  HironakaG8LocalHistory HironakaG1GenericPositiveClassData HironakaG8ScaledNonmonomialHistory

/-- Along every common suffix of a positive member step, the native
nonmonomial orders are equal after scaling by the opposite mark. The initial
pair can have an arbitrary boundary and unequal marks. -/
theorem positive_member_scaled_nmOrd_along {n kA kB : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (A B : MarkedIdeal n X)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hN : A.N = B.N)
    (hL : LocWPEquiv A B) (T : BlowupTower X Y) (hT : IsGeoTestTower A T)
    (y : Y) (s : ℕ) (hlevel : level A T y = s+1) :
    let O := maskA A T y
    let P := geoTransformAlong (barMarked A) T
    let Q := geoTransformAlong (barMarked B) T
    let A' := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y)
      (memberRestrict P (membersThrough P.E (origMembers A T) y))
    let B' := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y)
      (memberRestrict Q (membersThrough Q.E (origMembers B T) y))
    ∀ {Z : CMfd.{0} n} (S : BlowupTower (CMfd.of (n := n) O) Z),
      IsGeoTestTower A' S → ∀ z ∈ (geoTransformAlong A' S).cosupp,
      B'.d * nmOrd (geoTransformAlong A' S) z = A'.d * nmOrd (geoTransformAlong B' S) z := by
  dsimp only
  obtain ⟨hA', hB', hN', hE', hL', hInitial⟩ := positive_member_class_data hn A B hA hB hN hL T hT y s hlevel
  intro Z S hS z hz
  exact scaled_nmOrd_of_initial_exponents hn _ _ hA' hB' hN'.symm hE'.symm hL' hInitial S hS z hz
end
end Hironaka.HironakaG1GenericPositiveSuffixRaw
