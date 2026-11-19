import Hironaka.Resolution.HironakaG8PowerCompanionMasks
import Hironaka.Resolution.HironakaCoherentTransformExtension
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PowerLowerGeometry
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec NonmonomialOrderLocal NonmonomialOrderTail CompanionRebase CompanionReductionAlong
  HironakaActualPowerBoundaryExponents HironakaActualOriginalPowerTransform
  HironakaG8PowerCompanionLocal HironakaG8PowerActualCompanionStep HironakaG8PowerCompanionMasks
  HironakaG8MemberLoci HironakaCoherentTransformExtension StepOneValue
  InvDomainMemberRestriction InvDomainRebase

/-- The native positive-level member restriction retains equal carrier and
ordered boundary whenever the original records have equal carrier/boundary.
No equality of their coefficient ideals is inferred. -/
theorem positive_member_geometry_of_N_E {n : ℕ} {X Y : CMfd.{0} n}
    {A B : MarkedIdeal n X} (hN : A.N = B.N) (hE : A.E = B.E)
    (T : BlowupTower X Y) (y : Y) :
    let P := geoTransformAlong (barMarked A) T
    let Q := geoTransformAlong (barMarked B) T
    let P' := memberRestrict P (membersThrough P.E (origMembers A T) y)
    let Q' := memberRestrict Q (membersThrough Q.E (origMembers B T) y)
    P'.N = Q'.N ∧ P'.E = Q'.E := by
  have hN0 : (barMarked A).N = (barMarked B).N := hN
  have hE0 : (barMarked A).E = (barMarked B).E := hE
  have hNT := geoTransformAlong_N_eq_of_N_eq hN0 T
  have hET := MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hE0 T
  have hO := origMembers_eq_of_E_eq hE T
  constructor
  · rw [memberRestrict_membersThrough_N,memberRestrict_membersThrough_N, hNT,hET,hO]
  · rw [memberRestrict_membersThrough_E,memberRestrict_membersThrough_E, hET,hO]

/-- Restricting those literal member records to the same open retains their
common carrier and ordered boundary. -/
theorem positive_member_geometry_on_open {n : ℕ} {X Y : CMfd.{0} n}
    {A B : MarkedIdeal n X} (hN : A.N = B.N) (hE : A.E = B.E)
    (T : BlowupTower X Y) (y : Y) (U : Opens Y) :
    let P := geoTransformAlong (barMarked A) T
    let Q := geoTransformAlong (barMarked B) T
    let P' := memberRestrict P (membersThrough P.E (origMembers A T) y)
    let Q' := memberRestrict Q (membersThrough Q.E (origMembers B T) y)
    (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y) P').N =
      (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y) Q').N ∧
    (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y) P').E =
      (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y) Q').E := by
  obtain ⟨hPN,hPE⟩ := positive_member_geometry_of_N_E hN hE T y
  constructor
  · change (Subtype.val : U → Y) ⁻¹' _ = (Subtype.val : U → Y) ⁻¹' _
    rw [hPN]
  · change List.map ((Subtype.val : U → Y) ⁻¹' ·) _ = List.map ((Subtype.val : U → Y) ⁻¹' ·) _
    rw [hPE]

/-- Positive-level lower records of an original companion and its recoding
have the same carrier and boundary on the common literal Step 1 mask. -/
theorem positive_member_geometry_power_companions {n : ℕ} {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (e o : ℕ) (T : BlowupTower X Y) (y : Y) :
    let A := companionOf n M o
    let B := companionOf n (powerMarked M e) (e*o)
    let U := maskA A T y
    let P := geoTransformAlong (barMarked A) T
    let Q := geoTransformAlong (barMarked B) T
    let P' := memberRestrict P (membersThrough P.E (origMembers A T) y)
    let Q' := memberRestrict Q (membersThrough Q.E (origMembers B T) y)
    (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y) P').N =
      (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y) Q').N ∧
    (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y) P').E =
      (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y) Q').E := by
  have hE : (companionOf n M o).E = (companionOf n (powerMarked M e) (e*o)).E := by
    simp only [companionOf, companionAlong_E, powerMarked]
  have hN : (companionOf n M o).N = (companionOf n (powerMarked M e) (e*o)).N := by
    simp only [companionOf, companionAlong_N, powerMarked]
  exact positive_member_geometry_on_open hN hE T y _

/-- Literal actual masked companions have the same positive-level lower
carrier and ordered boundary on their common Step 1 mask. This isolates the
remaining comparison to their transformed marked ideals and recursive values. -/
theorem positive_member_geometry_actual_masked_companions {n : ℕ} (hn : 0 < n)
    {X Y Z : CMfd.{0} n} {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {e o : ℕ} (he : 1 ≤ e) (ho : 1 ≤ o) (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    let W := ordMask (geoTransformAlong M T) o
    let A := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) (geoTransformAlong M T)
    let B := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y)
      (geoTransformAlong (powerMarked M e) T)
    let C := companionOf n A o
    let D := companionOf n B (e*o)
    ∀ (S : BlowupTower (CMfd.of (n := n) W) Z) (z : Z),
      let U := maskA C S z
      let P := geoTransformAlong (barMarked C) S
      let Q := geoTransformAlong (barMarked D) S
      let P' := memberRestrict P (membersThrough P.E (origMembers C S) z)
      let Q' := memberRestrict Q (membersThrough Q.E (origMembers D S) z)
      (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Z) P').N =
        (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Z) Q').N ∧
      (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Z) P').E =
        (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Z) Q').E := by
  let W := ordMask (geoTransformAlong M T) o
  let A := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) (geoTransformAlong M T)
  let B := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y)
    (geoTransformAlong (powerMarked M e) T)
  let C := companionOf n A o
  let D := companionOf n B (e*o)
  have hE : C.E = D.E := (masked_companion_local_original_power_history hn M hM he ho T hT).wEquiv.1
  have hPowerN := (original_power_transform M hM e he T hT).2.N_eq
  have hN : C.N = D.N := by
    simp only [C, D, companionOf, companionAlong_N]
    change A.N = B.N
    change (Subtype.val : W → Y) ⁻¹' (geoTransformAlong M T).N =
      (Subtype.val : W → Y) ⁻¹' (geoTransformAlong (powerMarked M e) T).N
    rw [hPowerN]
    rfl
  change ∀ (S : BlowupTower (CMfd.of (n := n) W) Z) (z : Z), _
  intro S z
  exact positive_member_geometry_on_open hN hE S z _

end
end Hironaka.HironakaG8PowerLowerGeometry
