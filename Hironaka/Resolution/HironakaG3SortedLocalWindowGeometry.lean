import Hironaka.Resolution.HironakaG3OrderedFiniteWindows
import Hironaka.Resolution.HironakaG3SeparatedVisibleChartSNC
import Hironaka.Resolution.HironakaG3RTowerClass
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SortedLocalWindowGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings NormalCrossingsInvariance
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3OrderedFiniteWindows
  HironakaDisjointFiniteControlledHistory
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)

/-- A class-local certificate retaining complete globally sorted labels and
literal transformed-boundary SNC and strict-target NC. -/
def HasSortedLocalWindowGeometry {n : ℕ} {X : CMfd.{0} n} {κ : Type*} [LinearOrder κ]
    (C : Set X) (D : κ → Set X) (K : LocalTowerClass X) : Prop :=
  ∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
    K U Y T → ∀ R : Finset κ, (∀ j, (D j ∩ (U : Set X)).Nonempty → j ∈ R) →
    ∃ L : Finset κ, (∀ j, (D j ∩ (U : Set X)).Nonempty → j ∈ L) ∧
      let E := ((L.sort (· ≤ ·)).map D).map ((Subtype.val : U → X) ⁻¹' ·)
      let J := GermIdeal.pullback (m := n) (Subtype.val : U → X) (vanishingIdeal (n := n) (∅ : Set X))
      IsSNCDivisor n (geoTransformAlong (fullMarked E J) T).E ∧
        HasNormalCrossings n (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C))
          (geoTransformAlong (fullMarked E J) T).E

/-- Empty towers preserve SNC for any sorted finite indexed boundary window. -/
theorem empty_tower_sorted_window_snc {n : ℕ} {X : CMfd.{0} n} {κ : Type*} [LinearOrder κ]
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) (R : Finset κ)
    (U : Opens X) {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) U) Y)
    (hT : IsEmptyTower T) :
    let E := ((R.sort (· ≤ ·)).map D).map ((Subtype.val : U → X) ⁻¹' ·)
    let J := GermIdeal.pullback (m := n) (Subtype.val : U → X) (vanishingIdeal (n := n) (∅ : Set X))
    IsSNCDivisor n (geoTransformAlong (fullMarked E J) T).E := by
  let B := (R.sort (· ≤ ·)).map D
  have hB : IsSNCDivisor n B := sorted_boundary_snc D hD R
  have hB₀ : IsSNCDivisor n (B.map ((Subtype.val : U → X) ⁻¹' ·)) :=
    NormalCrossingsInvariance.isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hB
  exact HironakaG8P1ArcPair.isSNCDivisor_geoTransformAlong hB₀ T
    (isGeoTestTower_of_isEmptyTower (fullMarked _ _) T hT)
end
end Hironaka.HironakaG3SortedLocalWindowGeometry
