import Hironaka.Resolution.HironakaG4RetainedDefectRelativeDecrease

/-! A proof-relevant phase decomposition of an actual finite retained tower. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4OrderedRetainedDefectTrace
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport HomogenizedGlueingTower
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaG4PreparedCentreCoordinates HironakaG4RetainedDefectRelativeDecrease
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance

abbrev RetainedStampRank := (ℕ ×ₗ ℕ) ×ₗ ℕ

/-- Native input geometry attached to a physical source change. -/
structure NativeRetainedGeometry {n : ℕ} {X : CMfd.{u} n}
    (N : Set X) (old born : List (Set X)) : Prop where
  carrier : IsClosedSubmanifold n N
  full : IsSNCDivisor n (old ++ born)
  born_transverse : IsTransverse n N born
  dense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G)

/-- The original carrier and both ordered boundaries restrict literally. -/
theorem NativeRetainedGeometry.restrict {n : ℕ} {X : CMfd.{u} n} {N : Set X}
    {old born : List (Set X)} (h : NativeRetainedGeometry N old born) (U : Opens X) :
    let v := (Subtype.val : U → X)
    NativeRetainedGeometry (X := CMfd.of (n := n) U) (v ⁻¹' N) (old.map (v ⁻¹' ·))
      (born.map (v ⁻¹' ·)) := by
  intro v
  refine ⟨BlowupRestrictOpen.isClosedSubmanifold_preimage_val h.carrier U, ?_,
    isTransverse_preimage (pullsBackCoordinates_val U) h.born_transverse, ?_⟩
  · simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) U) continuous_subtype_val h.full
  · simpa only [List.map_append] using HironakaG34NonPureLowDim.open_full_density h.dense U

/-- The actual sequence of selected phases, with their strict ordered rank
cutoffs. Servicing an enclosure retains its literal open restrictions and
biholomorphic base transports at the points where they are used. -/
inductive OrderedRetainedDefectTrace {n : ℕ} (hn : 0 < n) :
    {X Y : CMfd.{u} n} → Set X → List (Set X) → List (Set X) →
    WithTop RetainedStampRank → BlowupTower X Y → Type (u+1)
  | done {X : CMfd.{u} n} {N : Set X} {old born : List (Set X)}
      {μ : WithTop RetainedStampRank}
      (defect_empty : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅) :
      OrderedRetainedDefectTrace hn N old born μ (.refl : BlowupTower X X)
  | phase {X Y Z : CMfd.{u} n} {N : Set X} {old born : List (Set X)}
      {μ : WithTop RetainedStampRank} (T : BlowupTower X Y) (S : BlowupTower Y Z)
      (crest : RetainedDefectCrestPhase hn N old born T) (bound : (crest.rank : WithTop _) < μ)
      (carrier_test : IsGeoTestTower (geometricTemplate N born) T)
      (full_test : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
      (continuation : OrderedRetainedDefectTrace hn
        (geoTransformAlong (geometricTemplate N born) T).N (old.map (strictAlong T))
        (geoTransformAlong (geometricTemplate N born) T).E crest.rank S) :
      OrderedRetainedDefectTrace hn N old born μ (T.append S)
  | restrictOpen {X Y : CMfd.{u} n} {N : Set X} {old born : List (Set X)}
      {μ : WithTop RetainedStampRank} {T : BlowupTower X Y} (O : Opens X)
      (geometry : NativeRetainedGeometry N old born)
      (trace : OrderedRetainedDefectTrace hn N old born μ T) :
      OrderedRetainedDefectTrace hn ((Subtype.val : O → X) ⁻¹' N)
        (old.map ((Subtype.val : O → X) ⁻¹' ·)) (born.map ((Subtype.val : O → X) ⁻¹' ·))
        μ (restrict O T)
  | rebase {X X' Y : CMfd.{u} n} {N : Set X} {old born : List (Set X)}
      {μ : WithTop RetainedStampRank} {T : BlowupTower X Y}
      (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
      (geometry : NativeRetainedGeometry N old born)
      (trace : OrderedRetainedDefectTrace hn N old born μ T) :
      OrderedRetainedDefectTrace hn (e ⁻¹' N) (old.map (e ⁻¹' ·)) (born.map (e ⁻¹' ·)) μ
        (transport e T).tower

/-- The number of selected phases is independent of literal source changes. -/
def OrderedRetainedDefectTrace.phaseCount {n : ℕ} {hn : 0 < n} {X Y : CMfd.{u} n}
    {N : Set X} {old born : List (Set X)} {μ : WithTop RetainedStampRank} {T : BlowupTower X Y}
    (trace : OrderedRetainedDefectTrace hn N old born μ T) : ℕ :=
  match trace with
  | .done _ => 0
  | .phase _ _ _ _ _ _ tail => tail.phaseCount + 1
  | .restrictOpen _ _ tree => tree.phaseCount
  | .rebase _ _ tree => tree.phaseCount

end
end Hironaka.HironakaG4OrderedRetainedDefectTrace
