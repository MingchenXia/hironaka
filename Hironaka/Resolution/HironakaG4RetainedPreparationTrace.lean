import Hironaka.Resolution.HironakaG34MaskFoldEquivariance
import Hironaka.Resolution.HironakaG4OrderedRetainedDefectTrace
import Hironaka.Resolution.HironakaG4SharpTerminalAtlas
import Hironaka.Resolution.HironakaG4ResidualInductionInputs

/-! The actual lower-row phases and defect reruns of a retained preparation history. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedPreparationTrace
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdealTowerTransport MarkedIdeals.MarkedIdeal
  HomogenizedGlueingTower HironakaG4SharpTerminalAtlas HironakaG4OrderedRetainedDefectTrace
  HironakaG4ResidualInductionInputs HironakaG4PreparedCentreCoordinates
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaG34MaskFoldEquivariance

/-- The recorded operation before physical restriction or rebasing. -/
inductive RetainedPreparationPhase
  | defect
  | lower (index : ℕ)

/-- First clear the defect, then rerun it after each selected lower phase. -/
def retainedPreparationPhases (indices : List ℕ) : List RetainedPreparationPhase :=
  .defect :: indices.flatMap (fun i => [.lower i,.defect])

theorem retainedPreparationPhases_append_singleton (indices : List ℕ) (i : ℕ) :
    retainedPreparationPhases (indices ++ [i]) = retainedPreparationPhases indices ++ [.lower i,.defect] := by
  simp [retainedPreparationPhases]

/-- The proof-relevant sequence attaches the selected original phases to
the physical lower terminal histories. Each distinct-defect rerun retains
its ordered crest trace. Literal source restrictions and physical rebases
remain visible in the sequence. -/
inductive RetainedPreparationTrace {n : ℕ} (hn : 0 < n) :
    {X Y : CMfd.{u} n} → Set X → List (Set X) → List (Set X) →
    List RetainedPreparationPhase → BlowupTower X Y → Type (u+1)
  | defect {X Y : CMfd.{u} n} {N : Set X} {old born : List (Set X)} {T : BlowupTower X Y}
      (trace : OrderedRetainedDefectTrace hn N old born ⊤ T) :
      RetainedPreparationTrace hn N old born [.defect] T
  | lower {X Y : CMfd.{u} n} {N : Set X} {old born : List (Set X)} {T : BlowupTower X Y}
      (geometry : NativeRetainedGeometry N old born)
      (no_defect : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
      (i : Fin old.length)
      (terminal : IsSharpTerminalTower (N ∩ (oldResidualPart N old born i).zeroLocus)
        (remainingBoundary old born i) T)
      (equivariant : IsEquivariant (N ∩ (oldResidualPart N old born i).zeroLocus)
        (remainingBoundary old born i) T) :
      RetainedPreparationTrace hn N old born [.lower i.val] T
  | append {X Y Z : CMfd.{u} n} {N : Set X} {old born : List (Set X)}
      {phases later : List RetainedPreparationPhase} (T : BlowupTower X Y) (S : BlowupTower Y Z)
      (geometry : NativeRetainedGeometry N old born)
      (carrier_test : IsGeoTestTower (geometricTemplate N born) T)
      (full_test : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
      (first : RetainedPreparationTrace hn N old born phases T)
      (continuation : RetainedPreparationTrace hn
        (geoTransformAlong (geometricTemplate N born) T).N (old.map (strictAlong T))
        (geoTransformAlong (geometricTemplate N born) T).E later S) :
      RetainedPreparationTrace hn N old born (phases ++ later) (T.append S)
  | restrictOpen {X Y : CMfd.{u} n} {N : Set X} {old born : List (Set X)}
      {phases : List RetainedPreparationPhase} {T : BlowupTower X Y} (O : Opens X)
      (geometry : NativeRetainedGeometry N old born)
      (trace : RetainedPreparationTrace hn N old born phases T) :
      RetainedPreparationTrace hn ((Subtype.val : O → X) ⁻¹' N)
        (old.map ((Subtype.val : O → X) ⁻¹' ·)) (born.map ((Subtype.val : O → X) ⁻¹' ·))
        phases (restrict O T)
  | rebase {X X' Y : CMfd.{u} n} {N : Set X} {old born : List (Set X)}
      {phases : List RetainedPreparationPhase} {T : BlowupTower X Y}
      (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
      (geometry : NativeRetainedGeometry N old born)
      (trace : RetainedPreparationTrace hn N old born phases T) :
      RetainedPreparationTrace hn (e ⁻¹' N) (old.map (e ⁻¹' ·)) (born.map (e ⁻¹' ·))
        phases (transport e T).tower

end
end Hironaka.HironakaG4RetainedPreparationTrace
