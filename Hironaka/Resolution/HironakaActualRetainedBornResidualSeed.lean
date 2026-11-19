import Hironaka.Resolution.HironakaG4OriginalSelectedResidualTail
import Hironaka.Resolution.HironakaG4RecordedTowerResidualCompatibility
import Hironaka.Resolution.HironakaG4ResidualInductionInputs

/-!
# The same original residual seed with its entire current born boundary

Blueprint: `hironaka-actual-retained-born-residual-seed-20261101.tex`.
The current seed uses the actual canonical residual, never a reset raw trace.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaActualRetainedBornResidualSeed

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsComparison DivisorExponentAlong
  HironakaG4PreparedCentreCoordinates HironakaG4RecordedTowerResidualCompatibility
  HironakaSharpActualFiniteChronologicalHistory
  RelativePrincipalizationSpan RestrictedIdealExtension

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- The actual normalized residual, with the ENTIRE retained born list. -/
def retainedResidualMarked (N : Set X) (old born : List (Set X))
    (i : Fin old.length) : MarkedIdeal n X :=
  ⟨N, born, oldResidualPart N old born i, 0⟩

/-- Genuine source geometry supplies all seed inputs, including relative
principality; none is a future residual-comparison hypothesis. -/
theorem retainedResidualMarked_geometry (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H)) (i : Fin old.length) :
    (retainedResidualMarked N old born i).IsWellFormed ∧
      (∀ x ∈ N, IsNonzeroAlongAt N (retainedResidualMarked N old born i).ideal x) ∧
      ∀ x ∈ N, ∃ c : X → ℂ, HolomorphicAt n c x ∧
        ∀ g, (retainedResidualMarked N old born i).ideal.mem x g ↔
          HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = c) x g := by
  obtain ⟨_hcI, _hnzI, hcJ, hnzJ, _hcD, _hnzD, _hmD, _hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  have hBorn : IsSNCDivisor n born :=
    isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  refine ⟨⟨hN, hcJ, hBorn, hTr⟩, hnzJ, ?_⟩
  intro x hx
  exact HironakaG4ResidualInductionInputs.actual_residual_principal_native
    hn hN hE hTr hdense i hx

/-- All four fields agree with the SAME original current chronological row. -/
theorem retained_seed_eq_original_chronological (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (i : Fin E.length) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let j : Fin (E.map (strictAlong T)).length :=
      ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
    retainedResidualMarked A.N (E.map (strictAlong T)) A.E j =
      chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let j : Fin (E.map (strictAlong T)).length :=
    ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
  have hDict := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hGeom := chronologicalMarked_geometric_fields
    (originalRelativeMemberMarked W (E.get i)) T
  have hN : (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N = A.N :=
    hGeom.1
  have hE' : (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).E = A.E :=
    hGeom.2
  have hI := (hDict.2.2.2.2 i).2.2.1
  have hD := chronologicalMarked_zero_mark (originalRelativeMemberMarked W (E.get i)) rfl T
  have hI' : oldResidualPart A.N (E.map (strictAlong T)) A.E j =
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal := by
    simpa [oldResidualPart, oldTraceIdeal, j] using hI
  change (⟨A.N, A.E, oldResidualPart A.N (E.map (strictAlong T)) A.E j, 0⟩ :
    MarkedIdeal n Y) = _
  rw [hI', ← hN, ← hE', ← hD]

/-- ANY actual appended tail starts from the true current residual seed,
retaining the same original row, every born label and every empty step. -/
theorem retained_seed_chronological_append (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (i : Fin E.length) (R : BlowupTower Y Z) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let j : Fin (E.map (strictAlong T)).length :=
      ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
    chronologicalMarked (retainedResidualMarked A.N (E.map (strictAlong T)) A.E j) R =
      chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R) := by
  dsimp only
  rw [retained_seed_eq_original_chronological hn hW hE hdense T hT hFull i]
  exact (HironakaG4OriginalSelectedResidualTail.chronological_append_native
    (originalRelativeMemberMarked W (E.get i)) T R).symm

end
end Hironaka.HironakaActualRetainedBornResidualSeed
