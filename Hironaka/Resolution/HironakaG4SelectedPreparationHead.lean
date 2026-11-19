import Hironaka.Resolution.HironakaG4RetainedPreparationHead

/-! Expose the actual selected lower tower and its immediate defect rerun
for whole overlap comparison. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4SelectedPreparationHead
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport HomogenizedGlueingTower
  HironakaSharpActualFiniteChronologicalHistory HironakaG4OrderedRetainedDefectTrace
  HironakaG4RetainedPreparationTrace HironakaG4RetainedPreparationEvent
  HironakaG4RetainedPreparationHeadTests HironakaG4RetainedPreparationHead HironakaG4RetainedPreparationLowerHistory
  HironakaSharpActualChronologicalDistinctDefect HironakaG4PreparedCentreCoordinates
  HironakaG4ResidualInductionInputs HironakaG4SharpTerminalAtlas HironakaG34MaskFoldEquivariance

variable {n : ℕ} {hn : 0 < n} {X Y : CMfd.{u} n} {N : Set X} {old born : List (Set X)}
  {T : BlowupTower X Y} {index : ℕ} {later : List RetainedPreparationPhase}

/-- The consecutive lower and defect blocks retain the precise old row
and the native ordered defect rerun on the lower block's actual codomain. -/
structure SelectedPreparationHead (hn : 0 < n) (N : Set X) (old born : List (Set X))
    (T : BlowupTower X Y) (index : ℕ) (later : List RetainedPreparationPhase) where
  lowerTarget : CMfd.{u} n
  defectTarget : CMfd.{u} n
  target : CMfd.{u} n
  lower : BlowupTower X lowerTarget
  defect : BlowupTower lowerTarget defectTarget
  rest : BlowupTower defectTarget target
  geometry : NativeRetainedGeometry N old born
  noDefect : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅
  row : Fin old.length
  rowIndex : row.val = index
  terminal : IsSharpTerminalTower (N ∩ (oldResidualPart N old born row).zeroLocus)
    (remainingBoundary old born row) lower
  equivariant : IsEquivariant (N ∩ (oldResidualPart N old born row).zeroLocus)
    (remainingBoundary old born row) lower
  lowerTests : BlockTests N old born lower
  rerun : OrderedRetainedDefectTrace hn (geoTransformAlong (geometricTemplate N born) lower).N
    (old.map (strictAlong lower)) (geoTransformAlong (geometricTemplate N born) lower).E ⊤ defect
  continuation : RetainedPreparationTail hn
    (geoTransformAlong (geometricTemplate N born) (lower.append defect)).N
    (old.map (strictAlong (lower.append defect)))
    (geoTransformAlong (geometricTemplate N born) (lower.append defect)).E later rest
  equiv : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ target
  iso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T ((lower.append defect).append rest) equiv

/-- The lower chart certificate applies to the actual selected lower
tower, and all later lower leaves remain certified. -/
def SelectedPreparationHead.usesLowerHistory (P : SharpHistoryPredicate.{u} n)
    (head : SelectedPreparationHead hn N old born T index later) : Prop :=
  P (N ∩ (oldResidualPart N old born head.row).zeroLocus)
      (remainingBoundary old born head.row) head.lower ∧
    head.continuation.usesLowerHistory P

variable {P : SharpHistoryPredicate.{u} n}

set_option maxHeartbeats 650000 in
/-- Read the actual selected lower and its immediate defect rerun together,
retaining the exact unprocessed phase tape and the whole physical tower. -/
def selectedPreparationHeadWithLower (actions : LowerHistoryActions P)
    (tape : RetainedPreparationTrace hn N old born (.lower index :: .defect :: later) T)
    (hUses : usesLowerHistory P tape) :
    { H : SelectedPreparationHead hn N old born T index later // H.usesLowerHistory P } := by
  obtain ⟨head,hHead⟩ := retainedPreparationHeadWithLower actions tape hUses
  cases head with
  | cons R S event remaining e hIso =>
    cases event with
    | lower g hEmpty j hTerminal hEq =>
      cases remaining with
      | trace tail =>
        obtain ⟨head',hHead'⟩ := retainedPreparationHeadWithLower actions tail hHead.2
        cases head' with
        | cons Q U event remaining e' hIso' =>
          cases event with
          | defect hDefect =>
            obtain ⟨hC,hOld⟩ := current_retained_records_append N old born R Q
            let rest := RetainedPreparationTail.castWithLower (congrArg MarkedIdeal.N hC).symm hOld.symm
              (congrArg MarkedIdeal.E hC).symm ⟨remaining,hHead'.2⟩
            have hI := hIso.trans ((IsTowerIso.refl_self R).append hIso')
            have hBase : (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞).trans
                (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) =
                  Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞ := Diffeomorph.ext fun _ => rfl
            rw [hBase,← BlowupTower.append_assoc] at hI
            exact ⟨⟨_,_,_,R,Q,U,g,hEmpty,j,rfl,hTerminal,hEq,
              lower_blockTests hn g hEmpty j hTerminal,hDefect,rest.val,_,hI⟩,hHead.1,rest.property⟩

/-- Read the actual selected lower and defect rerun, together with the
physical comparison and literal continuation. -/
def selectedPreparationHead
    (tape : RetainedPreparationTrace hn N old born (.lower index :: .defect :: later) T) :
    SelectedPreparationHead hn N old born T index later :=
  (selectedPreparationHeadWithLower unrestrictedLowerHistoryActions tape (usesLowerHistory_unrestricted tape)).val

end
end Hironaka.HironakaG4SelectedPreparationHead
