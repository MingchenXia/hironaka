import Hironaka.Resolution.HironakaG4RetainedRelativeLowerService
import Hironaka.Resolution.HironakaG4RetainedPreparationLowerHistory
import Hironaka.Resolution.HironakaG4RetainedPreparationHeadTests
import Hironaka.Resolution.HironakaG4SelectedLowerOverlapData
import Hironaka.Resolution.HironakaG4SharpTerminalOpen

/-! A single recorded preparation event on its actual physical source. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedPreparationEvent
noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail MarkedIdealTowerTransport
  HironakaG4RetainedPreparationTrace HironakaG4OrderedRetainedDefectTrace
  HironakaG4SharpTerminalAtlas HironakaG4SharpTerminalOpen
  HironakaG4ResidualInductionInputs HironakaG4PreparedCentreCoordinates
  HironakaSharpActualChronologicalDistinctDefect HironakaG34MaskFoldEquivariance
  HironakaG4RetainedDefectTraceEquivariance HironakaG4RetainedRelativeLowerService
  HironakaG4RetainedTraceComparison HironakaG4RetainedPreparationHeadTests
  HironakaG4RetainedCurrentStamp HironakaG4SelectedLowerOverlapData HironakaG3EmptyAwareBornSlots
  HironakaG4RetainedPreparationLowerHistory

variable {n : ℕ} {X Y X' : CMfd.{u} n}

/-- One already constructed defect or selected-lower tower, with no source
change pending in its data. -/
inductive RetainedPreparationEvent (hn : 0 < n) (N : Set X) (old born : List (Set X))
    (T : BlowupTower X Y) : RetainedPreparationPhase → Type (u+1)
  | defect (trace : OrderedRetainedDefectTrace hn N old born ⊤ T) :
      RetainedPreparationEvent hn N old born T .defect
  | lower (g : NativeRetainedGeometry N old born)
      (noDefect : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
      (i : Fin old.length)
      (terminal : IsSharpTerminalTower (N ∩ (oldResidualPart N old born i).zeroLocus)
        (remainingBoundary old born i) T)
      (equivariant : IsEquivariant (N ∩ (oldResidualPart N old born i).zeroLocus)
        (remainingBoundary old born i) T) :
      RetainedPreparationEvent hn N old born T (.lower i.val)

variable {hn : 0 < n} {N : Set X} {old born : List (Set X)}
  {T : BlowupTower X Y} {phase : RetainedPreparationPhase}

/-- Both upper tests refer to the same event tower. -/
theorem RetainedPreparationEvent.tests (E : RetainedPreparationEvent hn N old born T phase) :
    BlockTests N old born T := by
  cases E with
  | defect trace => exact ordered_defect_blockTests trace
  | lower g hEmpty i hT _ => exact lower_blockTests hn g hEmpty i hT

/-- Allowed changes of source for the lower-dimensional chart predicate. -/
structure LowerHistoryActions (P : SharpHistoryPredicate.{u} n) : Prop where
  restrictOpen : ∀ {A B : CMfd.{u} n} {W : Set A} {F : List (Set A)} {R : BlowupTower A B},
    P W F R → ∀ U : Opens A,
      P ((Subtype.val : U → A) ⁻¹' W) (F.map ((Subtype.val : U → A) ⁻¹' ·)) (restrict U R)
  rebase : ∀ {A A' B : CMfd.{u} n} {W : Set A} {F : List (Set A)} {R : BlowupTower A B},
    P W F R → ∀ e : A' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A,
      P (e ⁻¹' W) (F.map (e ⁻¹' ·)) (transport e R).tower

theorem unrestrictedLowerHistoryActions :
    LowerHistoryActions (n := n) (fun {_ _} _ _ _ => True) :=
  ⟨fun _ _ => trivial,fun _ _ => trivial⟩

/-- The actual normalized lower event carries the same lower-history
predicate on its current physical source. -/
def RetainedPreparationEvent.usesLowerHistory (P : SharpHistoryPredicate.{u} n)
    (event : RetainedPreparationEvent hn N old born T phase) : Prop :=
  match event with
  | .defect _ => True
  | .lower _ _ i _ _ =>
    P (N ∩ (oldResidualPart N old born i).zeroLocus) (remainingBoundary old born i) T

theorem RetainedPreparationEvent.usesLowerHistory_unrestricted
    (event : RetainedPreparationEvent hn N old born T phase) :
    event.usesLowerHistory (fun {_ _} _ _ _ => True) := by
  cases event <;> trivial

variable {P : SharpHistoryPredicate.{u} n}

/-- The selected lower support and its remaining ordered boundary pull back
under a physical rebase, keeping the original numerical row. -/
theorem retained_selected_lower_tuple_rebase (hn : 0 < n)
    (g : NativeRetainedGeometry N old born) (i : Fin old.length)
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    let N' := e ⁻¹' N
    let old' := old.map (e ⁻¹' ·)
    let born' := born.map (e ⁻¹' ·)
    let j : Fin old'.length := Fin.cast (List.length_map _).symm i
    N' ∩ (oldResidualPart N' old' born' j).zeroLocus =
      e ⁻¹' (N ∩ (oldResidualPart N old born i).zeroLocus) ∧
    remainingBoundary old' born' j = (remainingBoundary old born i).map (e ⁻¹' ·) := by
  intro N' old' born' j
  have hSupport := (selected_lower_data_under_endpoint hn e g
    (N' := N') (old' := old') (born' := born') rfl rfl
    (filter_map_bijection e e.surjective born) i j rfl).2.1
  refine ⟨hSupport,?_⟩
  change (old.map (e ⁻¹' ·)).eraseIdx i.val ++ born.map (e ⁻¹' ·) =
    (old.eraseIdx i.val ++ born).map (e ⁻¹' ·)
  rw [List.map_append,List.eraseIdx_map]

/-- Physical open restriction keeps the named original phase and its
selected lower certificate on the restricted tower. -/
def RetainedPreparationEvent.restrictOpenWithLower (E : RetainedPreparationEvent hn N old born T phase)
    (actions : LowerHistoryActions P) (hUses : E.usesLowerHistory P)
    (g : NativeRetainedGeometry N old born) (O : Opens X) :
    let f := (Subtype.val : O → X)
    { event : RetainedPreparationEvent hn (f ⁻¹' N) (old.map (f ⁻¹' ·)) (born.map (f ⁻¹' ·))
        (restrict O T) phase // event.usesLowerHistory P } := by
  intro f
  cases E with
  | defect trace => exact ⟨.defect (trace.restrictOpen O g),trivial⟩
  | lower g' hEmpty i hT hEq =>
    let j : Fin (old.map (f ⁻¹' ·)).length := Fin.cast (List.length_map _).symm i
    have hEmptyO := (actual_retained_defect_and_rank_open hn g'.carrier g'.full
      g'.born_transverse g'.dense O).1
    rw [hEmpty,preimage_empty] at hEmptyO
    have hL := (retained_selected_lower_geometry hn g' hEmpty i).1
    have hTO := sharpTerminal_restrict hL O T hT
    have hEqO := isEquivariant_restrictOpen hEq O
    obtain ⟨hCarrier,hBoundary⟩ := retained_selected_lower_tuple_open hn g' i O
    have hUseO := actions.restrictOpen (W := N ∩ (oldResidualPart N old born i).zeroLocus)
      (F := remainingBoundary old born i) (R := T) hUses O
    rw [← hCarrier,← hBoundary] at hTO hEqO hUseO
    exact ⟨.lower (g'.restrict O) hEmptyO j hTO hEqO,hUseO⟩

/-- Physical rebasing keeps the named original phase and its selected lower
certificate on the transported tower. -/
def RetainedPreparationEvent.rebaseWithLower (E : RetainedPreparationEvent hn N old born T phase)
    (actions : LowerHistoryActions P) (hUses : E.usesLowerHistory P)
    (g : NativeRetainedGeometry N old born)
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    { event : RetainedPreparationEvent hn (e ⁻¹' N) (old.map (e ⁻¹' ·)) (born.map (e ⁻¹' ·))
        (transport e T).tower phase // event.usesLowerHistory P } := by
  cases E with
  | defect trace => exact ⟨.defect (trace.rebase e g),trivial⟩
  | lower g' hEmpty i hT hEq =>
    let j : Fin (old.map (e ⁻¹' ·)).length := Fin.cast (List.length_map _).symm i
    have hEmpty' := (actual_retained_defect_and_rank_biholomorph hn g'.carrier g'.full
      g'.born_transverse g'.dense e).1
    rw [hEmpty,preimage_empty] at hEmpty'
    have hT' := sharpTerminal_rebase e _ _ T hT
    have hEq' := isEquivariant_of_actualIso (transport_isTowerIso e T) hEq
    obtain ⟨hCarrier,hBoundary⟩ := retained_selected_lower_tuple_rebase hn g' i e
    have hUse' := actions.rebase (W := N ∩ (oldResidualPart N old born i).zeroLocus)
      (F := remainingBoundary old born i) (R := T) hUses e
    rw [← hCarrier,← hBoundary] at hT' hEq' hUse'
    exact ⟨.lower (native_geometry_rebase g' e) hEmpty' j hT' hEq',hUse'⟩

/-- Restrict the original physical event and its actual certificates. -/
def RetainedPreparationEvent.restrictOpen (E : RetainedPreparationEvent hn N old born T phase)
    (g : NativeRetainedGeometry N old born) (O : Opens X) :
    let f := (Subtype.val : O → X)
    RetainedPreparationEvent hn (f ⁻¹' N) (old.map (f ⁻¹' ·)) (born.map (f ⁻¹' ·))
      (restrict O T) phase :=
  (E.restrictOpenWithLower unrestrictedLowerHistoryActions E.usesLowerHistory_unrestricted g O).val

/-- Rebase the original physical event and its actual certificates. -/
def RetainedPreparationEvent.rebase (E : RetainedPreparationEvent hn N old born T phase)
    (g : NativeRetainedGeometry N old born)
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    RetainedPreparationEvent hn (e ⁻¹' N) (old.map (e ⁻¹' ·)) (born.map (e ⁻¹' ·))
      (transport e T).tower phase :=
  (E.rebaseWithLower unrestrictedLowerHistoryActions E.usesLowerHistory_unrestricted g e).val

end
end Hironaka.HironakaG4RetainedPreparationEvent
