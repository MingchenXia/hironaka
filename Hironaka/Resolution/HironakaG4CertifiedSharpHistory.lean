import Hironaka.Resolution.HironakaG4CompactRelativeSharpDimension
import Hironaka.Resolution.HironakaG4OrderedMaskStrictEquivariance
import Hironaka.Resolution.HironakaG4SharpTerminalOpen
import Hironaka.Resolution.HironakaG4ProcessedMaskIncidenceOrder

/-! Actual recursive sharp histories with paired preparation and monomial phases. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4CertifiedSharpHistory
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdealTowerTransport NormalCrossings NormalCrossingsInvariance
  HironakaG4SharpTerminalAtlas HironakaG4OrderedRetainedDefectTrace
  HironakaG4RetainedPreparationTrace HironakaG4RetainedPreparationLowerHistory
  HironakaG4RetainedEquivariantRowService HironakaG4CompactRelativeSharpDimension
  HironakaG4OrderedProcessedMaskHistory HironakaG4RelativeOrderedProcessedFinish
  HironakaG4OrderedMaskStrictEquivariance HironakaG34MaskFoldEquivariance
  HironakaActualProcessedAllMasksDrop HironakaG4SharpTerminalOpen HironakaG4ProcessedMaskIncidenceOrder

/-- A certified history in carrier dimension zero starts from the actual
empty tower. Source restrictions and rebases are recorded explicitly. -/
inductive SharpHistoryZero (n : ℕ) : SharpHistoryPredicate.{u} n
  | refl (X : CMfd.{u} n) (W : Set X) (E : List (Set X)) :
      SharpHistoryZero n W E (.refl : BlowupTower X X)
  | restrictOpen {X Y : CMfd.{u} n} {W : Set X} {E : List (Set X)} {T : BlowupTower X Y}
      (O : Opens X) (h : SharpHistoryZero n W E T) :
      SharpHistoryZero n ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·)) (restrict O T)
  | rebase {X X' Y : CMfd.{u} n} {W : Set X} {E : List (Set X)} {T : BlowupTower X Y}
      (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (h : SharpHistoryZero n W E T) :
      SharpHistoryZero n (φ ⁻¹' W) (E.map (φ ⁻¹' ·)) (transport φ T).tower

/-- The complete successor retains both physical blocks and the literal
source restriction at the transition. Every lower terminal leaf carries
a chosen history from the preceding dimension. -/
inductive SharpHistoryStep {n : ℕ} (hn : 0 < n)
    (lower : ∀ (A B : CMfd.{u} n),Set A → List (Set A) → BlowupTower A B → Prop) :
    SharpHistoryPredicate.{u} n
  | finished {X Y Z : CMfd.{u} n} {W : Set X} {E : List (Set X)}
      (geometry : NativeRetainedGeometry W E []) (T : BlowupTower X Y)
      (prepared : At W E E.length T) (equivariant : IsEquivariant W E T)
      (preparation : RetainedPreparationTrace hn W E [] (originalRetainedPreparationPhases E.length) T)
      (lower_histories : usesLowerHistory (fun {A B} => lower A B) preparation)
      (O : Opens X) (S : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z)
      (masks :
        let v := (Subtype.val : O → X)
        let EO := E.map (v ⁻¹' ·)
        let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
        OrderedProcessedMaskHistory hn (v ⁻¹' W) EO (restrict O T) (fun P => P.map e.toEmbedding)
          S (descendingMaskLabels (orderedMaskLevel E.length) E.length).reverse)
      (terminal :
        let v := (Subtype.val : O → X)
        IsSharpTerminalTower (v ⁻¹' W) (E.map (v ⁻¹' ·)) ((restrict O T).append S)) :
      SharpHistoryStep hn lower ((Subtype.val : O → X) ⁻¹' W)
        (E.map ((Subtype.val : O → X) ⁻¹' ·)) ((restrict O T).append S)
  | restrictOpen {X Y : CMfd.{u} n} {W : Set X} {E : List (Set X)} {T : BlowupTower X Y}
      (O : Opens X) (h : SharpHistoryStep hn lower W E T) :
      SharpHistoryStep hn lower ((Subtype.val : O → X) ⁻¹' W)
        (E.map ((Subtype.val : O → X) ⁻¹' ·)) (restrict O T)
  | rebase {X X' Y : CMfd.{u} n} {W : Set X} {E : List (Set X)} {T : BlowupTower X Y}
      (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
      (h : SharpHistoryStep hn lower W E T) :
      SharpHistoryStep hn lower (φ ⁻¹' W) (E.map (φ ⁻¹' ·)) (transport φ T).tower

variable {n : ℕ} {X Y : CMfd.{u} n}

private def sharpHistoryWith (raw : SharpHistoryPredicate.{u} n) : SharpHistoryPredicate.{u} n :=
  fun {_ _} W E T => IsClosedSubmanifold n W ∧ IsSharpTerminalTower W E T ∧ raw W E T

/-- Recursive sharp histories on the actual tower, indexed by a bound on
the local carrier dimension. -/
def SharpHistory (hn : 0 < n) : ℕ → SharpHistoryPredicate.{u} n
  | 0 => sharpHistoryWith (@SharpHistoryZero n)
  | d + 1 => sharpHistoryWith (@SharpHistoryStep n hn (fun A B W E T =>
      SharpHistory hn d (X := A) (Y := B) W E T))

theorem sharpHistory_carrier {hn : 0 < n} {d : ℕ} {W : Set X} {E : List (Set X)} {T : BlowupTower X Y}
    (h : SharpHistory hn d W E T) : IsClosedSubmanifold n W := by
  cases d <;> exact h.1

/-- A certified chart is terminal for its literal source carrier and boundary. -/
theorem sharpHistory_terminal {hn : 0 < n} {d : ℕ} {W : Set X} {E : List (Set X)} {T : BlowupTower X Y}
    (h : SharpHistory hn d W E T) : IsSharpTerminalTower W E T := by
  cases d <;> exact h.2.1

/-- Read the physically empty certificate in carrier dimension zero. -/
theorem sharpHistory_zero {hn : 0 < n} {W : Set X} {E : List (Set X)} {T : BlowupTower X Y}
    (h : SharpHistory hn 0 W E T) : SharpHistoryZero n W E T := h.2.2

/-- Read the two prepared and processed blocks in a successor certificate. -/
theorem sharpHistory_succ {hn : 0 < n} {d : ℕ} {W : Set X} {E : List (Set X)} {T : BlowupTower X Y}
    (h : SharpHistory hn (d+1) W E T) : SharpHistoryStep hn (fun A B N I R =>
      SharpHistory hn d (X := A) (Y := B) N I R) W E T := h.2.2

/-- Literal restriction retains the same certified history. -/
theorem sharpHistory_restrict {hn : 0 < n} {d : ℕ} {W : Set X} {E : List (Set X)} {T : BlowupTower X Y}
    (h : SharpHistory hn d W E T) (O : Opens X) :
    SharpHistory hn d ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·)) (restrict O T) := by
  have hW := sharpHistory_carrier h
  have hC := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW O
  have hTerm := sharpTerminal_restrict hW O T (sharpHistory_terminal h)
  cases d with
  | zero => exact ⟨hC,hTerm,SharpHistoryZero.restrictOpen O h.2.2⟩
  | succ d => exact ⟨hC,hTerm,SharpHistoryStep.restrictOpen O h.2.2⟩

/-- An actual source biholomorphism preserves the recursive certificate. -/
theorem sharpHistory_rebase (hn : 0 < n) (d : ℕ) : SharpHistoryRebase (SharpHistory.{u} hn d) := by
  intro A B C W E φ T h
  have hC := (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff φ).mpr (sharpHistory_carrier h)
  have hTerm := sharpTerminal_rebase φ W E T (sharpHistory_terminal h)
  cases d with
  | zero => exact ⟨hC,hTerm,SharpHistoryZero.rebase φ h.2.2⟩
  | succ d => exact ⟨hC,hTerm,SharpHistoryStep.rebase φ h.2.2⟩

set_option maxHeartbeats 550000 in
/-- The exact processed finish appends its ordered mask tape to the
certified prepared prefix on the same actual tower. -/
theorem sharpHistory_processed_finish (hn : 0 < n) (d : ℕ) :
    CompactRelativeEquivariantProcessedFinishUsing hn (SharpHistory.{u} hn d) (SharpHistory hn (d+1)) := by
  intro A B W E hW hE hDense T hAt hEq prep lower K hK
  let F := orderedMaskLevel E.length
  let mask := id (α := Finset (Fin E.length))
  have hCover : ∀ j, ((F j).map mask).toFinset = (Finset.univ : Finset (Fin E.length)).powersetCard j := by
    intro j
    simpa only [F,mask,List.map_id] using orderedMaskLevel_toFinset E.length j
  obtain ⟨O,hKO,Z,S,hMasks,hTerminal,hEquivariant⟩ :=
    exists_equivariant_ordered_processed_finish_near hn hW hE hDense T E.length hAt F mask hCover K hK
  have g : NativeRetainedGeometry W E [] :=
    ⟨hW,by simpa using hE,isTransverse_nil_of_isClosedSubmanifold hW,by simpa using hDense⟩
  exact ⟨O,hKO,Z,(restrict O T).append S,hTerminal,hEquivariant hEq,
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW O,hTerminal,
    SharpHistoryStep.finished g T hAt hEq prep lower O S hMasks hTerminal⟩

/-- Every compact enclosure admits a certified actual sharp history
in any specified local dimension bound. -/
theorem compactRelativeCertifiedSharpCleanupsExist (hn : 0 < n) (d : ℕ) :
    CompactRelativeEquivariantSharpCleanupsExistUsing (SharpHistory.{u} hn d) d :=
  compactRelativeEquivariantSharpCleanupsExist_using hn (SharpHistory hn)
    (fun A W E hW hT => ⟨hW,hT,SharpHistoryZero.refl A W E⟩) (sharpHistory_rebase hn)
    (sharpHistory_processed_finish hn) d

end
end Hironaka.HironakaG4CertifiedSharpHistory
