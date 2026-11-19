import Hironaka.Resolution.HironakaG4RelativeOrderedProcessedFinish
import Hironaka.Resolution.HironakaG4StrictRelativeMaskEquivariance

/-! The same actual ordered processed continuation inherits strict local
equivariance from its initial prefix. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4OrderedMaskStrictEquivariance

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings HironakaSharpActualFiniteChronologicalHistory
  HironakaG34MaskFoldEquivariance HironakaG4OrderedProcessedMaskHistory
  HironakaG4StrictRelativeMaskEquivariance HironakaG4RelativeOrderedProcessedFinish
  HironakaG4RetainedDefectTraceEquivariance HironakaG4SharpTerminalAtlas
  HironakaActualProcessedAllMasksDrop HironakaG34NonPureLowDim NormalCrossingsInvariance

variable {n : ℕ} {X Y : CMfd.{u} n} {ι : Type v}

/-- Every phase of the actual ordered continuation extends strict
equivariance, without altering any physical stage of the given tower. -/
theorem ordered_processed_isEquivariant (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hEq : IsEquivariant W E T) (mask : ι → Finset (Fin E.length)) :
    ∀ (L : List ι) {Z : CMfd.{u} n} (Q : BlowupTower Y Z),
      IsGeoTestTower (geometricTemplate W []) (T.append Q) →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) →
      OrderedProcessedMaskHistory hn W E T mask Q L →
      IsEquivariant W E (T.append Q) := by
  intro L
  induction L with
  | nil =>
    intro Z Q _hQTest _hQFull hQ
    cases hQ
    exact hEq
  | cons label L ih =>
    intro Z Q hQTest hQFull hQ
    cases hQ with
    | snoc _ S hPrev hBlock =>
      rw [←BlowupTower.append_assoc] at hQTest hQFull
      have hPrevTest := ((isGeoTestTower_append_iff _ _ S).mp hQTest).1
      have hPrevFull := ((isGeoTestTower_append_iff _ _ S).mp hQFull).1
      have hEqPrev := ih _ hPrevTest hPrevFull hPrev
      simpa only [BlowupTower.append_assoc] using
        isEquivariant_append_processed_mask hn hW hE hdense _ hPrevTest hPrevFull hEqPrev
          (mask label) S hBlock.1 hBlock.2.1

/-- The fixed ordered compact-relative finish preserves strict local
equivariance of the same actual appended tower, whenever the prefix has it. -/
theorem exists_equivariant_ordered_processed_finish_near (hn : 0 < n)
    {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (q : ℕ) (hAt : At W E q T)
    [DecidableEq ι] (F : ℕ → List ι) (mask : ι → Finset (Fin E.length))
    (hCover : ∀ j,((F j).map mask).toFinset = (Finset.univ : Finset (Fin E.length)).powersetCard j)
    (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X,K ⊆ O ∧
      ∃ (Z : CMfd.{u} n) (S : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z),
        let v := (Subtype.val : O → X)
        let WO := v ⁻¹' W
        let EO := E.map (v ⁻¹' ·)
        let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
        let U := restrict O T
        OrderedProcessedMaskHistory hn WO EO U (fun a => (mask a).map e.toEmbedding)
          S (descendingMaskLabels F q).reverse ∧
        IsSharpTerminalTower WO EO (U.append S) ∧
        (IsEquivariant W E T → IsEquivariant WO EO (U.append S)) := by
  obtain ⟨O,hKO,Z,S,hTape,hEnd⟩ :=
    exists_ordered_processed_finish_near hn F q hW hE hdense T hAt mask hCover K hK
  let v := (Subtype.val : O → X)
  let WO := v ⁻¹' W
  let EO := E.map (v ⁻¹' ·)
  let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
  let U := restrict O T
  have hWO : IsClosedSubmanifold n WO :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW O
  have hEO : IsSNCDivisor n EO := isSNCDivisor_map_preimage
    (pullsBackCoordinates_val (n := n) O) continuous_subtype_val hE
  have hDenseO : WO ⊆ closure (WO \ ⋃ H ∈ EO,H) := open_full_density hdense O
  refine ⟨O,hKO,Z,S,hTape,hEnd,fun hEq => ?_⟩
  exact ordered_processed_isEquivariant hn hWO hEO hDenseO U (isEquivariant_restrictOpen hEq O)
    (fun a => (mask a).map e.toEmbedding) _ S hEnd.carrierTest hEnd.boundaryTest hTape

/-- A fully processed actual prefix with strict local equivariance admits
a strict sharp finish on a literal neighbourhood of any compact set. -/
theorem exists_equivariant_processed_finish_near (hn : 0 < n)
    {W : Set X} {E : List (Set X)} {q : ℕ}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hAt : At W E q T) (hEq : IsEquivariant W E T)
    (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X,K ⊆ O ∧
      ∃ (Z : CMfd.{u} n) (S : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z),
        let v := (Subtype.val : O → X)
        let WO := v ⁻¹' W
        let EO := E.map (v ⁻¹' ·)
        let U := (restrict O T).append S
        IsSharpTerminalTower WO EO U ∧ IsEquivariant WO EO U := by
  classical
  let F := fun j => ((Finset.univ : Finset (Fin E.length)).powersetCard j).toList
  have hCover (j : ℕ) : ((F j).map id).toFinset = (Finset.univ : Finset (Fin E.length)).powersetCard j := by
    simp [F]
  obtain ⟨O,hKO,Z,S,_hTape,hEnd,hEquiv⟩ :=
    exists_equivariant_ordered_processed_finish_near hn hW hE hdense T q hAt F id hCover K hK
  exact ⟨O,hKO,Z,S,hEnd,hEquiv hEq⟩

end
end Hironaka.HironakaG4OrderedMaskStrictEquivariance
