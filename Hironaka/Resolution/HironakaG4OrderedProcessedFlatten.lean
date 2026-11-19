import Hironaka.Resolution.HironakaG4OrderedSharpTerminalTransport

/-! Flatten a nested literal base open without changing the chronological
row masks of the actual continuation. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4OrderedProcessedFlatten

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings NormalCrossingsInvariance
  HironakaG34NonPureLowDim HironakaG4SharpTerminalAtlas MaxLocusLocal
  HironakaG4OrderedProcessedMaskRebase HironakaG4OrderedProcessedMaskHistory
  HironakaG4OrderedSharpTerminalTransport

variable {n : ℕ} {X Y : CMfd.{u} n} {ι : Type v}

set_option maxHeartbeats 650000 in
/-- The ordered terminal continuation over a nested restriction becomes an
actual ordered terminal continuation over the literal original open. -/
theorem ordered_processed_flatten (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (mask : ι → Finset (Fin E.length)) (L : List ι)
    {O V : Opens X} (hVO : V ≤ O) :
    let J := nestedOpens O V
    let v := (Subtype.val : O → X)
    let j := (Subtype.val : J → O)
    let WO := v ⁻¹' W
    let EO := E.map (v ⁻¹' ·)
    let WJ := j ⁻¹' WO
    let EJ := EO.map (j ⁻¹' ·)
    let e : Fin E.length ≃ Fin EJ.length := finCongr (by simp [EJ,EO])
    let T₀ := restrict J (restrict O T)
    ∀ {A : CMfd.{u} n} (Q : BlowupTower (CMfd.of (n := n) (openPreimage (restrict O T) J)) A),
      OrderedProcessedMaskHistory hn WJ EJ T₀ (fun a => (mask a).map e.toEmbedding) Q L →
      IsSharpTerminalTower WJ EJ (T₀.append Q) →
      let w := (Subtype.val : V → X)
      let WV := w ⁻¹' W
      let EV := E.map (w ⁻¹' ·)
      let eV : Fin E.length ≃ Fin EV.length := finCongr (List.length_map _).symm
      ∃ (B : CMfd.{u} n) (R : BlowupTower (CMfd.of (n := n) (openPreimage T V)) B),
        OrderedProcessedMaskHistory hn WV EV (restrict V T) (fun a => (mask a).map eV.toEmbedding) R L ∧
        IsSharpTerminalTower WV EV ((restrict V T).append R) := by
  intro J v j WO EO WJ EJ e T₀ A Q hQ hEnd w WV EV eV
  let φ := (nestedOpensDiffeo (n := n) hVO).symm
  have hT := (isTowerIso_restrict_nestedOpens hVO T).symm
  have hWO : IsClosedSubmanifold n WO := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW O
  have hEO : IsSNCDivisor n EO := isSNCDivisor_map_preimage
    (pullsBackCoordinates_val (n := n) O) continuous_subtype_val hE
  have hWJ : IsClosedSubmanifold n WJ := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hWO J
  have hEJ : IsSNCDivisor n EJ := isSNCDivisor_map_preimage
    (pullsBackCoordinates_val (n := n) J) continuous_subtype_val hEO
  have hDenseO : WO ⊆ closure (WO \ ⋃ H ∈ EO,H) := open_full_density hdense O
  have hDenseJ : WJ ⊆ closure (WJ \ ⋃ H ∈ EJ,H) :=
    open_full_density (X := CMfd.of (n := n) O) hDenseO J
  let PJ := fun a => (mask a).map e.toEmbedding
  obtain ⟨B,R,χ,hIso,hTape⟩ := ordered_processed_rebase hn hWJ hEJ hDenseJ T₀ (restrict V T)
    hT PJ L Q hEnd.carrierTest hEnd.boundaryTest hQ
  let eφ : Fin EJ.length ≃ Fin (EJ.map (φ ⁻¹' ·)).length := finCongr (List.length_map _).symm
  have hList : EJ.map (φ ⁻¹' ·) = EV := by
    unfold EJ EO EV
    rw [List.map_map,List.map_map]
    rfl
  have hCarrier : φ ⁻¹' WJ = WV := rfl
  rw [hCarrier] at hTape
  have hTapeV := ordered_processed_change_boundary hn WV hList (restrict V T) R L
    (fun a => (PJ a).map eφ.toEmbedding) hTape
  have hLabel (a : ι) : ((PJ a).map eφ.toEmbedding).map
      (finCongr (congrArg List.length hList)).toEmbedding = (mask a).map eV.toEmbedding := by
    unfold PJ
    rw [Finset.map_map,Finset.map_map]
    congr 1
  simp only [hLabel] at hTapeV
  have hEndV := sharp_terminal_of_isTowerIso hWJ hIso hEnd
  rw [hCarrier,hList] at hEndV
  exact ⟨B,R,hTapeV,hEndV⟩

end
end Hironaka.HironakaG4OrderedProcessedFlatten
