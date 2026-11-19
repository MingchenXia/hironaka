import Hironaka.Resolution.HironakaG4OrderedSharpTerminalTransport

/-! Join one retained canonical mask with the ordered finish on a smaller
literal base neighbourhood. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4OrderedProcessedHeadAppend

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaG34NonPureLowDim
  HironakaG4SharpTerminalAtlas HironakaG4OrderedSharpTerminalTransport
  HironakaG4OrderedProcessedMaskHistory HironakaG4OrderedProcessedMaskRestriction
  HironakaG4OrderedProcessedMaskRebase HironakaActualProcessedMaskControlledSum
  NormalCrossingsInvariance CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X Y Z A : CMfd.{u} n} {ι : Type v}

private abbrev ref (A : CMfd.{u} n) := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞

set_option maxHeartbeats 650000 in
/-- Prepend one canonical phase to the labelled actual finish available on a
smaller literal base. Both the earlier and later physical histories remain. -/
theorem ordered_processed_head_append (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (S : BlowupTower Y Z)
    (hT : IsGeoTestTower (geometricTemplate W []) (T.append S))
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append S))
    (mask : ι → Finset (Fin E.length)) (label : ι)
    (hS : let M := processedMaskMarked W E T (mask label)
      IsInvDomain (n+1) M ∧ IsCanonical M ((invFamily hn (n+1)).inv M) S ∧ IsGeoResolution M S)
    (J : Opens X) (Q : BlowupTower (CMfd.of (n := n) (openPreimage (T.append S) J)) A)
    (L : List ι) :
    let v := (Subtype.val : J → X)
    let WJ := v ⁻¹' W
    let EJ := E.map (v ⁻¹' ·)
    let e : Fin E.length ≃ Fin EJ.length := finCongr (List.length_map _).symm
    let maskJ := fun a => (mask a).map e.toEmbedding
    let P := restrict J (T.append S)
    OrderedProcessedMaskHistory hn WJ EJ P maskJ Q L →
    IsSharpTerminalTower WJ EJ (P.append Q) →
    ∃ (B : CMfd.{u} n) (R : BlowupTower (CMfd.of (n := n) (openPreimage T J)) B),
      OrderedProcessedMaskHistory hn WJ EJ (restrict J T) maskJ R (L ++ [label]) ∧
      IsSharpTerminalTower WJ EJ ((restrict J T).append R) := by
  intro v WJ EJ e maskJ P hQ hEnd
  have hHist : OrderedProcessedMaskHistory hn W E T mask S [label] := by
    have h := OrderedProcessedMaskHistory.snoc label S
      (OrderedProcessedMaskHistory.nil (hn := hn) (W := W) (E := E) (T := T) (mask := mask))
      (by simpa only [BlowupTower.append_refl] using hS)
    simpa only [BlowupTower.refl_append] using h
  obtain ⟨Z₀,S₀,χ,hχ,hS₀⟩ := ordered_processed_restrict hn hW hE hdense T mask J [label] S hT hFull hHist
  let T₀ := restrict J T
  let P₀ := T₀.append S₀
  have hWJ : IsClosedSubmanifold n WJ := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW J
  have hEJ : IsSNCDivisor n EJ :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val (n := n) J) continuous_subtype_val hE
  have hDenseJ : WJ ⊆ closure (WJ \ ⋃ H ∈ EJ,H) := open_full_density hdense J
  obtain ⟨B,Q₀,η,hη,hQ₀⟩ := ordered_processed_rebase hn hWJ hEJ hDenseJ P P₀ hχ
    maskJ L Q hEnd.carrierTest hEnd.boundaryTest hQ
  let ψ := ref (CMfd.of (n := n) J)
  have hEId : EJ.map (ψ ⁻¹' ·) = EJ := List.map_id EJ
  let eId : Fin EJ.length ≃ Fin (EJ.map (ψ ⁻¹' ·)).length := finCongr (List.length_map _).symm
  have hQJ := ordered_processed_change_boundary hn WJ hEId P₀ Q₀ L
    (fun a => (maskJ a).map eId.toEmbedding) hQ₀
  have hLabel (a : ι) : ((maskJ a).map eId.toEmbedding).map
      (finCongr (congrArg List.length hEId)).toEmbedding = maskJ a := by
    rw [Finset.map_map]
    have heId : eId.toEmbedding.trans (finCongr (congrArg List.length hEId)).toEmbedding =
        Function.Embedding.refl _ := by
      ext i
      rfl
    rw [heId,Finset.map_refl]
  simp only [hLabel] at hQJ
  have hEndJ := sharp_terminal_of_isTowerIso hWJ hη hEnd
  rw [hEId] at hEndJ
  refine ⟨B,S₀.append Q₀,ordered_processed_append hn T₀ S₀ maskJ [label] hS₀ Q₀ L hQJ,?_⟩
  rw [←BlowupTower.append_assoc]
  exact hEndJ

end
end Hironaka.HironakaG4OrderedProcessedHeadAppend
