import Hironaka.Resolution.HironakaG4OrderedPieceMerge
import Hironaka.Resolution.HironakaG3RestrictedAppendEmptyHead

/-! Carry out a fixed ordered disjoint merge and retain the comparison of
the whole merged tower on each isolating open. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
universe v

namespace Hironaka.HironakaG4OrderedPieceMergeConstruction

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  BlowupTowerIsoTail RestrictEmptyTower G3UniverseEmptyAwareCore
  HironakaG3CentresOverGenericFactor HironakaActualProcessedAllMasksDrop
  HironakaG4OrderedPieceMerge HironakaG3ClosedFootprintTransportedTower
  HironakaOriginalOldBranchEmptyProjection HironakaG3AppendEmptyTailComparison
  HironakaG3RestrictedAppendEmptyHead

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
/-- Perform the actual physical disjoint merge in the indicated order.
Each member of the list is compared with the full tower on its piece open. -/
theorem exists_ordered_piece_merge {n : ℕ} {X : CMfd.{0} n} {ι : Type v}
    (F : ι → Set X) (hF : ∀ i, IsClosed (F i)) (V : ι → Opens X)
    (hFV : ∀ i, F i ⊆ V i) (hDis : ∀ i j, i ≠ j → Disjoint (V i : Set X) (F j))
    (Y : ι → CMfd.{0} n) (S : ∀ i, BlowupTower X (Y i))
    (hS : ∀ i, CentresOver (F i) (S i)) (ls : List ι) (hls : ls.Nodup) :
    ∃ (Z : CMfd.{0} n) (T : BlowupTower X Z), OrderedPieceMerge F V Y S ls T ∧
      ∀ i ∈ ls, ∃ ψ : (CMfd.of (n := n) (openPreimage T (V i)))
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage (S i) (V i))),
        EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) (V i)) ∞)
          (restrict (V i) T) (restrict (V i) (S i)) ψ := by
  classical
  induction ls with
  | nil =>
    exact ⟨X, .refl, .nil, fun _ hi => (List.not_mem_nil hi).elim⟩
  | cons i ls ih =>
    have hi : i ∉ ls := (List.nodup_cons.mp hls).1
    obtain ⟨A, P, hP, hCompare⟩ := ih (List.nodup_cons.mp hls).2
    have hSep : Disjoint (V i : Set X) (⋃ j ∈ ls, F j) := by
      apply disjoint_left.mpr
      intro x hxF hxSupp
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxSupp
      have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
      exact disjoint_left.mp (hDis i j hij) hxF hxj
    have hEmpty := isEmptyTower_restrict_of_centresOver (V i) hSep P (orderedPieceMerge_centresOver hP)
    obtain ⟨β, hβ⟩ := exists_empty_tower_projection (restrict (V i) P) hEmpty
    let B := openPreimage P (V i)
    let K := P.proj ⁻¹' F i
    have hK : IsClosed K := (hF i).preimage P.contMDiff_proj.continuous
    have hKB : K ⊆ B := fun _ hz => hFV i hz
    have hPull : β.symm ⁻¹' ((Subtype.val : B → A) ⁻¹' K) = (Subtype.val : V i → X) ⁻¹' F i := by
      ext x
      change P.proj (β.symm x).val ∈ F i ↔ x.val ∈ F i
      rw [← proj_restrict (V i) P (β.symm x), ← hβ, β.apply_symm_apply]
    have hT : CentresOver (β.symm ⁻¹' ((Subtype.val : B → A) ⁻¹' K)) (restrict (V i) (S i)) := by
      rw [hPull]
      exact centresOver_restrict (V i) (F i) (S i) (hS i)
    obtain ⟨Z, Q, hQ, e, hIso⟩ :=
      extend_transported_closed_footprint_tower B K hK hKB β (restrict (V i) (S i)) hT
    let ψ := e.symm.trans (MarkedIdealTowerTransport.transport β (restrict (V i) (S i))).back
    have hPhase : PiecePhase (F i) (V i) (S i) P Q := ⟨hQ, β, hβ, ψ, hIso⟩
    refine ⟨Z, P.append Q, .snoc hP hPhase (IsTowerIso.refl_self _), ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with hji | hj
    · subst j
      exact restricted_append_comparison_of_empty_head P Q (V i) (restrict (V i) (S i)) hEmpty β hβ ψ hIso
    · have hji : j ≠ i := fun h => hi (h ▸ hj)
      obtain ⟨η, hη⟩ := restricted_append_comparison_off_tail_support P Q (F i) hQ (V j) (hDis j i hji)
      obtain ⟨χ, hχ⟩ := hCompare j hj
      exact ⟨η.trans χ, by simpa only [Diffeomorph.refl_trans] using G3UniverseEmptyAwareCore.trans hη hχ⟩

end
end Hironaka.HironakaG4OrderedPieceMergeConstruction
