import Hironaka.Resolution.HironakaG4CertifiedSharpSourceView
import Hironaka.Resolution.HironakaG4CertifiedSharpZeroComparison
import Hironaka.Resolution.HironakaG4RetainedPreparationComparison

/-! Reduce the recursive actual sharp comparison to the two completed blocks. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4CertifiedSharpOuterComparison
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdealTowerTransport
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareBornSlots
  HironakaG4CertifiedSharpHistory HironakaG4CertifiedSharpSourceView
  HironakaG4CertifiedSharpZeroComparison HironakaG4RetainedPreparationLowerHistory
  HironakaG4RetainedPreparationComparison HironakaG4RetainedTraceComparison

variable {n : ℕ} {hn : 0 < n} {lower : SharpHistoryPredicate.{u} n}

/-- The successor comparison needs only the two finished roots restricted
to arbitrary literal opens. The supplied source map matches the carrier
and the ordered nonempty original boundary positions. -/
def FinishedSharpOverlapCompatible (hn : 0 < n) (lower : SharpHistoryPredicate.{u} n) : Prop :=
  ∀ (R' R : FinishedSharpHistory hn lower) (U' : Opens R'.chart) (U : Opens R.chart)
    (φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U),
    R'.carrierOn U' = φ ⁻¹' R.carrierOn U →
    liveBorn (R'.boundaryOn U') = (liveBorn (R.boundaryOn U)).map (φ ⁻¹' ·) →
    ∃ χ : CMfd.of (n := n) (openPreimage R'.tower U')
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R.tower U),
      EmptyAwareTowerIso φ (restrict U' R'.tower) (restrict U R.tower) χ

set_option maxHeartbeats 600000 in
/-- Actual outer restrictions and rebases are absorbed by literal
source views and the same supplied whole-chart comparison. -/
theorem sharpHistoryStep_overlap_of_finished (hCompare : FinishedSharpOverlapCompatible hn lower) :
    LowerHistoryOverlapCompatible
      (fun {X Y} W E T => SharpHistoryStep hn (fun A B N I S => lower (X := A) (Y := B) N I S)
        (X := X) (Y := Y) W E T) := by
  intro X X' Y Y' φ W W' E E' T T' _hW _hE _hDense _hW' _hE' _hDense' hW hE hT hT'
  obtain ⟨R,U,e,η,hIso,hN,hB⟩ := exists_finished_sharp_source_view (lower := lower) hT
  obtain ⟨R',U',e',η',hIso',hN',hB'⟩ := exists_finished_sharp_source_view (lower := lower) hT'
  let ψ := e'.symm.trans (φ.trans e)
  have hCarrier : R'.carrierOn U' = ψ ⁻¹' R.carrierOn U := by
    change W = e ⁻¹' R.carrierOn U at hN
    change W' = e' ⁻¹' R'.carrierOn U' at hN'
    rw [hN,hN'] at hW
    have h := congrArg (fun S => e'.symm ⁻¹' S) hW
    rw [symm_preimage_preimage e'] at h
    exact h
  have hBoundary : liveBorn (R'.boundaryOn U') = (liveBorn (R.boundaryOn U)).map (ψ ⁻¹' ·) := by
    have hL : E = (R.boundaryOn U).map (e ⁻¹' ·) := by
      rw [hB]
      simp only [FinishedSharpHistory.boundaryOn,List.map_map]
      exact List.map_congr_left (fun _ _ => rfl)
    have hR : E' = (R'.boundaryOn U').map (e' ⁻¹' ·) := by
      rw [hB']
      simp only [FinishedSharpHistory.boundaryOn,List.map_map]
      exact List.map_congr_left (fun _ _ => rfl)
    rw [hL,hR] at hE
    unfold liveBorn at hE
    rw [filter_map_bijection e' e'.surjective,filter_map_bijection e e.surjective] at hE
    have h := congrArg (List.map (e'.symm ⁻¹' ·)) hE
    rw [map_symm_preimage_map_preimage e'] at h
    change liveBorn (R'.boundaryOn U') =
      (((liveBorn (R.boundaryOn U)).map (e ⁻¹' ·)).map (φ ⁻¹' ·)).map (e'.symm ⁻¹' ·) at h
    refine h.trans ?_
    simp only [List.map_map]
    exact List.map_congr_left (fun _ _ => rfl)
  obtain ⟨κ,hκ⟩ := hCompare R' R U' U ψ hCarrier hBoundary
  have h := G3UniverseEmptyAwareCore.trans
    (G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso hIso') hκ)
    (emptyAware_of_isTowerIso hIso.symm)
  have hφ : (e'.trans ψ).trans e.symm = φ := by
    ext x
    change e.symm (e (φ (e'.symm (e' x)))) = φ x
    rw [e.symm_apply_apply,e'.symm_apply_apply]
  rw [hφ] at h
  exact ⟨_,h⟩

/-- Once two completed blocks compare using the lower-dimensional
comparison, the actual whole histories compare in every dimension. -/
theorem sharpHistory_overlap_of_finished (hn : 0 < n)
    (hFinished : ∀ d, LowerHistoryOverlapCompatible (SharpHistory.{u} hn d) →
      FinishedSharpOverlapCompatible.{u} hn (SharpHistory.{u} hn d))
    (d : ℕ) : LowerHistoryOverlapCompatible (SharpHistory.{u} hn d) := by
  induction d with
  | zero =>
    intro X X' Y Y' φ W W' E E' T T' _ _ _ _ _ _ _ _ hT hT'
    exact sharpHistory_zero_compare φ hT' hT
  | succ d ih =>
    intro X X' Y Y' φ W W' E E' T T' hW hE hD hW' hE' hD' hC hB hT hT'
    exact sharpHistoryStep_overlap_of_finished (hFinished d ih) φ hW hE hD hW' hE' hD' hC hB
      (sharpHistory_succ hT) (sharpHistory_succ hT')

end
end Hironaka.HironakaG4CertifiedSharpOuterComparison
