import Hironaka.Resolution.HironakaG4CertifiedSharpSourceView
import Hironaka.Resolution.HironakaG4OrderedProcessedMaskRestriction
import Hironaka.Resolution.HironakaG4OrderedSharpTerminalTransport
import Hironaka.Resolution.HironakaG4SharpTerminalOpen

/-! Separate the actual prepared prefix and ordered monomial suffix on a literal open. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4CertifiedSharpFinishedRestriction
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  HironakaG4CertifiedSharpSourceView
  HironakaG4RetainedPreparationTrace HironakaG4RetainedPreparationLowerHistory
  HironakaG4CompactRelativeSharpDimension HironakaG4OrderedRetainedDefectTrace
  HironakaG4RelativeOrderedProcessedFinish HironakaG4ProcessedMaskIncidenceOrder
  HironakaG4OrderedProcessedMaskHistory HironakaG4OrderedProcessedMaskRestriction
  HironakaG4OrderedSharpTerminalTransport HironakaG4SharpTerminalOpen HironakaG4SharpTerminalAtlas

variable {n : ℕ} {hn : 0 < n} {lower : SharpHistoryPredicate.{u} n}

abbrev restrictedPreparedPrefix (R : FinishedSharpHistory hn lower) (U : Opens R.chart) :=
  restrict U (restrict R.window R.headTower)

/-- One literal view of the two raw blocks, carrying all original mask and
lower choices on the actual flattened phase factorization. -/
structure FinishedSharpBlocks (R : FinishedSharpHistory hn lower) (U : Opens R.chart) where
  endpoint : CMfd.{u} n
  suffix : BlowupTower (CMfd.of (n := n) (openPreimage (restrict R.window R.headTower) U)) endpoint
  presentation : endpoint ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
    CMfd.of (n := n) (openPreimage R.tower U)
  physical : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
    ((restrictedPreparedPrefix R U).append suffix) (restrict U R.tower) presentation
  geometry : NativeRetainedGeometry (X := CMfd.of (n := n) U) (R.carrierOn U) (R.boundaryOn U) []
  preparation : RetainedPreparationTrace hn (R.carrierOn U) (R.boundaryOn U) []
    (originalRetainedPreparationPhases (R.boundaryOn U).length) (restrictedPreparedPrefix R U)
  lower_histories : usesLowerHistory lower preparation
  masks : OrderedProcessedMaskHistory hn (R.carrierOn U) (R.boundaryOn U) (restrictedPreparedPrefix R U)
    id suffix (descendingMaskLabels (orderedMaskLevel (R.boundaryOn U).length) (R.boundaryOn U).length).reverse
  terminal : IsSharpTerminalTower (R.carrierOn U) (R.boundaryOn U) ((restrictedPreparedPrefix R U).append suffix)

private theorem ordered_mask_history_of_length_cast {A B C : CMfd.{u} n} {W : Set A}
    {E : List (Set A)} {r : ℕ} (hLen : r = E.length)
    (T : BlowupTower A B) (S : BlowupTower B C)
    (h : OrderedProcessedMaskHistory hn W E T (fun P : Finset (Fin r) => P.map (finCongr hLen).toEmbedding)
      S (descendingMaskLabels (orderedMaskLevel r) r).reverse) :
    OrderedProcessedMaskHistory hn W E T id S (descendingMaskLabels (orderedMaskLevel E.length) E.length).reverse := by
  subst r
  have hMap : (fun P : Finset (Fin E.length) => P.map (finCongr rfl).toEmbedding) = id := by
    funext P
    simp
  rwa [hMap] at h

set_option maxHeartbeats 850000 in
/-- Literal restriction retains the certified preparation and the exact
incidence-ordered Γ history on one actual appended factorization. -/
theorem finished_sharp_blocks_restrict (R : FinishedSharpHistory hn lower) (U : Opens R.chart) :
    Nonempty (FinishedSharpBlocks R U) := by
  let v := (Subtype.val : R.window → R.base)
  let u := (Subtype.val : U → R.chart)
  let W := v ⁻¹' R.carrier
  let E := R.boundary.map (v ⁻¹' ·)
  let WO := R.carrierOn U
  let EO := R.boundaryOn U
  let T := restrict R.window R.headTower
  let e₁ : Fin R.boundary.length ≃ Fin E.length := finCongr (List.length_map _).symm
  let e₂ : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
  have hLen : R.boundary.length = EO.length := by simp [EO]
  have g : NativeRetainedGeometry (X := R.chart) W E [] := R.geometry.restrict R.window
  let L := (descendingMaskLabels (orderedMaskLevel R.boundary.length) R.boundary.length).reverse
  obtain ⟨Z,S,χ,hIso,hMasks⟩ := ordered_processed_restrict hn (W := W) (E := E) g.carrier
    (by simpa only [List.append_nil] using g.full) (by simpa only [List.append_nil] using g.dense) T (fun P => P.map e₁.toEmbedding) U L R.suffix
    R.terminal.carrierTest R.terminal.boundaryTest R.masks
  let P := restrictedPreparedPrefix R U
  have hMasks' : OrderedProcessedMaskHistory hn WO EO P
      (fun A : Finset (Fin R.boundary.length) => (A.map e₁.toEmbedding).map e₂.toEmbedding) S L := hMasks
  have hMap : (fun A : Finset (Fin R.boundary.length) => (A.map e₁.toEmbedding).map e₂.toEmbedding) =
      (fun A : Finset (Fin R.boundary.length) => A.map (finCongr hLen).toEmbedding) := by
    funext A
    rw [Finset.map_map]
    congr 1
  rw [hMap] at hMasks'
  have hEnd := sharpTerminal_restrict g.carrier U R.tower R.terminal
  have gO : NativeRetainedGeometry (X := CMfd.of (n := n) U) WO EO [] := g.restrict U
  have hTerminal := sharp_terminal_of_isTowerIso gO.carrier hIso hEnd
  change IsSharpTerminalTower WO (EO.map id) (P.append S) at hTerminal
  rw [List.map_id] at hTerminal
  have hPrep : ∃ R₁ : RetainedPreparationTrace hn WO EO []
      (originalRetainedPreparationPhases R.boundary.length) P, usesLowerHistory lower R₁ := by
    refine ⟨(R.preparation.restrictOpen R.window R.geometry).restrictOpen U g,?_⟩
    change usesLowerHistory lower R.preparation
    exact R.lower_histories
  rw [hLen] at hPrep
  obtain ⟨R₁,hLower⟩ := hPrep
  exact ⟨⟨Z,S,χ,hIso,gO,R₁,hLower,ordered_mask_history_of_length_cast hLen P S hMasks',hTerminal⟩⟩

end
end Hironaka.HironakaG4CertifiedSharpFinishedRestriction
