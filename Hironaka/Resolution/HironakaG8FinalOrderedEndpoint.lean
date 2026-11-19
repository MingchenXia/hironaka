import Hironaka.Resolution.HironakaG8CorrectedOrderedEndpoint
import Hironaka.Resolution.HironakaG8LocallyFinitePhysicalCharts

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8FinalOrderedEndpoint
noncomputable section

open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass
  HironakaG8NoncompactInitialBoundaryAtlas HironakaG8NoncompactInitialBoundaryMembers
  HironakaG8InitialBoundaryAtlasMarkOne HironakaG8SurfaceLimitEndpoint
  HironakaEmbeddedAnalytic HironakaResolutionSpaceLocal NormalCrossings
  HironakaG3REmbeddedGlobalSNC HironakaG4SharpTerminalAtlas
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation

open HironakaG8LocallyFinitePhysicalCharts HironakaG8CorrectedOrderedEndpoint

/-- A proper embedded resolution carrying a locally finite cover by exact
finite histories. The original mark-one TEST and native HS epoch certificates
are read on the same charts, including the charts of the ordered SNC exhaustion. -/
theorem exists_locally_finite_ordered_boundary_epoch_canonical
    {m : ℕ} {X : CMfd.{0} (m+1)} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := m+1) W) {E : List (Set X)}
    (hE : IsSNCDivisor (m+1) E) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B)) :
    ∃ (Z : CMfd.{0} (m+1)) (P : Z → X),
      IsGluedFrom (orderedInitialBoundaryClass W E) Z P ∧
      IsProperMap P ∧
      IsClosedSubmanifold (m+1) (strictTransform (m+1) P W) ∧
      IsIsomorphismOver (m+1) P (singularSet (n := m+1) W ∪ (W ∩ ⋃ B ∈ E, B))ᶜ ∧
      (∃ c : ℕ → TowerChart (orderedInitialBoundaryClass W E) Z P,
        (∀ x, ∃ k, x ∈ (c k).U) ∧ (∀ z, ∃ k, z ∈ (c k).V) ∧
        LocallyFinite (fun k => ((c k).U : Set X)) ∧
        LocallyFinite (fun k => ((c k).V : Set Z)) ∧
        (∀ k, ∃ K : Set X, IsCompact K ∧ ((c k).U : Set X) ⊆ K) ∧
        ∀ k, InitialBoundaryChartMarkOne (c k) ∧ InitialBoundaryChartEpochs (c k)) ∧
      ∃ Ex : SNCExhaustion Z,
        (∀ k, ∃ c : TowerChart (orderedInitialBoundaryClass W E) Z P,
          Ex.W k = c.V ∧ Ex.B k = fullChartBoundary c E ∧
          InitialBoundaryChartMarkOne c ∧ InitialBoundaryChartEpochs c) ∧
        let B : {D : Set Z // Ex.IsGlobalMember D} → Set Z := Subtype.val
        IsLocallyFiniteSNCDivisor (m+1) B ∧ (∀ j, (B j).Nonempty) ∧
        HasNormalCrossingsWithBoundary (strictTransform (m+1) P W) B := by
  obtain ⟨Z,P,hGlue,hSmooth,hIso,⟨c,hCoverU,hCoverV,hLFU,hLFV,hCompact,hTest⟩,
    Ex,hCharts,hMembers⟩ :=
    exists_locally_finite_initial_boundary_markOne_physical_cover hW hE hDense
  refine ⟨Z,P,hGlue,hGlue.2.1,hSmooth,hIso,
    ⟨c,hCoverU,hCoverV,hLFU,hLFV,hCompact,fun k =>
      ⟨hTest k,initial_boundary_chart_epochs (c k)⟩⟩,Ex,?_,hMembers⟩
  intro k
  obtain ⟨d,hV,hE'⟩ := hCharts k
  exact ⟨d,hV,hE',initial_boundary_chart_original_markOne hW hE hDense hGlue d,
    initial_boundary_chart_epochs d⟩

#print axioms exists_locally_finite_ordered_boundary_epoch_canonical

end
end Hironaka.HironakaG8FinalOrderedEndpoint
