import Hironaka.Resolution.HironakaG8PhysicalChartOccupiedLifts
import Hironaka.Resolution.HironakaG8CofinalEventLimit
import Hironaka.Resolution.HironakaG8CofinalPhysicalCharts
import Hironaka.Resolution.HironakaG8FinalOrderedEndpoint

/-! # The actual event system on a certified compact exhaustion -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8CertifiedCofinalEvents

open BlowupTowers HironakaG3RTowerClass G3UniversePhysicalClassComparisons
  HironakaG8CofinalOccupiedAncestry HironakaG8CofinalEventLimit
  HironakaG8PhysicalChartOccupiedLifts HironakaG8CofinalPhysicalCharts
  HironakaG8NoncompactInitialBoundaryAtlas HironakaG8LabelledEmbeddedAtlas
  HironakaG8LabelledEmbeddedTape HironakaG8OrderedSmoothSuffix
  HironakaG8InitialBoundaryAtlasMarkOne HironakaG8LocallyFinitePhysicalCharts
  HironakaG8CorrectedOrderedEndpoint HironakaG8LocalMixedSmoothCleanup
  HironakaEmbeddedAnalytic NormalCrossings

/-- A nested chain of actual charts in a physically compatible class
determines represented global events and their precedence. -/
theorem exists_events_of_nested_physical_charts {n : ℕ} {X Z : CMfd.{0} n}
    {K : LocalTowerClass X} {P : Z → X} (cmp : HasPhysicalComparisons K)
    (c : ℕ → TowerChart K Z P) (hMono : Monotone fun i => (c i).U) :
    ∃ (I : Type) (A : CofinalEvents c I),
      ∀ e, ∃ (i : ℕ) (p : Slots c i), A.event i p = e := by
  obtain ⟨up,hId,hComp,hStrict⟩ := exists_coherent_chart_occupied_lifts cmp c hMono
  exact ⟨_,eventLimit c up (up_comp := hComp) (up_id := hId) (up_mono := hStrict),
    eventLimit_occurs c up (up_comp := hComp) (up_id := hId) (up_mono := hStrict)⟩

/-- For the actual cofinal charts of the arbitrary ordered initial SNC
atlas, the physical comparisons supply the event system. The original
mark-one TEST and native Hilbert–Samuel epochs hold on the same charts.
An increasing natural rank is equivalent to finite incoming ancestry
in this actual system. -/
theorem exists_certified_initial_boundary_cofinal_events
    {m : ℕ} {X : CMfd.{0} (m+1)} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := m+1) W) {E : List (Set X)}
    (hE : IsSNCDivisor (m+1) E) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B)) :
    ∃ (Z : CMfd.{0} (m+1)) (P : Z → X),
      IsGluedFrom (orderedInitialBoundaryClass W E) Z P ∧
      ∃ c : ℕ → TowerChart (orderedInitialBoundaryClass W E) Z P,
        Monotone (fun i => (c i).U) ∧
        (∀ L : Set X, IsCompact L → ∃ i, L ⊆ ((c i).U : Set X)) ∧
        (∀ i, InitialBoundaryChartMarkOne (c i) ∧ InitialBoundaryChartEpochs (c i)) ∧
        ∃ (I : Type) (A : CofinalEvents c I),
          (∀ e, ∃ (i : ℕ) (p : Slots c i), A.event i p = e) ∧
          ((∃ rank : I → ℕ, ∀ ⦃a b⦄, A.Before a b → rank a < rank b) ↔
            ∀ b, {a | A.Before a b}.Finite) := by
  obtain ⟨Z,P,hGlued,c,hMono,-,-,hCover⟩ :=
    exists_ordered_initial_boundary_cofinal_physical_charts hW hE hDense
  have hC : SmoothTailHasComparisons (ascending_smooth_tail_certificate (m+1)) := by
    intro A A' Y Y' φ A₀ E E' T T' hB hT' hT
    exact ordered_smooth_suffix_emptyAware φ (ds := List.finRange (m+2)) hB hT' hT
  have hCmp := initial_boundary_class_physical (Nat.succ_pos m) hC hW hE hDense
  obtain ⟨I,A,hOccurs⟩ := exists_events_of_nested_physical_charts hCmp c hMono
  refine ⟨Z,P,hGlued,c,hMono,hCover,fun i => ?_,I,A,hOccurs,A.exists_rank_iff_finite_predecessors hOccurs⟩
  exact ⟨initial_boundary_chart_original_markOne hW hE hDense hGlued (c i),
    initial_boundary_chart_epochs (c i)⟩

end Hironaka.HironakaG8CertifiedCofinalEvents
