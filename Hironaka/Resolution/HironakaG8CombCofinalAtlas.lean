import Hironaka.Resolution.HironakaG8CofinalPhysicalCharts
import Hironaka.Resolution.HironakaG8CofinalEventLimit
import Hironaka.Resolution.HironakaG8InitialBoundaryAtlasMarkOne
import Hironaka.Resolution.HironakaG8CombNativeFirstHits
import Hironaka.Resolution.HironakaG8PhysicalCombNoSpatialRank

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8CombCofinalAtlas

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms HironakaEmbeddedAnalytic NormalCrossings HironakaG3RTowerClass
  HironakaG8CombNativeFirstHits HironakaG8VariableCombArrangement
  HironakaG8NoncompactInitialBoundaryAtlas HironakaG8LabelledEmbeddedAtlas
  HironakaG8LabelledEmbeddedTape HironakaG8OrderedSmoothSuffix HironakaG8LocalMixedSmoothCleanup
  HironakaG8CofinalPhysicalCharts HironakaG8CofinalEventLimit
  HironakaG8CofinalOccupiedAncestry HironakaG8PhysicalChartOccupiedLifts
  HironakaG8InitialBoundaryAtlasMarkOne HironakaG8CorrectedOrderedEndpoint
  HironakaG8SpatialCofinalPrecedence HironakaG8PhysicalCombNoSpatialRank
  G3UniversePhysicalClassComparisons

private theorem comb_dense :
    (comb : Set combManifold) ⊆ closure (comb \ ⋃ B ∈ ([] : List (Set combManifold)), B) := by
  intro x hx
  apply subset_closure
  refine ⟨hx, ?_⟩
  intro h
  obtain ⟨B,hB⟩ := mem_iUnion.mp h
  obtain ⟨hNil,_⟩ := mem_iUnion.mp hB
  exact List.not_mem_nil hNil

/-- The ordered comb class has physical empty-aware comparisons. -/
theorem comb_physical_comparisons :
    HasPhysicalComparisons (orderedInitialBoundaryClass (X := combManifold) comb []) := by
  have hC : SmoothTailHasComparisons (ascending_smooth_tail_certificate 3) := by
    intro A A' Y Y' φ A₀ E E' T T' hB hT' hT
    exact ordered_smooth_suffix_emptyAware φ (ds := List.finRange 4) hB hT' hT
  exact initial_boundary_class_physical (by decide) hC analytic_comb isSNCDivisor_nil comb_dense

/-- The actual ordered comb atlas supplies compact-cofinal charts on one
projection and a represented event quotient with literal physical lifts. -/
theorem exists_comb_cofinal_physical_events :
    ∃ (Z : CMfd.{0} 3) (P : Z → combManifold),
      IsGluedFrom (orderedInitialBoundaryClass comb []) Z P ∧
      ∃ (c : ℕ → CombChart (P := P)) (hm : Monotone fun i => (c i).U),
        (∀ i, IsCompact (closure ((c i).U : Set combManifold))) ∧
        (∀ i, closure ((c i).U : Set combManifold) ⊆ ((c (i+1)).U : Set combManifold)) ∧
        (∀ K : Set combManifold, IsCompact K → ∃ i, K ⊆ ((c i).U : Set combManifold)) ∧
        (∀ i, InitialBoundaryChartMarkOne (c i) ∧ InitialBoundaryChartEpochs (c i)) ∧
        (∀ i, IsClosedSubmanifold 3 (strictTransform 3 (c i).T.proj
          ((Subtype.val : (c i).U → combManifold) ⁻¹' comb))) ∧
        ∃ (I : Type) (A : CofinalEvents c I),
          (∀ e, ∃ i p, A.event i p = e) ∧
          (∀ {i j} (h : i ≤ j) p, A.lift h p =
            chartOccupiedLift comb_physical_comparisons (c i) (c j) (hm h) p) := by
  obtain ⟨Z,P,hG,c,hm,hC,hNest,hCover⟩ :=
    exists_ordered_initial_boundary_cofinal_physical_charts (m := 2) (X := combManifold) (W := comb)
      analytic_comb isSNCDivisor_nil comb_dense
  let up {i j : ℕ} (h : i ≤ j) :=
    chartOccupiedLift comb_physical_comparisons (c i) (c j) (hm h)
  have hi (i : ℕ) (p : Slots c i) : up (le_refl i) p = p :=
    congrArg (fun e => e p) (chartOccupiedLift_id comb_physical_comparisons (c i))
  have hc {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (p : Slots c i) :
      up hjk (up hij p) = up (hij.trans hjk) p :=
    congrArg (fun e => e p)
      (chartOccupiedLift_comp comb_physical_comparisons (c i) (c j) (c k) (hm hij) (hm hjk))
  have hs {i j : ℕ} (h : i ≤ j) : StrictMono (up h) := (up h).strictMono
  refine ⟨Z,P,hG,c,hm,hC,hNest,hCover,fun i => ⟨?_,?_⟩,?_,?_⟩
  · exact initial_boundary_chart_original_markOne analytic_comb isSNCDivisor_nil comb_dense hG (c i)
  · exact initial_boundary_chart_epochs (c i)
  · intro i
    exact (c i).mem.geometry.2.2.1
  · exact ⟨_, eventLimit c (fun h p => up h p) hi hc hs,
      eventLimit_occurs c (fun h p => up h p) hi hc hs, fun _ _ => rfl⟩

/-- The variable comb has an actual compact-cofinal ordered embedded atlas
whose represented physical events admit no injective natural spatial rank. -/
theorem exists_comb_atlas_without_injective_spatial_rank :
    ∃ (Z : CMfd.{0} 3) (P : Z → combManifold),
      IsGluedFrom (orderedInitialBoundaryClass comb []) Z P ∧
      ∃ (c : ℕ → CombChart (P := P)) (hm : Monotone fun i => (c i).U),
        (∀ K : Set combManifold, IsCompact K → ∃ i, K ⊆ ((c i).U : Set combManifold)) ∧
        (∀ i, InitialBoundaryChartMarkOne (c i) ∧ InitialBoundaryChartEpochs (c i)) ∧
        ∃ (I : Type) (A : CofinalEvents c I),
          (∀ e, ∃ i p, A.event i p = e) ∧
          (∀ {i j} (h : i ≤ j) p, A.lift h p =
            chartOccupiedLift comb_physical_comparisons (c i) (c j) (hm h) p) ∧
          ¬ ∃ rank : I → ℕ, Injective rank ∧
            ∀ ⦃u v⦄, SpatialBefore A u v → rank u < rank v := by
  obtain ⟨Z,P,hG,c,hm,-,-,hCover,hCert,hSmooth,I,A,hOccurs,hLift⟩ :=
    exists_comb_cofinal_physical_events
  exact ⟨Z,P,hG,c,hm,hCover,hCert,I,A,hOccurs,hLift,
    no_injective_spatial_rank_of_physical_comb_chain A comb_physical_comparisons hm hLift
      hCover (fun i => (hCert i).2) hOccurs hSmooth⟩

end Hironaka.HironakaG8CombCofinalAtlas
