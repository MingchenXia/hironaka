import Hironaka.Resolution.HironakaG8SpatialDependencyBranching
import Hironaka.Resolution.HironakaG8SurfaceSingularPhase

/-! # Compact event footprints from connected surface singular support -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set TopologicalSpace

namespace Hironaka.HironakaG8SurfaceConnectedEventBranching

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaEmbeddedAnalytic HironakaStageCenters RestrictEmptyTower
  HironakaG3RTowerClass HironakaG8CompactEventAncestry
  HironakaG8SpatialDependencyBranching HironakaG8SurfaceSingularPhase
  HironakaG8IntrinsicSingularBlockSchedule HironakaUniformHistoricalSuccessorOriginalRegular
  HironakaResolutionSpaceLocal

private theorem centreFootprints_subset_compl_of_centresAvoid {n : ℕ} {X Y : CMfd.{0} n}
    (F : Opens X) (T : BlowupTower X Y) (h : CentresAvoid F T) :
    ∀ D ∈ centreFootprints T, D ⊆ (F : Set X)ᶜ := by
  induction T with
  | refl => simp [centreFootprints]
  | step T C π hπ ih =>
    intro D hD
    rcases List.mem_append.mp hD with hD' | hD'
    · exact ih h.1 D hD'
    · have hEq := List.mem_singleton.mp hD'
      change D = T.proj '' C at hEq
      rw [hEq]
      rintro _ ⟨z,hz,rfl⟩
      exact Set.disjoint_left.mp h.2 hz

/-- Every projected occurrence in a chart's actual singular-only history
lies in the original source singular set. This applies before the separate
smooth boundary-cleanup suffix of the complete embedded chart. -/
theorem projected_singular_event_subset_original_singular
    {n : ℕ} {X Z : CMfd.{0} n} {I ε : Type*}
    {K : LocalTowerClass X} {p : Z → X} (c : I → TowerChart K Z p)
    (event : ∀ i, Fin (centreFootprints (c i).T).length → ε)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hStages : ∀ i, StageCentres (fun T D => D ⊆ singularSet (n := n)
      (strictTransform n T.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) (c i).T)
    (a : ε) :
    eventFootprint c event a ⊆ singularSet (n := n) W := by
  rintro _ ⟨i,j,rfl,z,hz,rfl⟩
  let U := (c i).U
  let WU := (Subtype.val : U → X) ⁻¹' W
  have hWU := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW U
  have hHistory := intrinsic_stage_native_history WU (c i).T (hStages i)
  let O : Opens U :=
    ⟨(singularSet (n := n) WU)ᶜ,(isClosed_singularSet hWU.isClosed).isOpen_compl⟩
  have hAvoid : CentresAvoid O (c i).T :=
    (actual_singular_history_original_regular_protection WU hWU (c i).T hHistory).1
  have hProjection := centreFootprints_subset_compl_of_centresAvoid O (c i).T hAvoid _ (List.get_mem _ j) hz
  have hzS : z ∈ singularSet (n := n) WU := by
    simpa only [O,Opens.coe_mk,compl_compl] using hProjection
  rw [singularSet_preimage_val] at hzS
  exact hzS

/-- A connected projected event in a surface singular-only history is
supported at at most one original point. Compactness then follows from
surface discreteness and is not an extra assumption on the event. -/
theorem connected_surface_singular_event_subsingleton
    {X Z : CMfd.{0} 2} {I ε : Type*}
    {K : LocalTowerClass X} {p : Z → X} (c : I → TowerChart K Z p)
    (event : ∀ i, Fin (centreFootprints (c i).T).length → ε)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W)
    (hStages : ∀ i, StageCentres (fun T D => D ⊆ singularSet (n := 2)
      (strictTransform 2 T.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) (c i).T)
    (a : ε) (ha : IsPreconnected (eventFootprint c event a)) :
    (eventFootprint c event a).Subsingleton := by
  have hSub := projected_singular_event_subset_original_singular c event W hW hStages a
  have hDiscrete := (isDiscrete_iff_discreteTopology.mpr (surface_singular_discrete hW)).mono hSub
  exact ha.isDiscrete_iff_subsingleton.mp hDiscrete

/-- Connected events of a surface singular-only physical atlas have
finite incoming spatial dependencies without a separate compactness
hypothesis. The chosen edge relation still has to be spatial. -/
theorem finite_incoming_of_connected_surface_singular_events
    {X Z : CMfd.{0} 2} {I ε : Type*}
    {K : LocalTowerClass X} {p : Z → X} (c : I → TowerChart K Z p)
    (event : ∀ i, Fin (centreFootprints (c i).T).length → ε)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W)
    (hStages : ∀ i, StageCentres (fun T D => D ⊆ singularSet (n := 2)
      (strictTransform 2 T.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) (c i).T)
    (hLF : LocallyFinite (fun i => ((c i).U : Set X)))
    (before : ε → ε → Prop)
    (hSpatial : ∀ ⦃a b⦄, before a b → (eventFootprint c event a ∩ eventFootprint c event b).Nonempty)
    (b : ε) (hb : IsPreconnected (eventFootprint c event b)) :
    {a | before a b}.Finite :=
  finite_incoming_of_compact_projected_events c event hLF before hSpatial b
    (connected_surface_singular_event_subsingleton c event W hW hStages b hb).isCompact

end Hironaka.HironakaG8SurfaceConnectedEventBranching
