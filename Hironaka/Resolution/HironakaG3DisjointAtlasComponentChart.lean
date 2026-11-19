import Hironaka.Resolution.HironakaG3DisjointLocalTowerAtlas
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointAtlasComponentChart
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass HironakaG3DisjointLocalTowerAtlas

/-- A chart of the assembled class meeting a component is literally a chart
of that component's class, with the same base, tower, inclusion, and map. -/
theorem disjoint_atlas_chart_over_component {n : ℕ} {X Z : CMfd.{0} n} {ι : Type*}
    (A : ι → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hWindow : ∀ i j, i ≠ j → Disjoint (A j) (W i : Set X))
    {P : Z → X} (c : TowerChart (disjointWindowClass A W K) Z P)
    (i : ι) {x : X} (hxA : x ∈ A i) (hxU : x ∈ c.U) :
    c.U ≤ W i ∧ K i c.U c.Y c.T := by
  rcases c.mem with ⟨j,hj,hK⟩ | ⟨havoid,_⟩
  · have hji : j = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hWindow j i hne) hxA (hj hxU)
    subst j
    exact ⟨hj,hK⟩
  · exact False.elim ((havoid hxU) (mem_iUnion.mpr ⟨i,hxA⟩))

/-- Over a component, the same global map admits an actual component-class
chart; its restricted source is the given global map's saturated open. -/
theorem exists_component_chart_for_disjoint_atlas {n : ℕ} {X Z : CMfd.{0} n} {ι : Type*}
    (A : ι → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hWindow : ∀ i j, i ≠ j → Disjoint (A j) (W i : Set X))
    {P : Z → X} (hP : IsGluedFrom (disjointWindowClass A W K) Z P)
    (i : ι) {x : X} (hx : x ∈ A i) :
    ∃ c : TowerChart (K i) Z P, x ∈ c.U ∧ c.U ≤ W i := by
  obtain ⟨c,hxU⟩ := hP.2.2.2 x
  obtain ⟨hUW,hK⟩ := disjoint_atlas_chart_over_component A W K hWindow c i hx hxU
  let c' : TowerChart (K i) Z P := ⟨c.U,c.Y,c.T,hK,c.V,c.V_eq,c.φ,c.proj_φ⟩
  exact ⟨c',hxU,hUW⟩
end
end Hironaka.HironakaG3DisjointAtlasComponentChart
