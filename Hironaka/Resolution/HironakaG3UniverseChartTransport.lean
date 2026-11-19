import Hironaka.Blowup.BlowupTowers
import Mathlib.Topology.Instances.Shrink
set_option autoImplicit false
open Set Function TopologicalSpace OpenPartialHomeomorph
open scoped Topology Manifold ContDiff
universe u v w
namespace Hironaka.HironakaG3UniverseChartTransport
noncomputable section

/-- Transport every chart by one actual homeomorphism, retaining the old atlas. -/
@[instance_reducible] def transportedChartedSpace {H : Type w} {X : Type u} {Y : Type v}
    [Nonempty H]
    [TopologicalSpace H] [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X]
    (e : X ≃ₜ Y) : ChartedSpace H Y where
  atlas := (fun c : OpenPartialHomeomorph X H => c.lift_openEmbedding e.isOpenEmbedding) '' atlas H X
  chartAt y := (chartAt H (e.symm y)).lift_openEmbedding e.isOpenEmbedding
  mem_chart_source y := ⟨e.symm y,mem_chart_source H (e.symm y),e.apply_symm_apply y⟩
  chart_mem_atlas y := ⟨chartAt H (e.symm y),chart_mem_atlas H (e.symm y),rfl⟩

/-- Coordinate transitions are unchanged when the same homeomorphism is
precomposed into both charts. -/
theorem transported_chart_transition {H : Type w} {X : Type u} {Y : Type v}
    [Nonempty H]
    [TopologicalSpace H] [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (a b : OpenPartialHomeomorph X H) :
    (a.lift_openEmbedding e.isOpenEmbedding).symm.trans
        (b.lift_openEmbedding e.isOpenEmbedding) = a.symm.trans b :=
  a.lift_openEmbedding_trans b e.isOpenEmbedding

/-- A transported atlas has the same structure groupoid compatibility. -/
theorem transported_hasGroupoid {H : Type w} {X : Type u} {Y : Type v}
    [Nonempty H]
    [TopologicalSpace H] [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X]
    (e : X ≃ₜ Y) (G : StructureGroupoid H) [HasGroupoid X G] :
    @HasGroupoid H _ Y _ (transportedChartedSpace e) G := by
  let : ChartedSpace H Y := transportedChartedSpace e
  refine ⟨?_⟩
  intro a b ha hb
  obtain ⟨a,ha,rfl⟩ := ha
  obtain ⟨b,hb,rfl⟩ := hb
  rw [transported_chart_transition]
  exact G.compatible ha hb
end
end Hironaka.HironakaG3UniverseChartTransport
