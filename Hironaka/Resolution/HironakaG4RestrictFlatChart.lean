import Hironaka.Resolution.HironakaG4OpenGammaChart

/-! Shrink a chart's flat domain to any neighborhood without changing its map. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4RestrictFlatChart
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupFlatCoordinates
  HironakaG34CoordinateScaling

variable {n : ℕ} {X : CMfd.{u} n}

/-- Restriction to any open neighborhood keeps the coordinate map and puts
the entire flat chart domain in that neighborhood. -/
theorem exists_flat_chart_inside_open {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (U : Opens X) (hxU : x ∈ U) :
    ∃ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x),
      Ψ.source ⊆ Φ.source ∧ flatDomain Ψ ⊆ (U : Set X) ∧
      (∀ y ∈ flatDomain Ψ, y ∈ flatDomain Φ ∧ flatMap Ψ y = flatMap Φ y) ∧
      Ψ.toFun (chartAt (ComplexModel n) x x) = Φ.toFun (chartAt (ComplexModel n) x x) := by
  let e := chartAt (ComplexModel n) x
  let P : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' (U : Set X)
  have hPo : IsOpen P := e.continuousOn_symm.isOpen_inter_preimage e.open_target U.isOpen
  have hxp : e x ∈ Φ.source ∩ P := by
    refine ⟨Φ.center_mem_source,e.map_source (mem_chart_source (ComplexModel n) x),?_⟩
    change e.symm (e x) ∈ U
    rw [e.left_inv (mem_chart_source (ComplexModel n) x)]
    exact hxU
  let Ψ := Φ.restrict P hPo (e x) hxp
  refine ⟨Ψ, (fun _ hz => hz.1), ?_, ?_, rfl⟩
  · intro y hy
    have hh := hy.2.2.2
    change e.symm (e y) ∈ U at hh
    rwa [e.left_inv hy.1] at hh
  · intro y hy
    exact ⟨⟨hy.1,hy.2.1⟩,rfl⟩

end
end Hironaka.HironakaG4RestrictFlatChart
