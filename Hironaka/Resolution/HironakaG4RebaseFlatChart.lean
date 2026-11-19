import Hironaka.Blowup.RegularPatchPullback
import Hironaka.Blowup.BlowupSpaceTangent
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Resolution.HironakaG34CoordinateScaling

/-!
# Rebasing a flat chart without translating its coordinate values

A point anywhere in the qualified domain has its own chart-at-point
presentation with the same literal coordinate functions on an open subset.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4RebaseFlatChart
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates HironakaG34CoordinateScaling

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {x₀ x : X}

/-- A flat chart can be based at any point of its domain while retaining
its uncentred coordinate values and staying inside the original domain. -/
theorem exists_rebased_flat_chart
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (hx : x ∈ flatDomain (y₀ := x₀) Φ) :
    ∃ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x),
      Ψ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      ∀ y ∈ flatDomain (y₀ := x) Ψ, y ∈ flatDomain (y₀ := x₀) Φ ∧
        flatMap (x₀ := x) Ψ y = flatMap (x₀ := x₀) Φ y := by
  set e := chartAt (ComplexModel n) x with he
  let d := chartAt (ComplexModel n) x₀
  set F : ComplexModel n → ComplexModel n := fun u => d (e.symm u) with hF
  set O : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' d.source with hO
  have hOo : IsOpen O := e.continuousOn_symm.isOpen_inter_preimage e.open_target d.open_source
  have hxO : e x ∈ O := ⟨e.map_source (mem_chart_source _ x), by
    rw [mem_preimage, e.left_inv (mem_chart_source _ x)]
    exact hx.1⟩
  have hFO : DifferentiableOn ℂ F O := by
    intro u hu
    exact (BlowupSpaceTangent.differentiableAt_chart_comp_chart_symm hu.1 hu.2).differentiableWithinAt
  have hinj : Function.Injective (fderiv ℂ F (e x)) := by
    have hno : x ∉ exceptionalLocus n (id : X → X) := by simp [exceptionalLocus_id]
    have h := RegularPatchPullback.injective_fderiv_chartExpr (g := id) contMDiff_id hno
      (complexChartAt (n := n) x₀) hx.1
    change Function.Injective (fderiv ℂ (fun u =>
      (chartAt (ComplexModel n) x₀) ((chartAt (ComplexModel n) x).symm u))
        ((chartAt (ComplexModel n) x) x)) at h
    exact h
  obtain ⟨Θ, hΘO, hΘF, -⟩ := exists_localHolomorphicEquivAt hOo hxO hFO hinj
  have hFx : F (e x) = d x := by simp [hF, e.left_inv (mem_chart_source _ x)]
  have hxΦ : d x ∈ Φ.source := hx.2
  let Φx : LocalHolomorphicEquivAt (n := n) (d x) :=
    Φ.restrict univ isOpen_univ (d x) ⟨hxΦ, mem_univ _⟩
  let Ψ := RegularAtDimTransport.LocalHolomorphicEquivAt.comp Θ Φx (hΘF ▸ hFx)
  refine ⟨Ψ, fun u hu => (hΘO hu.1).1, ?_⟩
  intro y hy
  obtain ⟨hyE, hyΨ⟩ := hy
  change e y ∈ Θ.source ∩ Θ.toFun ⁻¹' Φx.source at hyΨ
  have hyO := (hΘO hyΨ.1).2
  rw [mem_preimage, e.left_inv hyE] at hyO
  have hFy : F (e y) = d y := by simp [hF, e.left_inv hyE]
  have hyd : d y ∈ Φ.source := by
    have h := hyΨ.2
    change Θ.toFun (e y) ∈ Φ.source ∩ univ at h
    rw [hΘF, hFy] at h
    exact h.1
  refine ⟨⟨hyO, hyd⟩, ?_⟩
  change Φ.toFun (Θ.toFun (e y)) = Φ.toFun (d y)
  rw [hΘF, hFy]

end
end Hironaka.HironakaG4RebaseFlatChart
