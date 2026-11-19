import Hironaka.Resolution.HironakaG3UniverseChartTransport
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
set_option autoImplicit false
set_option linter.style.haveILetI false
open scoped Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3UniverseChartTransport
noncomputable section

open BlowupTowers

/-- A homeomorphic copy of a complex manifold carries the transported complex atlas. -/
theorem transported_complex_manifold {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (e : X ≃ₜ Y) :
    @IsComplexManifold n Y _ (transportedChartedSpace e) := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  letI : T2Space Y := e.symm.isEmbedding.t2Space
  letI : SecondCountableTopology Y := e.symm.isEmbedding.secondCountableTopology
  letI : HasGroupoid Y (contDiffGroupoid ∞ (𝓘(ℂ, ComplexModel n))) :=
    transported_hasGroupoid e _
  letI : IsManifold (𝓘(ℂ, ComplexModel n)) ∞ Y := IsManifold.mk' _ _ _
  exact {}

/-- The homeomorphism is holomorphic for the transported complex atlas. -/
theorem transported_homeomorph_contMDiff {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (e : X ≃ₜ Y) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    letI : IsComplexManifold n Y := transported_complex_manifold e
    ContMDiff (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ComplexModel n)) ∞ e := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  letI : IsComplexManifold n Y := transported_complex_manifold e
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨e.continuous.continuousAt, ?_⟩
  have h : (extChartAt (𝓘(ℂ, ComplexModel n)) (e x) ∘ e) =
      extChartAt (𝓘(ℂ, ComplexModel n)) x := by
    funext y
    change ((chartAt (ComplexModel n) (e.symm (e x))).lift_openEmbedding e.isOpenEmbedding) (e y) =
      (chartAt (ComplexModel n) x) y
    rw [e.symm_apply_apply]
    exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _
  rw [h]
  exact contMDiffAt_extChartAt

/-- The inverse homeomorphism is holomorphic for the transported atlas. -/
theorem transported_homeomorph_symm_contMDiff {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (e : X ≃ₜ Y) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    letI : IsComplexManifold n Y := transported_complex_manifold e
    ContMDiff (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ComplexModel n)) ∞ e.symm := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  letI : IsComplexManifold n Y := transported_complex_manifold e
  intro y
  rw [contMDiffAt_iff_target]
  refine ⟨e.symm.continuous.continuousAt, ?_⟩
  have h : (extChartAt (𝓘(ℂ, ComplexModel n)) (e.symm y) ∘ e.symm) =
      extChartAt (𝓘(ℂ, ComplexModel n)) y := by
    funext z
    change (chartAt (ComplexModel n) (e.symm y)) (e.symm z) =
      ((chartAt (ComplexModel n) (e.symm y)).lift_openEmbedding e.isOpenEmbedding) z
    conv_rhs => rw [← e.apply_symm_apply z]
    exact (OpenPartialHomeomorph.lift_openEmbedding_apply _ _).symm
  rw [h]
  exact contMDiffAt_extChartAt
end
end Hironaka.HironakaG3UniverseChartTransport
