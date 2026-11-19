import Hironaka.Resolution.HironakaG3UniverseRegularTransport
import Hironaka.Resolution.HironakaActualIndexedBoundaryContinuation
set_option autoImplicit false
set_option linter.style.haveILetI false
open Set Function
open scoped Manifold ContDiff
universe u v w
namespace Hironaka.HironakaG3UniverseCarrierGeometry
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaActualIndexedBoundaryContinuation HironakaG3UniverseChartTransport
  HironakaG3UniverseCoordinateTransport

/-- Closed submanifold status follows the actual transported atlas. -/
theorem transported_closedSubmanifold {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (e : X ≃ₜ Y) (C : Set X) (hC : IsClosedSubmanifold n C) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    letI : IsComplexManifold n Y := transported_complex_manifold e
    IsClosedSubmanifold n (e.symm ⁻¹' C) := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  letI : IsComplexManifold n Y := transported_complex_manifold e
  refine ⟨hC.1.preimage e.symm.continuous, ?_⟩
  intro y hy
  obtain ⟨d,hd⟩ := hC.2 (e.symm y) hy
  exact ⟨d,(transported_regularAtDim_iff e C y d).2 hd⟩

/-- Normal crossings with the indexed boundary follow the same coordinate witnesses. -/
theorem transported_normalCrossings {n : ℕ} (X : CMfd.{u} n) {Y : Type v}
    [TopologicalSpace Y] (e : X ≃ₜ Y) {ι : Type w} (C : Set X) (D : ι → Set X)
    (hNC : HasNormalCrossingsWithBoundary C D) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    letI : IsComplexManifold n Y := transported_complex_manifold e
    HasNormalCrossingsWithBoundary (X := CMfd.of (n := n) Y)
      (e.symm ⁻¹' C) (fun i => e.symm ⁻¹' D i) := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  letI : IsComplexManifold n Y := transported_complex_manifold e
  intro y hy
  obtain ⟨S₀,S,hcoord,hcard⟩ := hNC (e.symm y) hy
  refine ⟨S₀,S,?_,?_⟩
  · have h := transported_coordinate_family e (fun o : Option ι => o.elim C D)
      (fun o => o.elim S₀ S) y hcoord
    convert h using 1
    funext o
    cases o <;> rfl
  · intro i hi
    exact hcard i hi
end
end Hironaka.HironakaG3UniverseCarrierGeometry
