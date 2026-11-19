import Hironaka.Resolution.HironakaG3UniverseCoordinateTransport
import Hironaka.Resolution.HironakaActualLocallyFiniteBoundary
set_option autoImplicit false
set_option linter.style.haveILetI false
open Set Function
open scoped Manifold ContDiff
universe u v w
namespace Hironaka.HironakaG3UniverseIndexedSNC
noncomputable section
open BlowupTowers NormalCrossings HironakaActualLocallyFiniteBoundary
  HironakaG3UniverseChartTransport HironakaG3UniverseCoordinateTransport

/-- The whole indexed SNC family pulls back through the transported atlas. -/
theorem transported_indexed_snc {n : ℕ} (X : CMfd.{u} n) {Y : Type v}
    [TopologicalSpace Y] (e : X ≃ₜ Y) {ι : Type w} (D : ι → Set X)
    (hD : IsLocallyFiniteSNCDivisor n D) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    letI : IsComplexManifold n Y := transported_complex_manifold e
    IsLocallyFiniteSNCDivisor n (Q := CMfd.of (n := n) Y) (fun i => e.symm ⁻¹' D i) := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  letI : IsComplexManifold n Y := transported_complex_manifold e
  refine ⟨hD.1.preimage_continuous e.symm.continuous, fun i => (hD.2.1 i).preimage e.symm.continuous, ?_⟩
  intro y
  obtain ⟨S,hcoord,hcard,hinj⟩ := hD.2.2 (e.symm y)
  refine ⟨S,transported_coordinate_family e D S y hcoord, ?_, ?_⟩
  · intro i hi
    exact hcard i hi
  · exact hinj
end
end Hironaka.HironakaG3UniverseIndexedSNC
