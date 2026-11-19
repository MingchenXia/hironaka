import Hironaka.Resolution.HironakaG3UniverseCarrierGeometry
import Hironaka.Resolution.HironakaG3UniverseOrderedBoundary
import Hironaka.Resolution.HironakaG3UniverseNonzeroAlong
set_option autoImplicit false
set_option linter.style.haveILetI false
open Set Function
open scoped Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3UniverseMarkedDomain
open BlowupTowers MarkedIdeals ResolutionInvariantSpec
  HironakaG3UniverseChartTransport HironakaG3UniverseCoordinateTransport
  HironakaG3UniverseCarrierGeometry HironakaG3UniverseOrderedBoundary
  HironakaG3UniverseNonzeroAlong HironakaSmoothSubmersionCoefficientIdeals
  GermIdealPullbackCalculus
noncomputable section

/-- A literal transported-atlas copy preserves the original invariant domain. -/
theorem transported_markedPullback_domain {n k : ℕ} (X : CMfd.{u} n) {Y : Type v}
    [TopologicalSpace Y] (e : X ≃ₜ Y) (M : MarkedIdeal n X) (hM : IsInvDomain k M) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    letI : IsComplexManifold n Y := transported_complex_manifold e
    IsInvDomain k (markedPullback (m := n) e.symm M) := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  letI : IsComplexManifold n Y := transported_complex_manifold e
  have he := transported_homeomorph_symm_contMDiff (n := n) e
  refine ⟨⟨?_,?_,?_,?_⟩,?_,hM.one_le_d,?_⟩
  · exact transported_closedSubmanifold e M.N hM.isWellFormed.isClosedSubmanifold_N
  · exact isCoherent_pullback he hM.isWellFormed.isCoherent
  · exact transported_list_snc X e M.E hM.isWellFormed.isSNCDivisor
  · exact transported_list_transverse X e M.N M.E hM.isWellFormed.isTransverse
  · intro y hy
    obtain ⟨j,hjk,hj⟩ := hM.dimLE (e.symm y) hy
    exact ⟨j,hjk,(transported_regularAtDim_iff e M.N y j).2 hj⟩
  · intro y hy
    exact nonzeroAlong_pullback_homeomorph e.symm he hM.isWellFormed.isCoherent
      (hM.isNonzeroAlongAt (e.symm y) hy)
end
end Hironaka.HironakaG3UniverseMarkedDomain
