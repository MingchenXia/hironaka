import Hironaka.Resolution.HironakaG3UniverseComplexTransport
import Hironaka.Resolution.HironakaG3UniverseSmallManifold
import Mathlib.Geometry.Manifold.Diffeomorph
set_option autoImplicit false
open scoped Manifold ContDiff
universe u
namespace Hironaka.HironakaG3UniverseShrinkManifold
noncomputable section
open BlowupTowers HironakaG3UniverseChartTransport HironakaG3UniverseSmallManifold

/-- A complex manifold has a literally transported base-universe model. -/
def shrinkCMfd {n : ℕ} (X : CMfd.{u} n) : CMfd.{0} n := by
  letI : Small.{0} X := complex_manifold_small X
  let e := Shrink.homeomorph X
  letI : ChartedSpace (ComplexModel n) (Shrink.{0} X) := transportedChartedSpace e
  letI : IsComplexManifold n (Shrink.{0} X) := transported_complex_manifold e
  exact CMfd.of (n := n) (Shrink.{0} X)

/-- The universe-small model is biholomorphic to the original manifold. -/
def shrinkDiffeomorph {n : ℕ} (X : CMfd.{u} n) :
    X ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ shrinkCMfd X := by
  letI : Small.{0} X := complex_manifold_small X
  let e := Shrink.homeomorph X
  exact { toEquiv := e.toEquiv
          contMDiff_toFun := transported_homeomorph_contMDiff e
          contMDiff_invFun := transported_homeomorph_symm_contMDiff e }
end
end Hironaka.HironakaG3UniverseShrinkManifold
