import Hironaka.Resolution.HironakaG3UniverseComplexTransport
import Mathlib.Geometry.Manifold.Diffeomorph
set_option autoImplicit false
open scoped Manifold ContDiff
universe u
namespace Hironaka.HironakaG3UniverseLiftManifold
noncomputable section
open BlowupTowers HironakaG3UniverseChartTransport

/-- The base-universe manifold as a literal complex manifold in universe u. -/
def liftCMfd {n : ℕ} (X : CMfd.{0} n) : CMfd.{u} n := by
  let e : X ≃ₜ ULift.{u} X := Homeomorph.ulift.symm
  letI : ChartedSpace (ComplexModel n) (ULift.{u} X) := transportedChartedSpace e
  letI : IsComplexManifold n (ULift.{u} X) := transported_complex_manifold e
  exact CMfd.of (n := n) (ULift.{u} X)

/-- The universe lift carries the actual transported biholomorphism. -/
def liftDiffeomorph {n : ℕ} (X : CMfd.{0} n) :
    X ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ liftCMfd.{u} X := by
  let e : X ≃ₜ ULift.{u} X := Homeomorph.ulift.symm
  exact { toEquiv := e.toEquiv
          contMDiff_toFun := transported_homeomorph_contMDiff e
          contMDiff_invFun := transported_homeomorph_symm_contMDiff e }
end
end Hironaka.HironakaG3UniverseLiftManifold
