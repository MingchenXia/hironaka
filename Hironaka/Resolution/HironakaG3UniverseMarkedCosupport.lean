import Hironaka.Resolution.HironakaG3UniverseSubmersionConjugate
import Hironaka.Resolution.HironakaSmoothSubmersionCoefficientIdeals
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeOrder
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3UniverseMarkedCosupport
open Hironaka.HolomorphicIdealSheaves BlowupTowers MarkedIdeals
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeOrder
  G3UniverseSubmersionConjugate
noncomputable section

/-- The literal cross-universe pullback of a coherent marked record has exactly the pulled-back cosupport. -/
theorem markedPullback_cosupp_diffeo {n : ℕ} {X : CMfd.{u} n} {Y : CMfd.{v} n}
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent) :
    (markedPullback (m := n) e M).cosupp = e ⁻¹' M.cosupp := by
  exact cosupport_preimage_eq (diffeo_isSubmersion e) hM M.N M.d
end
end Hironaka.G3UniverseMarkedCosupport
