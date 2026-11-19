import Hironaka.Resolution.HironakaG3UniverseNormalCrossings
import Hironaka.Resolution.HironakaG3UniverseMarkedCosupport
import Hironaka.Resolution.HironakaG3UniverseLiftManifold
set_option autoImplicit false
open Set Function
open scoped Manifold ContDiff
universe u
namespace Hironaka.HironakaG3UniverseLiftedAdmissibility
open Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold
  HironakaG3UniverseCarrierGeometry G3UniverseMarkedCosupport HironakaG3UniverseNormalCrossings
noncomputable section

/-- An actual admissible centre remains admissible for the literal lifted marked record. -/
theorem lifted_admissibleCentre {n : ℕ} (X : CMfd.{0} n) (M : MarkedIdeal n X)
    (hM : M.ideal.IsCoherent) (C : Set X) (hC : M.IsAdmissibleCentre C) :
    (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M).IsAdmissibleCentre
      ((liftDiffeomorph.{u} X).symm ⁻¹' C) := by
  refine ⟨?_,?_,?_⟩
  · exact transported_closedSubmanifold (Homeomorph.ulift.symm : X ≃ₜ ULift.{u} X) C hC.1
  · rw [markedPullback_cosupp_diffeo (liftDiffeomorph.{u} X).symm M hM]
    exact preimage_mono hC.2.1
  · exact transported_list_normalCrossings X (Homeomorph.ulift.symm : X ≃ₜ ULift.{u} X) C M.E hC.2.2
end
end Hironaka.HironakaG3UniverseLiftedAdmissibility
