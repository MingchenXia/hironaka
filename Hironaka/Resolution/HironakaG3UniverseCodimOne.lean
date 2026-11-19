import Hironaka.Resolution.HironakaG3UniverseMarkedCosupport
import Hironaka.Resolution.HironakaG3UniverseLiftManifold
import Hironaka.Resolution.HironakaG3UniverseRegularTransport
import Hironaka.MarkedIdeal.CodimOneSupportAlong
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseCodimOne
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold
  G3UniverseMarkedCosupport HironakaG3UniverseCoordinateTransport CodimOneSupportAlong GermIdealOrder
noncomputable section

/-- The actual codimension-one cosupport part commutes with the literal lift. -/
theorem codimOne_lifted_record {n : ℕ} (X : CMfd.{0} n) (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent) :
    codimOnePartAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M).N
      (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M).ideal M.d =
    (liftDiffeomorph.{u} X).symm ⁻¹' codimOnePartAlong M.N M.ideal M.d := by
  have hc := markedPullback_cosupp_diffeo (liftDiffeomorph.{u} X).symm M hM
  ext y
  change (∃ k, RegularAtDim (n := n) ((liftDiffeomorph.{u} X).symm ⁻¹' M.N) y (k + 1) ∧
      RegularAtDim (n := n) (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M).cosupp y k) ↔
    ∃ k, RegularAtDim (n := n) M.N ((liftDiffeomorph.{u} X).symm y) (k + 1) ∧
      RegularAtDim (n := n) M.cosupp ((liftDiffeomorph.{u} X).symm y) k
  rw [hc]
  constructor
  · rintro ⟨k, hN, hS⟩
    exact ⟨k, (transported_regularAtDim_iff (Homeomorph.ulift.symm : X ≃ₜ ULift.{u} X) M.N y (k+1)).mp hN,
      (transported_regularAtDim_iff (Homeomorph.ulift.symm : X ≃ₜ ULift.{u} X) M.cosupp y k).mp hS⟩
  · rintro ⟨k, hN, hS⟩
    exact ⟨k, (transported_regularAtDim_iff (Homeomorph.ulift.symm : X ≃ₜ ULift.{u} X) M.N y (k+1)).mpr hN,
      (transported_regularAtDim_iff (Homeomorph.ulift.symm : X ≃ₜ ULift.{u} X) M.cosupp y k).mpr hS⟩
end
end Hironaka.G3UniverseCodimOne
