import Hironaka.Resolution.HironakaG8HSTowerStateRebase
import Hironaka.Resolution.HironakaG11PresLineState
import Hironaka.Resolution.HironakaG11InvCommonMark
import Hironaka.Resolution.HironakaCoherentTransformExtension

/-! Replay a powered native Hilbert–Samuel record along the literal
restriction of an actual ambient prefix. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativePrefixReplay

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HomogenizedGlueingTower HironakaG11PresTowerState HironakaG11PresLineState
  ResolutionInvariantSpec HironakaActualPowerBoundaryExponents HironakaG11InvCommonMark
  HironakaCoherentTransformExtension

/-- The exact powered record on an actual ambient restriction retains the
state of the strict trace and every ambient boundary position after the
given prefix. -/
theorem powered_native_state_after_actual_restriction
    {n k : ℕ} {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (W : Set X) (H : ℕ → ℕ) (U : Opens X) (P : MarkedIdeal n (CMfd.of (n := n) U))
    (hP : IsInvDomain k P) (hState : NativeHSState P ((Subtype.val : U → X) ⁻¹' W) H)
    (hE : P.E = M.E.map ((Subtype.val : U → X) ⁻¹' ·))
    (e : ℕ) (he : 1 ≤ e) (hLocal : IsGeoTestTower (powerMarked P e) (restrict U T)) :
    let Q := geoTransformAlong (powerMarked P e) (restrict U T)
    Q.E = (geoTransformAlong M T).E.map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·) ∧
    HSTowerState Q ((Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T W) H := by
  have hBound : (powerMarked P e).E = (MarkedIdeal.pullback (Subtype.val : U → X) M).E := hE
  have hComparison := geoTransformAlong_E_eq_of_E_eq hBound (restrict U T)
  have hPull := geoTransformAlong_restrict U hM.isClosedSubmanifold_N hM.isCoherent T hT
  rw [hPull] at hComparison
  refine ⟨hComparison, ?_⟩
  have hPowered : HSTowerState (powerMarked P e) ((Subtype.val : U → X) ⁻¹' W) H := by
    intro Z S hS
    obtain ⟨hTest, hCos⟩ := (wEquiv_powerMarked P hP he).2 S
    have hRaw := hTest.mpr hS
    rw [← hCos hRaw]
    exact hState.hsTowerState S hRaw
  rw [← strictAlong_restrict U T W]
  intro Z S hS
  exact hPowered.rebase (restrict U T) hLocal S hS

end Hironaka.HironakaG8NativePrefixReplay
