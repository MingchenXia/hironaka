import Hironaka.Resolution.HironakaG11PresTowerState
import Hironaka.Invariant.MemberInterLocusAlong

/-! The Hilbert–Samuel state persists when an actual test prefix becomes the new base. -/

set_option autoImplicit false

open Set

universe u

namespace Hironaka.HironakaG11PresTowerState

open Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedGlueingTower MemberInterLocusAlong

/-- The transformed record presents the same Hilbert–Samuel profile on the
strict transform, with the full state available along every subsequent test. -/
theorem HSTowerState.rebase {n : ℕ} {X Y : CMfd.{u} n}
    {Q : MarkedIdeal n X} {W : Set X} {H : ℕ → ℕ} (hState : HSTowerState Q W H)
    (T : BlowupTower X Y) (hT : IsGeoTestTower Q T) :
    HSTowerState (geoTransformAlong Q T) (strictAlong T W) H := by
  intro Z S hS
  have hAppend := (isGeoTestTower_append_iff Q T S).mpr ⟨hT, hS⟩
  simpa only [geoTransformAlong_append, strictAlong_append] using hState (T.append S) hAppend

end Hironaka.HironakaG11PresTowerState
