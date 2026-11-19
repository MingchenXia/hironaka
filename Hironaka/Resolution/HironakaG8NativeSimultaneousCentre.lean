import Hironaka.Resolution.HironakaStageCenters
import Hironaka.Invariant.ResolutionInvariantSeq

/-! Simultaneous maximum loci in one actual native phase. -/

set_option autoImplicit false

open Set TopologicalSpace

namespace Hironaka.HironakaG8NativeSimultaneousCentre

noncomputable section

open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal HironakaStageCenters

variable {n k : ℕ} {X Y : CMfd.{0} n} {I Λ : Type} [LinearOrder Λ]

/-- One numeric maximum is selected simultaneously on all literal native
windows, with no portion of the global centre outside those windows. -/
structure NativeSimultaneousCentre
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    (U : I → Opens X) (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (T : BlowupTower X Y) (C : Set Y) (m : Λ) : Prop where
  covered : ∀ y ∈ C, ∃ i, y ∈ openPreimage T (U i)
  upper : ∀ i (z : openPreimage T (U i)), z ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp →
    R.inv (P i) (restrict (U i) T) z ≤ m
  trace : ∀ i, (Subtype.val : openPreimage T (U i) → Y) ⁻¹' C =
    {z | z ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp ∧
      R.inv (P i) (restrict (U i) T) z = m}

/-- Every genuine nonempty stage of the actual native phase has a
simultaneous maximum, with literal empty stages allowed. -/
def NativeSimultaneousStages
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    (U : I → Opens X) (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (T : BlowupTower X Y) : Prop :=
  StageCentres (fun S C => C = ∅ ∨ ∃ m, NativeSimultaneousCentre R U P S C m) T

end
end Hironaka.HironakaG8NativeSimultaneousCentre
