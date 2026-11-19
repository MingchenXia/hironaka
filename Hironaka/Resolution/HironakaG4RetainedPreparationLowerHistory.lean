import Hironaka.Resolution.HironakaG4RetainedPreparationTrace

/-! Admissibility of the exact lower terminal leaves of a retained preparation trace. -/

set_option autoImplicit false
universe u

namespace Hironaka.HironakaG4RetainedPreparationLowerHistory

open Hironaka.BlowupSequences BlowupTowers
  HironakaG4RetainedPreparationTrace HironakaG4PreparedCentreCoordinates
  HironakaG4ResidualInductionInputs

/-- A condition on the exact actual sharp tower for a literal source record. -/
abbrev SharpHistoryPredicate (n : ℕ) :=
  ∀ {X Y : CMfd.{u} n}, Set X → List (Set X) → BlowupTower X Y → Prop

variable {n : ℕ} {hn : 0 < n} {X Y : CMfd.{u} n}
variable {N : Set X} {old born : List (Set X)} {phases : List RetainedPreparationPhase}
variable {T : BlowupTower X Y}

/-- Every original lower leaf is admitted at its own literal carrier,
remaining ordered boundary, and actual tower. Restrictions and rebases
retain the witnesses supplied by those original leaves. -/
def usesLowerHistory (P : SharpHistoryPredicate.{u} n)
    (trace : RetainedPreparationTrace hn N old born phases T) : Prop := by
  induction trace with
  | defect _ => exact True
  | @lower A B W I C R _ _ i _ _ =>
      exact P (X := A) (Y := B) (W ∩ (oldResidualPart W I C i).zeroLocus)
        (remainingBoundary I C i) R
  | append _ _ _ _ _ _ _ ih₁ ih₂ => exact ih₁ ∧ ih₂
  | restrictOpen _ _ _ ih => exact ih
  | rebase _ _ _ ih => exact ih

theorem usesLowerHistory_unrestricted (trace : RetainedPreparationTrace hn N old born phases T) :
    usesLowerHistory (fun {_ _} _ _ _ => True) trace := by
  induction trace with
  | defect _ | lower _ _ _ _ _ => trivial
  | append _ _ _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁,ih₂⟩
  | restrictOpen _ _ _ ih => exact ih
  | rebase _ _ _ ih => exact ih

theorem usesLowerHistory_mono {P Q : SharpHistoryPredicate.{u} n}
    (hPQ : ∀ {A B : CMfd.{u} n} (W : Set A) (E : List (Set A)) (R : BlowupTower A B),
      P W E R → Q W E R) (trace : RetainedPreparationTrace hn N old born phases T) :
    usesLowerHistory P trace → usesLowerHistory Q trace := by
  induction trace with
  | defect _ => simp [usesLowerHistory]
  | lower _ _ _ _ _ => exact hPQ _ _ _
  | append _ _ _ _ _ _ _ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1,ih₂ h.2⟩
  | restrictOpen _ _ _ ih => exact ih
  | rebase _ _ _ ih => exact ih

end Hironaka.HironakaG4RetainedPreparationLowerHistory
