/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.NonmonomialOrderGlobalPhase
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Blowup.BlowupSequences
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.StepOnePhase
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The phases of the general value in the count of centres; the monomial phase is finite along growing sequences

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2 of Proposition `pr:resol`; Bierstone--Milman 2008
(`bierstone-milman08-functoriality`), Step II.

Along a canonical segment `T` of general value `genInv M 𝔪`, `StepOnePhase.centreValues (genInv M 𝔪) T` lists the
values of the nonempty centres; their first entries are the orders `ν` of the nonmonomial part (the phases). This
module splits the count of (8') by phases and settles the phase of order `0`:

* `exists_bound_of_isPrefix`: prefix-growing lists, each strictly decreasing, with entries in a set on which no sequence strictly
  decreases forever, have bounded lengths;
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralPhaseCount

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MonomialInvariant Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.StepOnePhase Hironaka.NonmonomialOrderLocal Hironaka.MaxOrderValue Hironaka.GeneralValue
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
open Hironaka.ResolutionInvariantSeq (GrowingSeq)

noncomputable section

variable {n : ℕ}

/-! ### Bounded lengths of prefix-growing strictly decreasing lists -/

section Lists

variable {β : Type*} [Preorder β]

/-- **Prefix-growing strictly decreasing lists with entries in a set on which no sequence decreases strictly forever have bounded
lengths** (otherwise the entries at the positions `0, 1, 2, …` of long enough lists form such a sequence). -/
theorem exists_bound_of_isPrefix (F : ℕ → List β) (hmono : ∀ i, F i <+: F (i + 1))
    (hpw : ∀ i, (F i).Pairwise (fun a b => b < a)) (P : β → Prop) (hP : ∀ i, ∀ b ∈ F i, P b)
    (hwf : ∀ g : ℕ → β, (∀ k, P (g k)) → ¬ StrictAnti g) : ∃ m : ℕ, ∀ i, (F i).length ≤ m := by
  classical
  by_contra hcon
  simp only [not_exists, not_forall, not_le] at hcon
  have hpre : ∀ i j, i ≤ j → F i <+: F j := by
    intro i j hij
    induction hij with
    | refl => exact List.prefix_refl _
    | step _ ih => exact ih.trans (hmono _)
  let idx : ℕ → ℕ := fun k => Nat.find (hcon k)
  have hidx : ∀ k, k < (F (idx k)).length := fun k => Nat.find_spec (hcon k)
  let g : ℕ → β := fun k => (F (idx k))[k]'(hidx k)
  refine hwf g (fun k => hP _ _ (List.getElem_mem _)) fun k k' hkk' => ?_
  have hj1 : idx k ≤ max (idx k) (idx k') := le_max_left _ _
  have hj2 : idx k' ≤ max (idx k) (idx k') := le_max_right _ _
  have e1 : g k = (F (max (idx k) (idx k')))[k]'(Nat.lt_of_lt_of_le (hidx k) (hpre _ _ hj1).length_le) :=
    (hpre _ _ hj1).getElem (hidx k)
  have e2 : g k' = (F (max (idx k) (idx k')))[k']'(Nat.lt_of_lt_of_le (hidx k') (hpre _ _ hj2).length_le) :=
    (hpre _ _ hj2).getElem (hidx k')
  rw [e1, e2]
  exact List.pairwise_iff_getElem.mp (hpw _) k k' _ _ hkk'

end Lists

/-! ### Along growing sequences -/

section Seq

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ} {𝔪 : MarkedIdeal n X}

/-- Along a growing sequence the lists of centre values grow by prefixes. -/
theorem centreValues_isPrefix_succ {Λ' : Type v} [LinearOrder Λ'] (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ') (s : GrowingSeq X)
    (i : ℕ) : centreValues inv (s.stage i).2 <+: centreValues inv (s.stage (i + 1)).2 := by
  obtain ⟨C, π, hπ, heq⟩ := s.succ i
  rw [heq]
  by_cases hne : C.Nonempty
  · rw [centreValues_step_of_nonempty _ _ C π hπ hne]
    exact List.prefix_append _ _
  · rw [centreValues_step_of_eq_empty _ _ C π hπ (not_nonempty_iff_eq_empty.mp hne)]

end Seq

end

end Hironaka.GeneralPhaseCount
