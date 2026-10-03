/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneWellFounded
import Hironaka.Blowup.BlowupSequences
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantSpec
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The values of the nonempty centres of a canonical segment; the phases of the Step 1 value

Sources: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 1 (Step 1a lowers the number `s`
of original members through the points of the cosupport, one phase per value of `s`; Step 1aa and Step 1ba blow up
the points of value `(s, ∞)`); Bierstone--Milman 2008 §7.

Along a tower `T` and for a value function `inv`, `centreValues inv T` lists, in order, the value of `inv` at (a
point of) each nonempty centre of `T`; on a canonical segment such a centre is the maximum locus, so the entry is
the maximum of the value on the cosupport at that stage. If one step of a canonical segment never raises a value and
lowers the values over its centre (`StepOneWellFounded.StepDrop`, properties (3) and (4) of `hir:centre-function`),
then **the values of the nonempty centres strictly decrease, and every value on the last cosupport lies below all of
them** (`pairwise_centreValues`). The list of a prefix is a prefix of the list, so along a growing sequence of
canonical segments the values of all nonempty centres form one strictly decreasing sequence.

For the masked Step 1 value `stepOneInvM R 𝔍` (marked ideals of the domain of maximal order) this is the **phase
bookkeeping** of property (8), which does not depend on the form chosen for (8): the first entries (the levels `s`)
of the values of the nonempty centres do not increase and are at most `#E`; each special value `(s, ∞)` occurs at
most once, so at most `#E + 1` nonempty centres have a special value; the number of nonempty centres is the sum over
the phases `s = 0, …, #E`, and inside the phase `s` the lower values of the non-special centres strictly decrease.
What is left for (8) is a bound, in each phase, on such decreasing sequences of lower values: that is where the
lower-dimensional invariant's own (8) enters.

## Main results

* `centreValues`, `centreValues_step_of_nonempty`, `centreValues_step_of_eq_empty`;
* `length_centreValues`, `countCentresMeeting_le_length_centreValues`: the length is the number of nonempty centres;
* **`pairwise_centreValues`**: under `StepDrop`, along canonical segments;
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOnePhase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneValue Hironaka.StepOneValueMasked Hironaka.StepOneWellFounded Hironaka.BoundaryCount Hironaka.HomogenizedIdealAlong
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)

noncomputable section

variable {n : ℕ}

/-! ### The values of the nonempty centres -/

section Generic

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

variable (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) in
open Classical in
/-- **The values of the nonempty centres of a tower**, in order: for each step along a nonempty centre `C` after `T`, the value
of `inv T` at a point of `C` (on a canonical segment `C` is then the maximum locus, and the entry is the maximum). -/
def centreValues : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → List Λ
  | _, .refl => []
  | _, .step T C _ _ => centreValues T ++ if h : C.Nonempty then [inv T h.some] else []

variable (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)

@[simp] theorem centreValues_refl : centreValues inv (BlowupTower.refl : BlowupTower X X) = [] := rfl

theorem centreValues_step_of_nonempty {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (h : C.Nonempty) :
    centreValues inv (.step T C π hπ) = centreValues inv T ++ [inv T h.some] := by
  classical
  show (centreValues inv T ++ if h : C.Nonempty then [inv T h.some] else []) = _
  rw [dif_pos h]

theorem centreValues_step_of_eq_empty {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (h : C = ∅) : centreValues inv (.step T C π hπ) = centreValues inv T := by
  classical
  show (centreValues inv T ++ if h : C.Nonempty then [inv T h.some] else []) = _
  rw [dif_neg (by rw [h]; exact not_nonempty_empty), List.append_nil]

/-- **The length of the list is the number of nonempty centres.** -/
theorem length_centreValues :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), (centreValues inv T).length = countCentresMeeting (univ : Set X) T
  | _, .refl => rfl
  | _, .step T C π hπ => by
      classical
      show (centreValues inv (.step T C π hπ)).length =
        countCentresMeeting (univ : Set X) T + if (C ∩ T.proj ⁻¹' (univ : Set X)).Nonempty then 1 else 0
      rw [preimage_univ, inter_univ]
      by_cases h : C.Nonempty
      · rw [centreValues_step_of_nonempty inv T C π hπ h, List.length_append, length_centreValues T, if_pos h]
        rfl
      · rw [centreValues_step_of_eq_empty inv T C π hπ (not_nonempty_iff_eq_empty.mp h), length_centreValues T,
          if_neg h]
        rfl

/-- The nonempty centres meeting the preimage of `K` are at most the nonempty centres. -/
theorem countCentresMeeting_le_countCentresMeeting_univ (K : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), countCentresMeeting K T ≤ countCentresMeeting (univ : Set X) T
  | _, .refl => le_rfl
  | _, .step T C π hπ => by
      classical
      show countCentresMeeting K T + (if (C ∩ T.proj ⁻¹' K).Nonempty then 1 else 0) ≤
        countCentresMeeting (univ : Set X) T + if (C ∩ T.proj ⁻¹' (univ : Set X)).Nonempty then 1 else 0
      have ih := countCentresMeeting_le_countCentresMeeting_univ K T
      by_cases h : (C ∩ T.proj ⁻¹' K).Nonempty
      · have h' : (C ∩ T.proj ⁻¹' (univ : Set X)).Nonempty := h.mono (inter_subset_inter_right _ (preimage_mono
          (subset_univ K)))
        rw [if_pos h, if_pos h']
        omega
      · rw [if_neg h]
        split_ifs <;> omega

/-- The nonempty centres meeting the preimage of `K` are at most the length of the list. -/
theorem countCentresMeeting_le_length_centreValues (K : Set X) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    countCentresMeeting K T ≤ (centreValues inv T).length := by
  rw [length_centreValues]
  exact countCentresMeeting_le_countCentresMeeting_univ K T

variable {𝔪 : MarkedIdeal n X} {inv}

/-- The two halves of the induction: strictly decreasing, and above every value on the last cosupport. -/
theorem pairwise_and_lt_centreValues (hdrop : StepDrop 𝔪 inv) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 inv T →
      (centreValues inv T).Pairwise (fun a b => b < a) ∧
        ∀ a ∈ centreValues inv T, ∀ z ∈ (geoTransformAlong 𝔪 T).cosupp, inv T z < a
  | _, .refl, _ => ⟨List.Pairwise.nil, fun a ha => by simp at ha⟩
  | _, .step T C π hπ, hcan => by
      have hT : IsCanonical 𝔪 inv T := hcan.1
      have hC : C = ∅ ∨ C = maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp := hcan.2
      have ih := pairwise_and_lt_centreValues hdrop T hT
      -- one step: a point of the new cosupport lies over the old one, with a value at most that of its image
      have hstep : ∀ z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp,
          π z ∈ (geoTransformAlong 𝔪 T).cosupp ∧ inv (.step T C π hπ) z ≤ inv T (π z) := by
        intro z hz
        obtain ⟨hpz, h1, h2⟩ := hdrop T C π hπ hcan z hz
        refine ⟨hpz, ?_⟩
        by_cases hzC : π z ∈ C
        · exact (h1 hzC).le
        · exact (h2 hzC).le
      have hold : ∀ a ∈ centreValues inv T, ∀ z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp,
          inv (.step T C π hπ) z < a := fun a ha z hz =>
        (hstep z hz).2.trans_lt (ih.2 a ha _ (hstep z hz).1)
      by_cases hne : C.Nonempty
      · have hCm : C = maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp := hC.resolve_left hne.ne_empty
        have hsome : hne.some ∈ maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp := hCm ▸ hne.some_mem
        rw [centreValues_step_of_nonempty inv T C π hπ hne]
        refine ⟨List.pairwise_append.mpr ⟨ih.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩, ?_⟩
        · rw [List.mem_singleton] at hb
          rw [hb]
          exact ih.2 a ha _ hsome.1
        · intro a ha z hz
          rcases List.mem_append.mp ha with ha | ha
          · exact hold a ha z hz
          · rw [List.mem_singleton] at ha
            rw [ha]
            obtain ⟨hpz, h1, h2⟩ := hdrop T C π hπ hcan z hz
            exact lt_of_mem_maxLocus hsome hpz
              ⟨fun hm => h1 (by rw [hCm]; exact hm), fun hm => h2 fun hc => hm (by rw [← hCm]; exact hc)⟩
      · rw [centreValues_step_of_eq_empty inv T C π hπ (not_nonempty_iff_eq_empty.mp hne)]
        exact ⟨ih.1, hold⟩

/-- **The values of the nonempty centres of a canonical segment strictly decrease** (under `StepDrop`). -/
theorem pairwise_centreValues (hdrop : StepDrop 𝔪 inv) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical 𝔪 inv T) : (centreValues inv T).Pairwise (fun a b => b < a) :=
  (pairwise_and_lt_centreValues hdrop T hcan).1

end Generic

end

end Hironaka.StepOnePhase
