/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ResolutionInvariantSegments

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.ResolutionInvariantSegments
open Hironaka
noncomputable section
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.ResolutionInvariantSpec
variable {n : ℕ} {X : CMfd.{u} n}

/-- No centre meets the preimage of the empty set. -/
theorem countCentresMeeting_empty : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    countCentresMeeting (∅ : Set X) T = 0
  | _, .refl => rfl
  | _, .step T C π hπ => by
      have h : ¬ (C ∩ T.proj ⁻¹' (∅ : Set X)).Nonempty := by
        rw [preimage_empty, inter_empty]
        exact not_nonempty_empty
      simp only [countCentresMeeting, countCentresMeeting_empty T, if_neg h]

/-- **The count is monotone in `K`.** -/
theorem countCentresMeeting_mono {K K' : Set X} (hK : K ⊆ K') : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    countCentresMeeting K T ≤ countCentresMeeting K' T
  | _, .refl => le_rfl
  | _, .step T C π hπ => by
      have ih := countCentresMeeting_mono hK T
      have hsub : C ∩ T.proj ⁻¹' K ⊆ C ∩ T.proj ⁻¹' K' := inter_subset_inter_right _ (preimage_mono hK)
      simp only [countCentresMeeting]
      by_cases h1 : (C ∩ T.proj ⁻¹' K).Nonempty
      · rw [if_pos h1, if_pos (h1.mono hsub)]
        omega
      · rw [if_neg h1]
        split_ifs <;> omega

/-- **The count is subadditive in `K`.** -/
theorem countCentresMeeting_union_le (K K' : Set X) : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    countCentresMeeting (K ∪ K') T ≤ countCentresMeeting K T + countCentresMeeting K' T
  | _, .refl => le_rfl
  | _, .step T C π hπ => by
      have ih := countCentresMeeting_union_le K K' T
      simp only [countCentresMeeting]
      by_cases h : (C ∩ T.proj ⁻¹' (K ∪ K')).Nonempty
      · rw [if_pos h]
        rw [preimage_union, inter_union_distrib_left] at h
        rcases union_nonempty.mp h with h1 | h2
        · rw [if_pos h1]
          split_ifs <;> omega
        · rw [if_pos h2]
          split_ifs <;> omega
      · rw [if_neg h]
        split_ifs <;> omega

/-- **The count is finitely subadditive**: for finitely many sets `K i`, the centres meeting the preimage of their union
are at most the sum of the counts. -/
theorem countCentresMeeting_biUnion_le {ι : Type*} (s : Finset ι) (K : ι → Set X) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) : countCentresMeeting (⋃ i ∈ s, K i) T ≤ ∑ i ∈ s, countCentresMeeting (K i) T := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, Finset.sum_empty]
    exact (countCentresMeeting_empty T).le
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (countCentresMeeting_union_le _ _ T).trans (Nat.add_le_add_left ih _)

open Classical in
/-- **Counting along a restricted tower**: the nonempty centres of `T|_U` meeting the preimage of `K ∩ U` are the traces
of the centres of `T` meeting the preimage of `K ∩ U`. -/
theorem countCentresMeeting_restrict (U : Opens X) (K : Set X) : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    countCentresMeeting ((Subtype.val : U → X) ⁻¹' K) (restrict U T) = countCentresMeeting (K ∩ U) T
  | _, .refl => rfl
  | _, .step T C π hπ => by
      have ih := countCentresMeeting_restrict U K T
      have hiff : (((Subtype.val : openPreimage T U → _) ⁻¹' C) ∩
          (restrict U T).proj ⁻¹' ((Subtype.val : U → X) ⁻¹' K)).Nonempty ↔
          (C ∩ T.proj ⁻¹' (K ∩ (U : Set X))).Nonempty := by
        constructor
        · rintro ⟨p, hpC, hpK⟩
          refine ⟨p.1, hpC, ?_, p.2⟩
          have := proj_restrict U T p
          simp only [mem_preimage] at hpK
          rw [this] at hpK
          exact hpK
        · rintro ⟨y, hyC, hyK, hyU⟩
          refine ⟨⟨y, hyU⟩, hyC, ?_⟩
          simp only [mem_preimage]
          rw [proj_restrict U T ⟨y, hyU⟩]
          exact hyK
      show countCentresMeeting ((Subtype.val : U → X) ⁻¹' K) (restrict U T) +
          (if (((Subtype.val : openPreimage T U → _) ⁻¹' C) ∩
            (restrict U T).proj ⁻¹' ((Subtype.val : U → X) ⁻¹' K)).Nonempty then 1 else 0) =
        countCentresMeeting (K ∩ U) T + (if (C ∩ T.proj ⁻¹' (K ∩ (U : Set X))).Nonempty then 1 else 0)
      rw [ih]
      by_cases h : (C ∩ T.proj ⁻¹' (K ∩ (U : Set X))).Nonempty
      · rw [if_pos h, if_pos (hiff.mpr h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]

/-- For `K ⊆ U` the count along `T|_U` is the count along `T`. -/
theorem countCentresMeeting_restrict_of_subset (U : Opens X) {K : Set X} (hKU : K ⊆ U) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) :
    countCentresMeeting ((Subtype.val : U → X) ⁻¹' K) (restrict U T) = countCentresMeeting K T := by
  rw [countCentresMeeting_restrict, inter_eq_left.mpr hKU]

end
end Hironaka.ResolutionInvariantSegments
