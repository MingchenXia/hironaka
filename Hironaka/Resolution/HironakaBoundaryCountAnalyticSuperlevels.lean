/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaOrderTupleAnalyticSuperlevels

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

/-!
# Genuine globally analytic boundary-count superlevels

The indexed finite intersection dictionary constructs global analytic
superlevels and applies them to the actual original-boundary level and
masked StepOne invariant. Higher history entries and global G3 remain open.
Blueprint: `hironaka-boundary-count-superlevels-extension.tex`.
-/

open Set
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaBoundaryCountAnalyticSuperlevels

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BoundaryCount MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  NormalCrossings StepOneValue StepOneLowerDomain

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The actual indexed count superlevel is exactly its finite union of
intersections, including zero and excessive thresholds and repeated members. -/
theorem boundaryCount_superlevel_eq_biUnion (E : List (Set M)) (s : ℕ) :
    {x | s ≤ boundaryCount E x} =
      ⋃ S ∈ (Finset.univ : Finset (Fin E.length)).powersetCard s, memberInter E S := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hx
    refine mem_iUnion₂.mpr ⟨S, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hScard⟩
    · intro i hi
      exact (Finset.mem_filter.mp (hSsub hi)).2
  · intro hx
    obtain ⟨S, hS, hxS⟩ := mem_iUnion₂.mp hx
    have hScard := (Finset.mem_powersetCard.mp hS).2
    have hsub : S ⊆ Finset.univ.filter (fun i : Fin E.length => x ∈ E.get i) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxS i hi⟩
    change s ≤ (Finset.univ.filter (fun i : Fin E.length => x ∈ E.get i)).card
    rw [← hScard]
    exact Finset.card_le_card hsub

private theorem isComplexAnalyticSubset_memberInter (E : List (Set M))
    (hE : ∀ H ∈ E, IsComplexAnalyticSubset (n := n) H)
    (S : Finset (Fin E.length)) : IsComplexAnalyticSubset (n := n) (memberInter E S) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [memberInter]
  | insert i S hi ih =>
    have heq : memberInter E (insert i S) = E.get i ∩ memberInter E S := by
      ext x
      simp [memberInter]
    rw [heq]
    exact (hE _ (List.get_mem E i)).inter ih

private theorem isComplexAnalyticSubset_finset_union {ι : Type*} (t : Finset ι)
    (A : ι → Set M) (hA : ∀ i ∈ t, IsComplexAnalyticSubset (n := n) (A i)) :
    IsComplexAnalyticSubset (n := n) (⋃ i ∈ t, A i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.set_biUnion_insert]
    exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
      (hA i (Finset.mem_insert_self i t))
      (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)))

/-- Actual analytic members produce every global indexed-count superlevel. -/
theorem isComplexAnalyticSubset_boundaryCount_superlevel (E : List (Set M))
    (hE : ∀ H ∈ E, IsComplexAnalyticSubset (n := n) H) (s : ℕ) :
    IsComplexAnalyticSubset (n := n) {x | s ≤ boundaryCount E x} := by
  rw [boundaryCount_superlevel_eq_biUnion]
  exact isComplexAnalyticSubset_finset_union _ (memberInter E)
    (fun S _ => isComplexAnalyticSubset_memberInter E hE S)

section ActualStepOne

universe u v
variable {k : ℕ} {X Y : CMfd.{u} n}

/-- Genuine transformed SNC geometry supplies the original-member level's
global analytic superlevels along every actual admissible test tower. -/
theorem isComplexAnalyticSubset_stepOne_level_superlevel (hn : 0 < n)
    (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T) (s : ℕ) :
    IsComplexAnalyticSubset (n := n) {y | s ≤ level 𝔍 T y} := by
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked 𝔍 h𝔍) T hT
  have hE : IsSNCDivisor n (origMembers 𝔍 T) :=
    NormalCrossingsComparison.isSNCDivisor_of_sublist hwf.isSNCDivisor
    (List.take_sublist 𝔍.E.length (geoTransformAlong (barMarked 𝔍) T).E)
  apply isComplexAnalyticSubset_boundaryCount_superlevel (origMembers 𝔍 T) _ s
  intro H hH
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hH
  have hinter := isClosedSubmanifold_memberInter hn hE {i}
  have heq : memberInter (origMembers 𝔍 T) {i} = H := by
    ext y
    simp only [memberInter, mem_ofPred_eq, Finset.mem_singleton, forall_eq]
    rw [hi]
  rw [heq] at hinter
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hinter

/-- The genuine masked StepOne invariant's first entry is its actual level,
so its analytic superlevels require no caller-supplied tuple presentation. -/
theorem isComplexAnalyticSubset_stepOneInvM_first_superlevel
    {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    (hn : 0 < n) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T) (s : ℕ) :
    IsComplexAnalyticSubset (n := n)
      {y | s ≤ (ofLex (Seq.StepOneValueMasked.stepOneInvM R 𝔍 T y)).1} := by
  have heq : {y | s ≤ (ofLex (Seq.StepOneValueMasked.stepOneInvM R 𝔍 T y)).1} =
      {y | s ≤ level 𝔍 T y} := by
    ext y
    change (s ≤ (ofLex (Seq.StepOneValueMasked.stepOneInvL R 𝔍
      (StepOneValueMasked.lowerMarkedM 𝔍) T y)).1) ↔ s ≤ level 𝔍 T y
    rw [Seq.StepOneValueMasked.stepOneInvL_fst]
  rw [heq]
  exact isComplexAnalyticSubset_stepOne_level_superlevel hn 𝔍 h𝔍 T hT s

end ActualStepOne

end
end Hironaka.HironakaBoundaryCountAnalyticSuperlevels
