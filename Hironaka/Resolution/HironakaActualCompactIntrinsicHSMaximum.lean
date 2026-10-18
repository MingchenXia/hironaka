/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualReferenceHSSingularCentre
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.PiLex

/-! Internally attained actual all-order intrinsic HS maxima on original compact carriers. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCompactIntrinsicHSMaximum
noncomputable section

/-- Actual countably many upper semicontinuous coordinates attain a true lexicographic maximum by compactness. -/
theorem exists_actual_compact_countable_usc_lexmax {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X] (f : X → ℕ → ℕ)
    (hf : ∀ i, UpperSemicontinuous (fun x => f x i)) :
    ∃ y : X, (∀ x, ¬ Pi.Lex (· < ·) (· < ·) (f y) (f x)) ∧
      ∀ x, (∀ i, f y i ≤ f x i) ↔ ∀ i, f x i = f y i := by
  let S := {s : Set X // IsClosed s ∧ IsCompact s ∧ s.Nonempty}
  let a (i : ℕ) (s : S) : X :=
    Classical.choose (UpperSemicontinuousOn.exists_isMaxOn s.2.2.2 s.2.2.1 ((hf i).upperSemicontinuousOn s.1))
  have ha (i : ℕ) (s : S) : a i s ∈ s.1 ∧ IsMaxOn (fun x => f x i) s.1 (a i s) :=
    Classical.choose_spec (UpperSemicontinuousOn.exists_isMaxOn s.2.2.2 s.2.2.1 ((hf i).upperSemicontinuousOn s.1))
  let next (i : ℕ) (s : S) : S :=
    ⟨s.1 ∩ {x | f (a i s) i ≤ f x i},
      s.2.1.inter ((hf i).isClosed_preimage _),
      s.2.2.1.inter_right ((hf i).isClosed_preimage _),
      ⟨a i s,(ha i s).1,by change f (a i s) i ≤ f (a i s) i; exact le_rfl⟩⟩
  let sets : ℕ → S := Nat.rec ⟨univ,isClosed_univ,isCompact_univ,Set.univ_nonempty⟩ next
  have hstep (i : ℕ) : (sets (i+1)).1 ⊆ (sets i).1 := fun _ hx => hx.1
  obtain ⟨y,hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun i => (sets i).1) hstep (fun i => (sets i).2.2.2) (sets 0).2.2.1 (fun i => (sets i).2.1)
  have hym (i : ℕ) : y ∈ (sets i).1 := mem_iInter.mp hy i
  have hmax (i : ℕ) (x : X) (hx : x ∈ (sets i).1) : f x i ≤ f y i :=
    ((ha i (sets i)).2 hx).trans ((hym (i+1)).2)
  have hprefix (i : ℕ) (x : X) (hx : ∀ j < i, f x j = f y j) : x ∈ (sets i).1 := by
    induction i with
    | zero => exact mem_univ x
    | succ i ih =>
      refine ⟨ih (fun j hj => hx j (by omega)),?_⟩
      change f (a i (sets i)) i ≤ f x i
      rw [hx i (Nat.lt_succ_self i)]
      exact (hym (i+1)).2
  refine ⟨y,?_,?_⟩
  · intro x
    rintro ⟨i,hpre,hlt⟩
    exact (not_lt_of_ge (hmax i x (hprefix i x (fun j hj => (hpre j hj).symm)))) hlt
  · intro x
    constructor
    · intro hx i
      induction i using Nat.strong_induction_on with
      | h i ih => exact le_antisymm (hmax i x (hprefix i x ih)) (hx i)
    · intro hx i
      exact (hx i).ge

open Hironaka.HolomorphicIdealSheaves
  HironakaHolomorphicJetChartInvariance HironakaActualWholeAmbientHSSuperlevel
  HironakaActualReferenceHSSingularCentre
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Original coherence gives true upper semicontinuity of the EXISTING intrinsic HS at EVERY order. -/
theorem actual_intrinsic_hs_upperSemicontinuous (A : GermIdeal n M) (hA : A.IsCoherent) (i : ℕ) :
    UpperSemicontinuous (fun x => hilbertSamuelAt A x i) :=
  upperSemicontinuous_iff_isClosed_preimage.mpr
    (fun r => (isComplexAnalyticSubset_hilbertSamuelAt_superlevel A hA i r).isClosed)

/-- ONLY original coherence and actual compactness choose the actual whole-profile maximum and BOTH constant-locus directions. -/
theorem exists_actual_original_compact_hs_maximum (A : GermIdeal n M) (hA : A.IsCoherent)
    {K : Set M} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ y ∈ K, (∀ x ∈ K, ¬ Pi.Lex (· < ·) (· < ·) (hilbertSamuelAt A y) (hilbertSamuelAt A x)) ∧
      ∀ x ∈ K, (∀ i, hilbertSamuelAt A y i ≤ hilbertSamuelAt A x i) ↔
        ∀ i, hilbertSamuelAt A x i = hilbertSamuelAt A y i := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : Nonempty K := hne.to_subtype
  have hf (i : ℕ) : UpperSemicontinuous (fun x : K => hilbertSamuelAt A x i) :=
    upperSemicontinuous_iff_isClosed_preimage.mpr (fun r =>
      (isComplexAnalyticSubset_hilbertSamuelAt_superlevel A hA i r).isClosed.preimage continuous_subtype_val)
  obtain ⟨y,hy,hconst⟩ := exists_actual_compact_countable_usc_lexmax
    (fun x : K => hilbertSamuelAt A x) hf
  exact ⟨y,y.2,(fun x hx => hy ⟨x,hx⟩),fun x hx => hconst ⟨x,hx⟩⟩

/-- The actual whole ambient maximal threshold is internally analytic, compact and EXACTLY the full constant reduced HS locus. -/
theorem exists_actual_original_compact_reduced_constant_maximal_hs_locus
    {W : Set M} (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) (hne : W.Nonempty) :
    ∃ y ∈ W,
      (∀ x ∈ W, ¬ Pi.Lex (· < ·) (· < ·)
        (hilbertSamuelAt (vanishingIdeal (n := n) W) y) (hilbertSamuelAt (vanishingIdeal (n := n) W) x)) ∧
      (actualReferenceHSLocus (vanishingIdeal (n := n) W) y).Nonempty ∧
      IsComplexAnalyticSubset (n := n) (actualReferenceHSLocus (vanishingIdeal (n := n) W) y) ∧
      IsCompact (actualReferenceHSLocus (vanishingIdeal (n := n) W) y) ∧
      actualReferenceHSLocus (vanishingIdeal (n := n) W) y =
        {x | x ∈ W ∧ ∀ i, hilbertSamuelAt (vanishingIdeal (n := n) W) x i =
          hilbertSamuelAt (vanishingIdeal (n := n) W) y i} := by
  let A := vanishingIdeal (n := n) W
  have hA : A.IsCoherent := CartanIrreducible.cartanCoherence W hW
  have hz : A.zeroLocus = W := BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hW.isClosed
  obtain ⟨y,hy,hmax,hconst⟩ := exists_actual_original_compact_hs_maximum A hA hK hne
  have hy0 : hilbertSamuelAt A y 0 = 1 := by
    rw [hilbertSamuelAt_zero_eq_support A hA y,hz,if_pos hy]
  have hsub : actualReferenceHSLocus A y ⊆ W := by
    intro x hx
    have hh : 1 ≤ hilbertSamuelAt A x 0 := hy0 ▸ hx 0
    exact hz ▸ (one_le_hilbertSamuelAt_zero_iff A hA x).mp hh
  have ha := isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel A hA (hilbertSamuelAt A y)
  refine ⟨y,hy,hmax,⟨y,fun _ => le_rfl⟩,ha,hK.of_isClosed_subset ha.isClosed hsub,?_⟩
  ext x
  constructor
  · intro hx
    exact ⟨hsub hx,(hconst x (hsub hx)).mp hx⟩
  · rintro ⟨hx,hprof⟩
    exact (hconst x hx).mpr hprof

end
end Hironaka.HironakaActualCompactIntrinsicHSMaximum
