/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.AnalyticDescendingLocalStableExact
import Hironaka.Resolution.HironakaHolomorphicJetChartInvariance
import Hironaka.Analytic.AnalyticDescendingChain
import Hironaka.Coherence.CartanIrreducible
import Hironaka.Blowup.BlowupExceptionalDivisor

/-! Genuine COORDINATEWISE all-order original ambient HS conditions have finite local equations. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualWholeAmbientHSSuperlevel
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaHolomorphicJetChartInvariance AnalyticDescendingChain
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal COORDINATEWISE whole original intrinsic ambient HS condition retains EVERY actual order. -/
def actualWholeAmbientHSSuperlevel (A : GermIdeal n M) (h : ℕ → ℕ) : Set M :=
  {y | ∀ ℓ : ℕ, h ℓ ≤ hilbertSamuelAt A y ℓ}

/-- Genuine finite prefixes intersect the SAME original intrinsic HS inequalities. -/
def actualAmbientHSFinitePrefix (A : GermIdeal n M) (h : ℕ → ℕ) : ℕ → Set M
  | 0 => {y | h 0 ≤ hilbertSamuelAt A y 0}
  | k+1 => actualAmbientHSFinitePrefix A h k ∩ {y | h (k+1) ≤ hilbertSamuelAt A y (k+1)}

/-- BOTH true finite-prefix membership directions retain all original orders through the same cutoff. -/
theorem mem_actualAmbientHSFinitePrefix (A : GermIdeal n M) (h : ℕ → ℕ) (k : ℕ) (y : M) :
    y ∈ actualAmbientHSFinitePrefix A h k ↔ ∀ ℓ ≤ k, h ℓ ≤ hilbertSamuelAt A y ℓ := by
  induction k with
  | zero => simp [actualAmbientHSFinitePrefix]
  | succ k ih =>
    change (y ∈ actualAmbientHSFinitePrefix A h k ∧ h (k+1) ≤ hilbertSamuelAt A y (k+1)) ↔ _
    constructor
    · intro hy ℓ hℓ
      by_cases he : ℓ = k+1
      · subst ℓ
        exact hy.2
      · exact ih.mp hy.1 ℓ (by omega)
    · intro hy
      exact ⟨ih.mpr (fun ℓ hℓ => hy ℓ (by omega)),hy (k+1) le_rfl⟩

/-- ONLY original coherence makes each genuine intrinsic HS finite prefix globally complex analytic. -/
theorem isComplexAnalyticSubset_actualAmbientHSFinitePrefix
    (A : GermIdeal n M) (hA : A.IsCoherent) (h : ℕ → ℕ) (k : ℕ) :
    IsComplexAnalyticSubset (n := n) (actualAmbientHSFinitePrefix A h k) := by
  induction k with
  | zero => exact isComplexAnalyticSubset_hilbertSamuelAt_superlevel A hA 0 (h 0)
  | succ k ih =>
    exact ih.inter (isComplexAnalyticSubset_hilbertSamuelAt_superlevel A hA (k+1) (h (k+1)))

/-- The SAME literal actual finite-prefix family is genuinely descending on the whole original manifold. -/
theorem actualAmbientHSFinitePrefix_antitone (A : GermIdeal n M) (h : ℕ → ℕ) :
    Antitone (actualAmbientHSFinitePrefix A h) :=
  antitone_nat_of_succ_le (fun _ => inter_subset_left)

/-- Literal all-order original HS membership implies EVERY true finite prefix. -/
theorem actualWholeAmbientHSSuperlevel_subset_prefix (A : GermIdeal n M) (h : ℕ → ℕ) (k : ℕ) :
    actualWholeAmbientHSSuperlevel A h ⊆ actualAmbientHSFinitePrefix A h k :=
  fun y hy => (mem_actualAmbientHSFinitePrefix A h k y).mpr (fun ℓ _ => hy ℓ)

/-- Original coherence INTERNALLY supplies ONE true neighborhood and finite order for the WHOLE all-order condition. -/
theorem exists_original_local_whole_ambient_hs_prefix
    (A : GermIdeal n M) (hA : A.IsCoherent) (h : ℕ → ℕ) (x : M) :
    ∃ k : ℕ, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      actualWholeAmbientHSSuperlevel A h ∩ U = actualAmbientHSFinitePrefix A h k ∩ U := by
  obtain ⟨k,U,hU,hx,hstable⟩ := exists_local_stable
    (isComplexAnalyticSubset_actualAmbientHSFinitePrefix A hA h)
    (actualAmbientHSFinitePrefix_antitone A h) x
  refine ⟨k,U,hU,hx,Subset.antisymm ?_ ?_⟩
  · exact fun y hy => ⟨actualWholeAmbientHSSuperlevel_subset_prefix A h k hy.1,hy.2⟩
  · intro y hy
    refine ⟨fun ℓ => ?_,hy.2⟩
    have hcut : y ∈ actualAmbientHSFinitePrefix A h (max k ℓ) ∩ U :=
      (hstable (max k ℓ) (Nat.le_max_left k ℓ)).symm ▸ hy
    exact (mem_actualAmbientHSFinitePrefix A h (max k ℓ) y).mp hcut.1 ℓ (Nat.le_max_right k ℓ)

/-- ONLY original coherence makes the literal WHOLE coordinatewise all-order original intrinsic HS condition analytic. -/
theorem isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel
    (A : GermIdeal n M) (hA : A.IsCoherent) (h : ℕ → ℕ) :
    IsComplexAnalyticSubset (n := n) (actualWholeAmbientHSSuperlevel A h) := by
  intro x
  obtain ⟨k,U,hU,hxU,hEq⟩ := exists_original_local_whole_ambient_hs_prefix A hA h x
  obtain ⟨P⟩ := isComplexAnalyticSubset_actualAmbientHSFinitePrefix A hA h k x
  let e := (complexChartAt (n := n) x).val
  have hxs : x ∈ e.source := mem_complexChartAt_source x
  refine ⟨{
    generatorCount := P.generatorCount
    generator := P.generator
    coordinateNeighborhood := P.coordinateNeighborhood ∩ (e.target ∩ e.symm ⁻¹' U)
    isOpen_coordinateNeighborhood := P.isOpen_coordinateNeighborhood.inter
      (e.isOpen_inter_preimage_symm hU)
    center_mem_coordinateNeighborhood := ⟨P.center_mem_coordinateNeighborhood,
      e.map_source hxs,by
        change e.symm (e x) ∈ U
        rw [e.left_inv hxs]
        exact hxU⟩
    coordinateNeighborhood_subset_target := fun _ hz => hz.2.1
    generator_holomorphic := fun i => (P.generator_holomorphic i).mono inter_subset_left
    zeroLocus := ?_ }⟩
  intro y hy hyV
  have hyU : y ∈ U := by
    have hh : e.symm (e y) ∈ U := hyV.2.2
    rwa [e.left_inv hy] at hh
  rw [← P.zeroLocus hy hyV.1]
  constructor
  · intro hyWhole
    exact ((hEq ▸ (⟨hyWhole,hyU⟩ : y ∈ actualWholeAmbientHSSuperlevel A h ∩ U)) :
      y ∈ actualAmbientHSFinitePrefix A h k ∩ U).1
  · intro hyFinite
    exact ((hEq.symm ▸ (⟨hyFinite,hyU⟩ : y ∈ actualAmbientHSFinitePrefix A h k ∩ U)) :
      y ∈ actualWholeAmbientHSSuperlevel A h ∩ U).1

/-- EVERY actual compact window has ONE true finite cutoff for the SAME whole original HS condition. -/
theorem exists_original_compact_window_whole_ambient_hs_prefix
    (A : GermIdeal n M) (hA : A.IsCoherent) (h : ℕ → ℕ)
    (K : Set M) (hK : IsCompact K) :
    ∃ k : ℕ, ∀ y ∈ K,
      y ∈ actualWholeAmbientHSSuperlevel A h ↔ y ∈ actualAmbientHSFinitePrefix A h k := by
  classical
  choose k U hU hxU hEq using exists_original_local_whole_ambient_hs_prefix A hA h
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU (fun y _ => mem_iUnion.mpr ⟨y,hxU y⟩)
  refine ⟨s.sup k,?_⟩
  intro y hyK
  constructor
  · exact fun hy => actualWholeAmbientHSSuperlevel_subset_prefix A h (s.sup k) hy
  · intro hyPrefix
    obtain ⟨x,hxs,hyU⟩ := mem_iUnion₂.mp (hs hyK)
    have hxy : y ∈ actualAmbientHSFinitePrefix A h (k x) :=
      actualAmbientHSFinitePrefix_antitone A h (Finset.le_sup hxs) hyPrefix
    have hpair : y ∈ actualWholeAmbientHSSuperlevel A h ∩ U x :=
      (Set.ext_iff.mp (hEq x) y).mpr ⟨hxy,hyU⟩
    exact hpair.1

/-- The literal WHOLE original HS locus has its genuine coherent original vanishing ideal. -/
theorem actualWholeAmbientHSSuperlevel_isCoherent
    (A : GermIdeal n M) (hA : A.IsCoherent) (h : ℕ → ℕ) :
    (vanishingIdeal (n := n) (actualWholeAmbientHSSuperlevel A h)).IsCoherent :=
  CartanIrreducible.cartanCoherence _ (isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel A hA h)

/-- The SAME actual ideal cuts out precisely the literal all-order original intrinsic HS condition. -/
theorem actualWholeAmbientHSSuperlevel_zeroLocus
    (A : GermIdeal n M) (hA : A.IsCoherent) (h : ℕ → ℕ) :
    (vanishingIdeal (n := n) (actualWholeAmbientHSSuperlevel A h)).zeroLocus =
      actualWholeAmbientHSSuperlevel A h :=
  BlowupExceptionalDivisor.zeroLocus_vanishingIdeal
    (isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel A hA h).isClosed

/-- Genuine original finite holomorphic generators give BOTH nearby ideal/span directions and the SAME literal all-order equations. -/
theorem exists_original_whole_ambient_hs_generators
    (A : GermIdeal n M) (hA : A.IsCoherent) (h : ℕ → ℕ) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ (N : ℕ) (f : Fin N → M → ℂ),
      (∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (f i) U) ∧
      (∀ y ∈ U, ∀ g, (vanishingIdeal (n := n) (actualWholeAmbientHSSuperlevel A h)).mem y g ↔
        IsInSpanAt (n := n) (· ∈ range f) y g) ∧
      ∀ y ∈ U, (∀ ℓ : ℕ, h ℓ ≤ hilbertSamuelAt A y ℓ) ↔ ∀ i, f i y = 0 := by
  obtain ⟨U,hU,hxU,N,f,hf,hgen⟩ := actualWholeAmbientHSSuperlevel_isCoherent A hA h x
  refine ⟨U,hU,hxU,N,f,hf,hgen,?_⟩
  intro y hy
  change y ∈ actualWholeAmbientHSSuperlevel A h ↔ _
  rw [← actualWholeAmbientHSSuperlevel_zeroLocus A hA h]
  constructor
  · intro hz i
    have hol : HolomorphicAt n (f i) y := eventually_of_mem (hU.mem_nhds hy)
      (fun z hz => (hf i z hz).mdifferentiableAt (hU.mem_nhds hz))
    apply hz (f i)
    apply (hgen y hy (f i)).mpr
    exact isInSpanAt_of_eq_mul ⟨i,rfl⟩ hol (holomorphicAt_const 1)
      (Eventually.of_forall fun z => (one_mul (f i z)).symm)
  · intro hz g hg
    obtain ⟨_,L,s,b,hs,_,he⟩ := (hgen y hy g).mp hg
    rw [he.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _hi
    obtain ⟨j,hj⟩ := hs i
    rw [← hj,hz j,mul_zero]

end
end Hironaka.HironakaActualWholeAmbientHSSuperlevel
