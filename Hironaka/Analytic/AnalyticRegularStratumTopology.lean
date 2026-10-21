/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.RegularPatchNeighborhood
import Hironaka.Analytic.RegularLocusDense

set_option autoImplicit false

/-!
# Relative openness of analytic regular strata

The Grauert--Remmert reduction separates a regular hypersurface stratum from
its singular core.  This file supplies the topological part of that
separation: for every fixed complex dimension, the corresponding regular
locus is open *inside* the analytic set.  This does not assert that the
singular core is analytic, nor does it flatten it; those are the remaining
geometric inputs for the general analytic-set extension theorem.

The result is derived from the local biholomorphic flattening already proved
in `RegularPatchNeighborhood.eventually_regularAtDim`.
-/

open Set Filter
open scoped Topology

namespace Hironaka.AnalyticRegularStratumTopology



noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Around a point regular of dimension `k`, the whole relative piece of the
analytic set is regular of the same dimension. -/
theorem exists_open_regularLocus_neighborhood {A : Set M} {x : M} {k : ℕ}
    (hx : x ∈ regularLocus (n := n) A k) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ∩ A ⊆ regularLocus (n := n) A k := by
  obtain ⟨U, hUE, hUopen, hxU⟩ :=
    _root_.mem_nhds_iff.mp
      (RegularPatchNeighborhood.eventually_regularAtDim (show RegularAtDim (n := n) A x k from hx))
  exact ⟨U, hUopen, hxU, fun y hy => hUE hy.1 hy.2⟩

/-- The regular locus of a fixed dimension is open in the relative topology
of the underlying set.  The displayed ambient open set is constructed as the
union of its regular neighbourhoods, so no analytic property of the
complement is silently assumed. -/
theorem exists_isOpen_inter_eq_regularLocus (A : Set M) (k : ℕ) :
    ∃ O : Set M, IsOpen O ∧ A ∩ O = regularLocus (n := n) A k := by
  classical
  let U : {x : M // x ∈ regularLocus (n := n) A k} → Set M := fun x =>
    Classical.choose (exists_open_regularLocus_neighborhood (n := n) x.property)
  have hU : ∀ x : {x : M // x ∈ regularLocus (n := n) A k},
      IsOpen (U x) ∧ x.1 ∈ U x ∧ U x ∩ A ⊆ regularLocus (n := n) A k := fun x =>
    Classical.choose_spec (exists_open_regularLocus_neighborhood (n := n) x.property)
  refine ⟨⋃ x, U x, isOpen_iUnion fun x => (hU x).1, ?_⟩
  apply Subset.antisymm
  · rintro y ⟨hyA, hyO⟩
    rcases mem_iUnion.mp hyO with ⟨x, hyUx⟩
    exact (hU x).2.2 ⟨hyUx, hyA⟩
  · intro y hy
    refine ⟨(regularLocus_subset A k) hy, mem_iUnion.mpr ?_⟩
    exact ⟨⟨_, hy⟩, (hU ⟨_, hy⟩).2.1⟩

/-- For a closed analytic set, removing a fixed-dimensional regular stratum
leaves a closed core.  This is only a topological boundary statement; it does
not claim the core is analytic or has a coordinate-plane flattening. -/
theorem isClosed_diff_regularLocus {A : Set M} (hA : IsClosed A) (k : ℕ) :
    IsClosed (A \ regularLocus (n := n) A k) := by
  obtain ⟨O, hOopen, hAO⟩ := exists_isOpen_inter_eq_regularLocus (n := n) A k
  have hset : A \ (A ∩ O) = A ∩ Oᶜ := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
    constructor
    · rintro ⟨hxA, hx⟩
      exact ⟨hxA, fun hxO => hx ⟨hxA, hxO⟩⟩
    · rintro ⟨hxA, hxO⟩
      refine ⟨hxA, ?_⟩
      rintro ⟨-, hxO'⟩
      exact hxO hxO'
  rw [← hAO, hset]
  exact hA.inter hOopen.isClosed_compl

/-- The union of all regular loci that can occur in complex dimension `n`.
Using `Fin (n + 1)` makes the ambient relative-openness statement finite
without asserting that this complement is itself analytic. -/
def regularLocusAny (A : Set M) : Set M :=
  ⋃ k : Fin (n + 1), regularLocus (n := n) A k.1

omit [IsComplexManifold n M] in
/-- No regular point has complex dimension above the ambient dimension, so
the finite union `regularLocusAny` contains exactly every regular stratum. -/
theorem iUnion_regularLocus_eq_regularLocusAny (A : Set M) :
    (⋃ k : ℕ, regularLocus (n := n) A k) = regularLocusAny (n := n) A := by
  ext x
  change x ∈ ⋃ k : ℕ, regularLocus (n := n) A k ↔
    x ∈ ⋃ k : Fin (n + 1), regularLocus (n := n) A k.1
  constructor
  · intro hx
    rcases mem_iUnion.mp hx with ⟨k, hxk⟩
    have hk : k ≤ n := hxk.1
    refine mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_iff.mpr hk⟩, ?_⟩
    exact hxk
  · intro hx
    rcases mem_iUnion.mp hx with ⟨k, hxk⟩
    exact mem_iUnion.mpr ⟨k.1, hxk⟩

/-- The complete regular locus is dense in every complex analytic subset.
This records the dense part of the regular/singular stratification; it makes
no claim that the closed singular core is analytic or lower-dimensional. -/
theorem subset_closure_regularLocusAny {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) :
    A ⊆ closure (regularLocusAny (n := n) A) := by
  rw [← iUnion_regularLocus_eq_regularLocusAny A]
  exact RegularLocusDense.subset_closure_iUnion_regularLocus hA

/-- The full regular locus is relatively open in its analytic set. -/
theorem exists_isOpen_inter_eq_regularLocusAny (A : Set M) :
    ∃ O : Set M, IsOpen O ∧ A ∩ O = regularLocusAny (n := n) A := by
  choose O hOopen hAO using fun k : Fin (n + 1) =>
    exists_isOpen_inter_eq_regularLocus (n := n) A k.1
  refine ⟨⋃ k, O k, isOpen_iUnion hOopen, ?_⟩
  ext x
  change x ∈ A ∩ (⋃ k : Fin (n + 1), O k) ↔
    x ∈ ⋃ k : Fin (n + 1), regularLocus (n := n) A k.1
  constructor
  · rintro ⟨hxA, hxO⟩
    rcases mem_iUnion.mp hxO with ⟨k, hxOk⟩
    refine mem_iUnion.mpr ⟨k, ?_⟩
    rw [← hAO k]
    exact ⟨hxA, hxOk⟩
  · intro hx
    rcases mem_iUnion.mp hx with ⟨k, hxk⟩
    rw [← hAO k] at hxk
    exact ⟨hxk.1, mem_iUnion.mpr ⟨k, hxk.2⟩⟩

/-- The topological singular core (the complement of every possible regular
dimension) is closed when the analytic set is closed.  Establishing that this
closed core is an analytic set of smaller dimension remains a separate
Grauert--Remmert input. -/
theorem isClosed_diff_regularLocusAny {A : Set M} (hA : IsClosed A) :
    IsClosed (A \ regularLocusAny (n := n) A) := by
  obtain ⟨O, hOopen, hAO⟩ := exists_isOpen_inter_eq_regularLocusAny (n := n) A
  have hset : A \ (A ∩ O) = A ∩ Oᶜ := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
    constructor
    · rintro ⟨hxA, hx⟩
      exact ⟨hxA, fun hxO => hx ⟨hxA, hxO⟩⟩
    · rintro ⟨hxA, hxO⟩
      refine ⟨hxA, ?_⟩
      rintro ⟨-, hxO'⟩
      exact hxO hxO'
  rw [← hAO, hset]
  exact hA.inter hOopen.isClosed_compl

end

end Hironaka.AnalyticRegularStratumTopology
