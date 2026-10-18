/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.AnalyticIdentityInteriorExact
import Hironaka.Analytic.PureDimension

set_option autoImplicit false

/-!
# Analytic hulls of regular dimension strata

For an analytic set `A`, the closure of any chosen union of regular dimension
strata is analytic.  This module proves the extra dimension control needed in
the codimension-two removable-singularity route: every *regular* point of the
analytic closure still has a dimension selected by the original predicate.

In particular, the closure of all regular strata of dimension at most `n - 2`
is a genuine analytic set with no regular hypersurface points.  It is not
claimed that its singular locus is already an analytic lower-dimensional core;
that requires the still-missing analytic stratification theorem.
-/

open Set Filter
open scoped Topology

namespace Hironaka.AnalyticCodimTwoStratification


open PureDimension
open AnalyticLocalStatement
open AnalyticLocalStatement.LocalDecomposition
open RegularPointDimension

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The analytic closure of the regular dimension stratum selected by `P`. -/
def regularStratumHull (A : Set M) (P : ℕ → Prop) : Set M :=
  closure (regularStratum (n := n) A P)

/-- The regular-stratum hull is analytic. -/
theorem isComplexAnalyticSubset_regularStratumHull {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (P : ℕ → Prop) :
    IsComplexAnalyticSubset (n := n) (regularStratumHull (n := n) A P) :=
  isComplexAnalyticSubset_closure_regularStratum hA P

/-- A regular-stratum hull remains inside the original closed analytic set. -/
theorem regularStratumHull_subset {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (P : ℕ → Prop) : regularStratumHull (n := n) A P ⊆ A := by
  change closure (regularStratum (n := n) A P) ⊆ A
  exact closure_minimal (regularStratum_subset A P) hA.isClosed

/-- No new regular dimension appears after taking the analytic closure of a
selected regular stratum. -/
theorem regularAtDim_regularStratumHull {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (P : ℕ → Prop) {x : M} {k : ℕ}
    (hx : RegularAtDim (n := n) (regularStratumHull (n := n) A P) x k) : P k := by
  let C : Set M := regularStratumHull (n := n) A P
  have hCA : C ⊆ A := by
    change closure (regularStratum (n := n) A P) ⊆ A
    exact closure_minimal (regularStratum_subset A P) hA.isClosed
  have hxA : x ∈ A := hCA hx.2.1
  obtain ⟨D⟩ := exists_localDecomposition hA hxA
  have hxD : x ∈ D.nbhd := D.mem_nbhd
  have hCD : C ∩ D.nbhd = ⋃ i, ⋃ (_ : P (D.dim i)), D.piece i := by
    exact D.closure_inter_nbhd_eq P
  have hxCD : x ∈ C ∩ D.nbhd := ⟨hx.2.1, hxD⟩
  rw [hCD] at hxCD
  obtain ⟨i, hxCD⟩ := mem_iUnion.mp hxCD
  obtain ⟨hPi, hxi⟩ := mem_iUnion.mp hxCD
  obtain ⟨O, hOsub, hOopen, hxO⟩ := mem_nhds_iff.mp
    (RegularPatchNeighborhood.eventually_regularAtDim hx)
  let O0 : Set M := O ∩ D.nbhd
  have hO0open : IsOpen O0 := hOopen.inter D.isOpen_nbhd
  have hxO0 : x ∈ O0 := ⟨hxO, hxD⟩
  obtain ⟨O', hO'open, hO'sub, hO'ne, hdisj⟩ :=
    D.exists_isOpen_disjoint_others i hO0open ⟨x, hxO0, hxi⟩
  obtain ⟨y, hyO', hypiece⟩ := hO'ne
  obtain ⟨w, hwO', hwreg⟩ := mem_closure_iff.mp
    (D.subset_closure_regularLocus i hypiece) O' hO'open hyO'
  have hwpiece : w ∈ D.piece i := hwreg.2.1
  have hwO0 : w ∈ O0 := hO'sub hwO'
  have hwC : w ∈ C := by
    have hwD : w ∈ D.nbhd := hwO0.2
    have hwCD : w ∈ C ∩ D.nbhd := by
      rw [hCD]
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hPi, hwpiece⟩⟩
    exact hwCD.1
  have hCO' : C ∩ O' = D.piece i ∩ O' := by
    apply Subset.antisymm
    · rintro y ⟨hyC, hyO'⟩
      have hyD : y ∈ D.nbhd := (hO'sub hyO').2
      have hyU : y ∈ ⋃ j, ⋃ (_ : P (D.dim j)), D.piece j := by
        rw [← hCD]
        exact ⟨hyC, hyD⟩
      obtain ⟨j, hyU⟩ := mem_iUnion.mp hyU
      obtain ⟨hPj, hyj⟩ := mem_iUnion.mp hyU
      by_cases hji : j = i
      · exact ⟨hji ▸ hyj, hyO'⟩
      · exact False.elim ((eq_empty_iff_forall_notMem.mp (hdisj j hji)) y ⟨hyO', hyj⟩)
    · rintro y ⟨hyi, hyO'⟩
      have hyD : y ∈ D.nbhd := (hO'sub hyO').2
      refine ⟨?_, hyO'⟩
      have hyCD : y ∈ C ∩ D.nbhd := by
        rw [hCD]
        exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hPi, hyi⟩⟩
      exact hyCD.1
  have hwCreg : RegularAtDim (n := n) C w k :=
    hOsub ((hO'sub hwO').1) hwC
  have hwpieceReg : RegularAtDim (n := n) (D.piece i) w k :=
    regularAtDim_of_inter_eq hO'open hwO' hCO' hwCreg
  have hkd : k = D.dim i := D.eq_dim_of_regularAtDim i hwpieceReg
  rw [hkd]
  exact hPi

/-- The analytic hull of all regular strata of codimension at least two. -/
def codimTwoRegularHull (A : Set M) : Set M :=
  regularStratumHull (n := n) A (fun k => k + 2 ≤ n)

theorem isComplexAnalyticSubset_codimTwoRegularHull {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) :
    IsComplexAnalyticSubset (n := n) (codimTwoRegularHull (n := n) A) :=
  isComplexAnalyticSubset_regularStratumHull hA _

/-- Every regular point of the codimension-two analytic hull has complex
codimension at least two. -/
theorem codimTwoRegularHull_regularAtDim {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {x : M} {k : ℕ}
    (hx : RegularAtDim (n := n) (codimTwoRegularHull (n := n) A) x k) : k + 2 ≤ n := by
  change RegularAtDim (n := n)
    (regularStratumHull (n := n) A (fun j => j + 2 ≤ n)) x k at hx
  exact regularAtDim_regularStratumHull hA (fun j => j + 2 ≤ n) hx

/-- If every regular point already has codimension at least two, the
codimension-two regular hull is the original analytic set.  This is the
closest fully verified general-codimension-two instance available from the
current regular-stratum API. -/
theorem eq_codimTwoRegularHull_of_forall_regularAtDim {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A)
    (hcodim : ∀ {x : M} {k : ℕ}, RegularAtDim (n := n) A x k → k + 2 ≤ n) :
    codimTwoRegularHull (n := n) A = A := by
  apply Subset.antisymm
  · exact regularStratumHull_subset hA _
  · intro x hx
    have hxreg := RegularLocusDense.subset_closure_iUnion_regularLocus hA hx
    apply closure_mono ?_ hxreg
    rintro y hy
    obtain ⟨k, hyk⟩ := mem_iUnion.mp hy
    exact mem_regularStratum.mpr ⟨k, hcodim hyk, hyk⟩

/-- The analytic hull generated by the regular hypersurface stratum. -/
def hypersurfaceRegularHull (A : Set M) : Set M :=
  regularStratumHull (n := n) A (fun k => k = n - 1)

theorem isComplexAnalyticSubset_hypersurfaceRegularHull {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) :
    IsComplexAnalyticSubset (n := n) (hypersurfaceRegularHull (n := n) A) :=
  isComplexAnalyticSubset_regularStratumHull hA _

theorem hypersurfaceRegularHull_regularAtDim {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {x : M} {k : ℕ}
    (hx : RegularAtDim (n := n) (hypersurfaceRegularHull (n := n) A) x k) :
    k = n - 1 := by
  change RegularAtDim (n := n)
    (regularStratumHull (n := n) A (fun j => j = n - 1)) x k at hx
  exact regularAtDim_regularStratumHull hA (fun j => j = n - 1) hx

/-- A proper analytic subset has no regular point of full ambient dimension.
This is the exact point where connectedness rules out an open analytic
component. -/
theorem regularAtDim_ne_ambientDim_of_proper [ConnectedSpace M] {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hproper : A ≠ univ)
    {x : M} (hx : RegularAtDim (n := n) A x n) : False := by
  obtain ⟨-, hxA, Phi, -, -, hflat⟩ := hx
  let e := (complexChartAt (n := n) x).val
  let U : Set M := e.source ∩ e ⁻¹' Phi.source
  have hUopen : IsOpen U := e.isOpen_inter_preimage Phi.isOpen_source
  have hxU : x ∈ U := by
    exact ⟨mem_complexChartAt_source x, Phi.center_mem_source⟩
  have hUA : U ⊆ A := by
    intro y hy
    apply (hflat hy.1 hy.2).mpr
    intro i hi
    omega
  have hxint : x ∈ interior A :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hUopen.mem_nhds hxU) hUA)
  exact hproper (hA.eq_univ_of_interior_nonempty ⟨x, hxint⟩)

/-- A proper analytic set separates into two **analytic** supports: the hull
of its regular hypersurface stratum and the hull of all its regular
codimension-two strata.  Singular points of the hypersurface support remain
in that support; no false assertion that they lie in the codimension-two hull
is made here. -/
theorem eq_union_hypersurfaceRegularHull_codimTwoRegularHull [ConnectedSpace M]
    {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) (hproper : A ≠ univ) :
    A = hypersurfaceRegularHull (n := n) A ∪ codimTwoRegularHull (n := n) A := by
  apply Subset.antisymm
  · intro x hxA
    have hxreg := RegularLocusDense.subset_closure_iUnion_regularLocus hA hxA
    have hsplit : (⋃ k, regularLocus (n := n) A k) ⊆
        regularStratum (n := n) A (fun k => k = n - 1) ∪
          regularStratum (n := n) A (fun k => k + 2 ≤ n) := by
      rintro y hy
      obtain ⟨k, hyk⟩ := mem_iUnion.mp hy
      by_cases hhk : k = n - 1
      · exact Or.inl (mem_regularStratum.mpr ⟨k, hhk, hyk⟩)
      · right
        refine mem_regularStratum.mpr ⟨k, ?_, hyk⟩
        have hk : k ≤ n := hyk.1
        have hkn : k ≠ n := fun hkn =>
          regularAtDim_ne_ambientDim_of_proper hA hproper (hkn ▸ hyk)
        omega
    have hxsplit : x ∈ closure
        (regularStratum (n := n) A (fun k => k = n - 1) ∪
          regularStratum (n := n) A (fun k => k + 2 ≤ n)) :=
      closure_mono hsplit hxreg
    rw [closure_union] at hxsplit
    exact hxsplit
  · exact union_subset
      (regularStratumHull_subset hA (fun k => k = n - 1))
      (regularStratumHull_subset hA (fun k => k + 2 ≤ n))

end

end Hironaka.AnalyticCodimTwoStratification
