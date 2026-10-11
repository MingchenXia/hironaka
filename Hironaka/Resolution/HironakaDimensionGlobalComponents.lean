/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaEmbeddedDimensionParts
import Hironaka.Analytic.GlobalComponents
import Hironaka.Analytic.AnalyticDimensionBasics
import Hironaka.Analytic.GeometricPureDimension
import Hironaka.Analytic.GlobalComponentRegularity

set_option autoImplicit false

/-!
# Geometric dimensions of genuine global irreducible components

The closure of `regularLocus A k` equals the union of the genuine global
irreducible components of `A` of geometric pure dimension `k`.
The global components are Demailly II.5.3's closures of connected components
of the full regular locus; their analytic irreducibility and local finiteness
are proved in `GlobalComponents`. This module requires neither compactness
nor positive ambient dimension nor empty interior.

Blueprint: `hironaka-dimension-extension.tex`.
-/

open Set Filter
open scoped Topology

namespace Hironaka.HironakaDimensionGlobalComponents

open GlobalComponents RegularLocusComponent AnalyticDimensionBasics
  HironakaEmbeddedDimensionParts

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The regular-locus component through a `k`-regular point closes to an
actual analytically irreducible set of geometric pure dimension `k`. -/
theorem isPureDim_closure_component {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {c : M} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k) :
    IsPureDim (n := n) (closure (component (n := n) A c)) k := by
  let V : ClosedIrreducibleAnalyticSubvariety n M :=
    { carrier := closure (component (n := n) A c)
      isClosed_carrier := isClosed_closure
      irreducible_carrier := isComplexAnalyticallyIrreducible_closure_component hA hc
      dim := k
      dim_le := hc.1
      regularLocus_nonempty :=
        ⟨c, regularAtDim_closure_component hc (mem_component_self hc)⟩ }
  intro y j hy
  exact PureDimension.eq_dim_of_regularAtDim V hy

/-- A genuine global irreducible component has an internally witnessed,
unique geometric pure dimension, including in ambient dimension zero. -/
theorem exists_unique_isPureDim_of_mem_globalComponents {A B : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A)
    (hB : B ∈ globalComponents (n := n) A) :
    ∃! k : ℕ, k ≤ n ∧ IsPureDim (n := n) B k := by
  obtain ⟨c, ⟨k, hc⟩, rfl⟩ := hB
  refine ⟨k, ⟨hc.1, isPureDim_closure_component hA hc⟩, ?_⟩
  intro j hj
  exact (hj.2 c k (regularAtDim_closure_component hc (mem_component_self hc))).symm

/-- Arbitrary subunions of actual global components are closed; compactness
is unnecessary because the full component family is locally finite. -/
theorem isClosed_sUnion_globalComponents_subfamily {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {S : Set (Set M)}
    (hS : S ⊆ globalComponents (n := n) A) : IsClosed (⋃₀ S) := by
  let f : S → globalComponents (n := n) A := fun B => ⟨B.1, hS B.2⟩
  have hf : Function.Injective f := by
    intro B C h
    exact Subtype.ext
      (congrArg (fun D : globalComponents (n := n) A => (D : Set M)) h)
  have hlf := (locallyFinite_globalComponents hA).comp_injective hf
  have hclosed : IsClosed (⋃ B : S, (B : Set M)) := hlf.isClosed_iUnion fun B => by
    change IsClosed (B : Set M)
    obtain ⟨c, -, hBc⟩ := hS B.2
    rw [hBc]
    exact isClosed_closure
  have heq : (⋃ B : S, (B : Set M)) = ⋃₀ S := by
    ext x
    simp only [mem_iUnion, mem_sUnion]
    exact ⟨fun ⟨B, hx⟩ => ⟨B.1, B.2, hx⟩,
      fun ⟨B, hB, hx⟩ => ⟨⟨B, hB⟩, hx⟩⟩
  rwa [heq] at hclosed

/-- Every global component of pure geometric dimension `k` lies in the
`k`-dimensional part, using the genuine regular-locus generating component. -/
theorem subset_dimensionPart_of_mem_globalComponents_of_isPureDim {A B : Set M}
    (hB : B ∈ globalComponents (n := n) A) {k : ℕ}
    (hp : IsPureDim (n := n) B k) : B ⊆ dimensionPart (n := n) A k := by
  obtain ⟨c, ⟨j, hc⟩, rfl⟩ := hB
  have hjk : j = k := hp c j (regularAtDim_closure_component hc (mem_component_self hc))
  subst j
  exact closure_mono fun y hy => regularAtDim_of_mem_component hc hy

/-- **The standard irreducible-component identification of dimension parts.**
The component dimensions are actual local manifold dimensions, not supplied
labels. The statement permits noncompact, disconnected and empty manifolds,
empty analytic sets, dimension zero and the full-dimensional part. -/
theorem dimensionPart_eq_sUnion_globalComponents {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (k : ℕ) :
    dimensionPart (n := n) A k =
      ⋃₀ {B | B ∈ globalComponents (n := n) A ∧ IsPureDim (n := n) B k} := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro c hc
      exact mem_sUnion.mpr ⟨closure (component (n := n) A c),
        ⟨closure_component_mem_globalComponents hc, isPureDim_closure_component hA hc⟩,
        subset_closure (mem_component_self hc)⟩
    · exact isClosed_sUnion_globalComponents_subfamily hA fun B hB => hB.1
  · rintro x ⟨B, ⟨hB, hp⟩, hx⟩
    exact subset_dimensionPart_of_mem_globalComponents_of_isPureDim hB hp hx

/-- Geometric purity of each actual dimension part: every regular point has
dimension `k`, rather than merely a density statement about `k`-regular points. -/
theorem isPureDim_dimensionPart {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (k : ℕ) : IsPureDim (n := n) (dimensionPart (n := n) A k) k := by
  intro y j hy
  obtain ⟨z, hz, hzk⟩ := mem_closure_iff_nhds.mp
    (subset_closure_regularLocus_dimensionPart hA.isClosed k hy.2.1) _
    (RegularPatchNeighborhood.eventually_regularAtDim hy)
  exact RegularPointDimension.eq_of_regularAtDim (hz hzk.2.1) hzk

/-- A genuine global component belongs wholly to the dimension part exactly
when its internally witnessed geometric pure dimension is the selected one. -/
theorem isPureDim_iff_subset_dimensionPart_of_mem_globalComponents {A B : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A)
    (hB : B ∈ globalComponents (n := n) A) (k : ℕ) :
    IsPureDim (n := n) B k ↔ B ⊆ dimensionPart (n := n) A k := by
  constructor
  · exact subset_dimensionPart_of_mem_globalComponents_of_isPureDim hB
  · intro hsub
    obtain ⟨c, ⟨j, hc⟩, rfl⟩ := hB
    obtain ⟨z, hz, hzk⟩ := mem_closure_iff_nhds.mp
      (hsub (subset_closure (mem_component_self hc))) _
      (RegularPatchNeighborhood.eventually_regularAtDim hc)
    have hjk : j = k := RegularPointDimension.eq_of_regularAtDim (hz hzk.2.1) hzk
    subst j
    exact isPureDim_closure_component hA hc

/-- Actual local decomposition data of a dimension part, produced by
filtering the original local analytic branches by geometric dimension.
The neighborhood and all retained holomorphic equations are preserved. -/
def localDecomposition_dimensionPart {A : Set M} {p : M}
    (D : AnalyticLocalStatement.LocalDecomposition (n := n) A p) (k : ℕ) :
    AnalyticLocalStatement.LocalDecomposition (n := n) (dimensionPart (n := n) A k) p := by
  classical
  let I := {i : Fin D.count // D.dim i = k}
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine
    { nbhd := D.nbhd
      isOpen_nbhd := D.isOpen_nbhd
      mem_nbhd := D.mem_nbhd
      nbhd_subset_source := D.nbhd_subset_source
      count := Fintype.card I
      piece := fun i => D.piece (e i).1
      dim := fun _ => k
      eqnCount := fun i => D.eqnCount (e i).1
      eqn := fun i => D.eqn (e i).1
      eqn_holomorphic := fun i => D.eqn_holomorphic (e i).1
      piece_subset := fun i => D.piece_subset (e i).1
      mem_piece_iff := fun i => D.mem_piece_iff (e i).1
      inter_nbhd_eq := ?_
      eq_dim_of_regularAtDim := fun i {_} {_} hy =>
        (D.eq_dim_of_regularAtDim (e i).1 hy).trans (e i).2
      subset_closure_regularLocus := fun i => ?_
      exists_mem_not_mem := fun i j hij => ?_ }
  · have heq := D.closure_inter_nbhd_eq (· = k)
    rw [regularStratum_eq_regularLocus] at heq
    change closure (regularLocus (n := n) A k) ∩ D.nbhd = ⋃ i, D.piece (e i).1
    rw [heq]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hik, hxi⟩
      refine ⟨e.symm ⟨i, hik⟩, ?_⟩
      simpa using hxi
    · rintro ⟨i, hxi⟩
      exact ⟨(e i).1, (e i).2, hxi⟩
  · simpa only [(e i).2] using D.subset_closure_regularLocus (e i).1
  · apply D.exists_mem_not_mem (e i).1 (e j).1
    intro heq
    exact hij (e.injective (Subtype.ext heq))

/-- Natural analytic data produce a finite local decomposition of the actual
dimension part with every retained branch of geometric dimension `k`. -/
theorem exists_localDecomposition_dimensionPart {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {p : M} {k : ℕ}
    (hp : p ∈ dimensionPart (n := n) A k) :
    ∃ D : AnalyticLocalStatement.LocalDecomposition (n := n)
      (dimensionPart (n := n) A k) p, ∀ i, D.dim i = k := by
  obtain ⟨D⟩ := AnalyticLocalStatement.exists_localDecomposition hA
    (dimensionPart_subset hA.isClosed k hp)
  exact ⟨localDecomposition_dimensionPart D k, fun _ => rfl⟩

end

end Hironaka.HironakaDimensionGlobalComponents
