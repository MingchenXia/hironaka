/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.SNCSubdivisorTopology
import DeJongAlterations.Geometry.AlgebraicFieldFiniteBoundaryIdeals

/-!
# Actual components of the descended split boundary

The entire original singleton ideal pullbacks and their actual integral closed subschemes
internally determine the finite reduced boundary and all of its native support components.

Blueprint: `split-boundary-components.tex`.
-/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData

namespace DeJongAlterations.Geometry.SplitBoundaryComponents

noncomputable section

variable {Y X : Scheme.{u}} (D : Y.IdealSheafData) [Finite (DivisorComponent D)]
  (I : DivisorComponent D → X.IdealSheafData)

def unionSupport : Closeds X :=
  ⟨⋃ C, ((I C).support : Set X), isClosed_iUnion_of_finite fun C => (I C).support.isClosed⟩

def boundary : X.IdealSheafData := ⨅ C, I C

private theorem unionSupport_eq_iSup : unionSupport D I = ⨆ C, (I C).support := by
  apply le_antisymm
  · intro x hx
    obtain ⟨C, hx⟩ := Set.mem_iUnion.mp hx
    exact le_iSup (fun C => (I C).support) C hx
  · refine iSup_le fun C => ?_
    intro x hx
    exact Set.mem_iUnion.mpr ⟨C, hx⟩

variable (hIntegral : ∀ C, IsIntegral (I C).subscheme)

include hIntegral

omit [Finite (DivisorComponent D)] in
private theorem singleton_ideal_eq (C : DivisorComponent D) :
    vanishingIdeal (I C).support = I C := by
  let : IsIntegral (I C).subscheme := hIntegral C
  exact vanishingIdeal_support.trans (idealSheaf_radical_eq_of_isReduced _)

theorem boundary_eq_vanishingIdeal : boundary D I = vanishingIdeal (unionSupport D I) := by
  rw [unionSupport_eq_iSup, vanishingIdeal_iSup]
  exact iInf_congr fun C => (singleton_ideal_eq D I hIntegral C).symm

theorem boundary_support : (boundary D I).support = unionSupport D I := by
  rw [boundary_eq_vanishingIdeal D I hIntegral, ReducedClosedSubscheme.support_vanishingIdeal]

theorem boundary_isReduced : IsReduced (boundary D I).subscheme := by
  rw [boundary_eq_vanishingIdeal D I hIntegral]
  exact ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme _

omit [Finite (DivisorComponent D)] in
private theorem singleton_irreducible (C : DivisorComponent D) :
    IsIrreducible ((I C).support : Set X) := by
  let : IsIntegral (I C).subscheme := hIntegral C
  have h := (IrreducibleSpace.isIrreducible_univ (I C).subscheme).image
    (I C).subschemeι (I C).subschemeι.continuous.continuousOn
  simpa only [Set.image_univ, range_subschemeι] using h

private theorem exists_index_of_component (C : DivisorComponent (boundary D I)) :
    ∃ A : DivisorComponent D, C.val = (I A).support := by
  classical
  let : Fintype (DivisorComponent D) := Fintype.ofFinite _
  let F : Finset (Set X) := Finset.univ.image (fun A : DivisorComponent D => ((I A).support : Set X))
  have hcover : (C.val : Set X) ⊆ ⋃₀ (F : Set (Set X)) := by
    intro x hx
    have hxD := SNCSubdivisorComponent.component_le_support (boundary D I) C hx
    rw [boundary_support D I hIntegral] at hxD
    obtain ⟨A, hxA⟩ := Set.mem_iUnion.mp hxD
    exact Set.mem_sUnion.mpr ⟨(I A).support, Finset.mem_image.mpr ⟨A, Finset.mem_univ _, rfl⟩, hxA⟩
  obtain ⟨T, hTF, hCT⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (SNCLocality.divisorComponent_isIrreducible (boundary D I) C) F
    (by intro T hT; obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hT; exact (I A).support.isClosed)
    hcover
  obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hTF
  refine ⟨A, Closeds.ext (Set.Subset.antisymm hCT ?_)⟩
  apply SNCSubdivisorTopology.component_maximal (boundary D I) C _
    (singleton_irreducible D I hIntegral A) hCT
  intro x hx
  rw [boundary_support D I hIntegral]
  exact Set.mem_iUnion.mpr ⟨A, hx⟩

variable (f : Y ⟶ X)
  (hI : ∀ C, (I C).comap f = vanishingIdeal C.val)

include hI

omit hIntegral [Finite (DivisorComponent D)] in
private theorem support_preimage (C : DivisorComponent D) :
    ((I C).support).preimage f.continuous = C.val := by
  rw [← support_comap, hI, ReducedClosedSubscheme.support_vanishingIdeal]

omit hIntegral [Finite (DivisorComponent D)] in
private theorem antichain (A B : DivisorComponent D)
    (h : (I A).support ≤ (I B).support) : A = B := by
  have hAB : A.val ≤ B.val := by
    rw [← support_preimage D I f hI A, ← support_preimage D I f hI B]
    exact fun _ hx => h hx
  apply Subtype.ext
  exact le_antisymm hAB (SNCSubdivisorTopology.component_maximal D A (B.val : Set Y)
    (SNCLocality.divisorComponent_isIrreducible D B) hAB
    (SNCSubdivisorComponent.component_le_support D B))

private theorem exists_component_of_index (A : DivisorComponent D) :
    ∃ C : DivisorComponent (boundary D I), C.val = (I A).support := by
  have hAD : (I A).support ≤ (boundary D I).support := by
    intro x hx
    rw [boundary_support D I hIntegral]
    exact Set.mem_iUnion.mpr ⟨A, hx⟩
  let : IrreducibleSpace (I A).support := Subtype.irreducibleSpace (singleton_irreducible D I hIntegral A)
  let g : (I A).support → (boundary D I).support := fun x => ⟨x.val, hAD x.property⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk _
  have hirr := (IrreducibleSpace.isIrreducible_univ (I A).support).image g hg.continuousOn
  obtain ⟨S, hS, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible (g '' Set.univ) hirr
  let C := divisorComponentOf (boundary D I) S hS
  have hAC : (I A).support ≤ C.val := by
    intro x hx
    exact ⟨g ⟨x, hx⟩, hsub ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩, rfl⟩
  obtain ⟨B, hCB⟩ := exists_index_of_component D I hIntegral C
  have hAB : A = B := antichain D I f hI A B (hCB ▸ hAC)
  exact ⟨C, hCB.trans (congrArg (fun A => (I A).support) hAB.symm)⟩

def componentEquiv : DivisorComponent D ≃ DivisorComponent (boundary D I) :=
  Equiv.ofBijective (fun A => (exists_component_of_index D I hIntegral f hI A).choose) (by
    constructor
    · intro A B h
      apply antichain D I f hI A B
      have hA := (exists_component_of_index D I hIntegral f hI A).choose_spec
      have hB := (exists_component_of_index D I hIntegral f hI B).choose_spec
      exact (hA.symm.trans ((congrArg Subtype.val h).trans hB)).le
    · intro C
      obtain ⟨A, hA⟩ := exists_index_of_component D I hIntegral C
      refine ⟨A, Subtype.ext ?_⟩
      exact (exists_component_of_index D I hIntegral f hI A).choose_spec.trans hA.symm)

theorem componentEquiv_support (A : DivisorComponent D) :
    (componentEquiv D I hIntegral f hI A).val = (I A).support :=
  (exists_component_of_index D I hIntegral f hI A).choose_spec

theorem componentEquiv_ideal (A : DivisorComponent D) :
    vanishingIdeal (componentEquiv D I hIntegral f hI A).val = I A := by
  rw [componentEquiv_support, singleton_ideal_eq D I hIntegral]

theorem componentEquiv_comap (A : DivisorComponent D) :
    (vanishingIdeal (componentEquiv D I hIntegral f hI A).val).comap f = vanishingIdeal A.val := by
  rw [componentEquiv_ideal, hI]

theorem componentIntersection_eq (J : Finset (DivisorComponent D)) :
    componentIntersection (boundary D I) (J.map (componentEquiv D I hIntegral f hI).toEmbedding) =
      ⨆ C ∈ J, I C := by
  classical
  simp only [componentIntersection, Finset.map_eq_image, Finset.iSup_finset_image]
  exact iSup_congr fun C => iSup_congr fun _ => componentEquiv_ideal D I hIntegral f hI C

end

end DeJongAlterations.Geometry.SplitBoundaryComponents
