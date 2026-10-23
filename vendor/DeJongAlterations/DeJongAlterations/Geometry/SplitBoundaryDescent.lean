/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.SplitBoundaryComponents
import DeJongAlterations.Geometry.FlatIdealSheafIntersection

/-!
# Entire split boundary descent with all actual native support components

All native components, their whole original ideals, the entire reduced boundary pullback,
and every original finite scheme-theoretic intersection are constructed internally.

Blueprint: `split-boundary-descent.tex`.
-/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData

namespace DeJongAlterations.Geometry.SplitBoundaryDescent

noncomputable section

theorem original_eq_iInf_components {Y : Scheme.{u}} (D : Y.IdealSheafData)
    [IsReduced D.subscheme] : D = ⨅ C : DivisorComponent D, vanishingIdeal C.val := by
  have hsup : (⨆ C : DivisorComponent D, C.val) = D.support := by
    apply le_antisymm
    · exact iSup_le fun C => SNCSubdivisorComponent.component_le_support D C
    · intro y hy
      let z : D.support := ⟨y, hy⟩
      let C := divisorComponentOf D (irreducibleComponent z)
        (irreducibleComponent_mem_irreducibleComponents z)
      have hyC : y ∈ (C.val : Set Y) := ⟨z, mem_irreducibleComponent, rfl⟩
      exact le_iSup (fun C : DivisorComponent D => C.val) C hyC
  rw [← vanishingIdeal_iSup, hsup, vanishingIdeal_support, idealSheaf_radical_eq_of_isReduced]

open AlgebraicFieldFiniteModel AlgebraicFieldFiniteBoundaryIdeals
open StableModification.Limits

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem exists_snc_descended_components
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] [PerfectField L]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of L))
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (D : Y.IdealSheafData) (hD : IsStrictNormalCrossings D)
    {i : Index k L} (m : Model (diagram k L) (scalarCone k L) p i) (hm : m.IsFP) :
    ∃ (j : Index k L) (h : j ⟶ i)
      (I : IntersectionIndex D → (m.baseChange h).Y.IdealSheafData)
      (D₀ : (m.baseChange h).Y.IdealSheafData) (e : DivisorComponent D ≃ DivisorComponent D₀),
      D₀ = ⨅ C : DivisorComponent D, I (singletonIndex C) ∧
      IsReduced D₀.subscheme ∧ D₀.comap (m.baseChange h).g = D ∧
      (∀ C : DivisorComponent D,
        vanishingIdeal (e C).val = I (singletonIndex C) ∧
        (e C).val = (I (singletonIndex C)).support) ∧
      (∀ J : IntersectionIndex D,
        componentIntersection D₀ (J.val.map e.toEmbedding) = I J ∧
        (I J).comap (m.baseChange h).g = componentIntersection D J.val ∧
        IsRegularScheme (I J).subscheme) ∧
      (∀ C : DivisorComponent D, IsIntegral (I (singletonIndex C)).subscheme) := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian Y := ⟨⟩
  let : IsReduced D.subscheme := hD.reduced
  obtain ⟨j, h, I, hI, hIntegral⟩ := exists_snc_intersection_ideals k L p D hD m hm
  let M := m.baseChange h
  let A : DivisorComponent D → M.Y.IdealSheafData := fun C => I (singletonIndex C)
  have hA (C : DivisorComponent D) : (A C).comap M.g = vanishingIdeal C.val := by
    simpa only [A, componentIntersection, singletonIndex, Finset.mem_singleton, iSup_iSup_eq_left]
      using (hI (singletonIndex C)).1
  let c : Spec (.of L) ⟶ Spec (.of (levelField k L j)) :=
    Spec.map (CommRingCat.ofHom (levelField k L j).val.toRingHom)
  have H : IsPullback M.g p M.fY c := by simpa only [scalarCone_π, c] using M.isPullback
  let : Flat c := inferInstance
  let : IsAffineHom c := inferInstance
  let : Flat M.g := MorphismProperty.of_isPullback H.flip inferInstance
  let : IsAffineHom M.g := MorphismProperty.of_isPullback H.flip inferInstance
  let D₀ := SplitBoundaryComponents.boundary D A
  let e := SplitBoundaryComponents.componentEquiv D A hIntegral M.g hA
  have hD₀ : D₀.comap M.g = D := by
    change (⨅ C, A C).comap M.g = D
    rw [FlatIdealSheafIntersection.comap_iInf]
    simp only [hA]
    exact (original_eq_iInf_components D).symm
  refine ⟨j, h, I, D₀, e, rfl, SplitBoundaryComponents.boundary_isReduced D A hIntegral, hD₀,
    (fun C => ⟨SplitBoundaryComponents.componentEquiv_ideal D A hIntegral M.g hA C,
      SplitBoundaryComponents.componentEquiv_support D A hIntegral M.g hA C⟩), ?_, hIntegral⟩
  intro J
  refine ⟨?_, (hI J).1, (hI J).2.1⟩
  exact (SplitBoundaryComponents.componentIntersection_eq D A hIntegral M.g hA J.val).trans
    (hI J).2.2.symm

end

end DeJongAlterations.Geometry.SplitBoundaryDescent
