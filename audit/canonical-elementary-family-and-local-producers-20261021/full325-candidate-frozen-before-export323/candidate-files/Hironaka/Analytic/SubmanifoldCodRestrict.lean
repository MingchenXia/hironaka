/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.SubmanifoldChartedSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Holomorphic maps into a closed complex submanifold

Source: standard (a holomorphic map with values in a closed complex submanifold is holomorphic
into the submanifold); needed for Copy-4, `prop:principalization`, Step 4
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1880-1906`),
where `φ' = (π|_W)^* φ_{K,ℓ} + τ ψ_{E_rel}|_W` pulls a potential on the submanifold `V ⊆ X` back
along the restriction `π|_W : W → V` of the modification to the strict transform.

`Hironaka.SubmanifoldChartedSpace` makes a closed complex submanifold `W ⊆ X` of dimension `k`
a complex manifold `↥W` (flattening charts) and proves the inclusion `↥W → X` holomorphic.
This module proves the converse direction for maps: if `f : M → X` is holomorphic and takes
values in `W`, the corestriction `M → ↥W` is holomorphic.  In the flattening chart `F` at
`f y` it reads `z ↦ pr_k (Φ_F (e_F (f z)))`, a composition of holomorphic maps.

* `contMDiff_codRestrict` — the corestriction is holomorphic;
* `contMDiff_restrictPreimage` — the restriction `↥W' → ↥W` of a holomorphic `π : Y → X` to
  closed submanifolds `W' ⊆ π⁻¹ W` (Copy-4's `π|_W : W → V`) is holomorphic.

Sorry-free; no compactness, connectedness or Kähler hypothesis.
-/

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace Hironaka.SubmanifoldCodRestrict

open Hironaka.RegularLocusDense SubmanifoldChartedSpace

noncomputable section

variable {n k m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {M : Type v} [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]

/-- **A holomorphic map with values in a closed complex submanifold is holomorphic into the
submanifold**, for the flattening atlas of `SubmanifoldChartedSpace.chartedSpace`. -/
theorem contMDiff_codRestrict {W : Set X} (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) {f : M → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) (hfW : ∀ y, f y ∈ W) :
    letI := chartedSpace hk hW
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel k) ∞
      (fun y => (⟨f y, hfW y⟩ : W)) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro y
  set F := FlatData.ofRegularAtDim (hW (f y) (hfW y)) with hF
  have hamb : f y ∈ F.ambSource := FlatData.mem_ambSource_ofRegularAtDim (hW (f y) (hfW y))
  rw [contMDiffAt_iff_target]
  refine ⟨(hf.continuous.subtype_mk hfW).continuousAt, ?_⟩
  have hext : (extChartAt 𝓘(ℂ, ComplexModel k) (⟨f y, hfW y⟩ : W) : W → ComplexModel k) =
      F.toCoord := by
    ext1 p
    simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply, id]
    rfl
  rw [hext]
  -- `e_F ∘ f` is holomorphic at `y`
  have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞
      (fun z => F.amb.val (f z)) y :=
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas F.amb.property)
      hamb.1).comp y (hf y)
  -- `pr_k ∘ Φ_F` is holomorphic at `e_F (f y)`
  have h2 : ContDiffAt ℂ ∞ (fun w => coordinateProjection n k (F.flat w)) (F.amb.val (f y)) :=
    (coordinateProjection n k).contDiff.contDiffAt.comp _
      ((contDiffOn_of_differentiableOn_complex F.differentiableOn_flat
        F.flat.open_source).contDiffAt (F.flat.open_source.mem_nhds hamb.2))
  have h3 : ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel k) ∞
      (fun z => coordinateProjection n k (F.flat (F.amb.val (f z)))) y :=
    ContMDiffAt.comp (g := fun w => coordinateProjection n k (F.flat w))
      (f := fun z => F.amb.val (f z)) y h2.contMDiffAt h1
  exact h3

/-- **The restriction of a holomorphic map to closed submanifolds is holomorphic**: if
`π : Y → X` is holomorphic, `W' ⊆ Y` and `W ⊆ X` are closed complex submanifolds (flattening
atlases) and `π (W') ⊆ W`, then `π|_{W'} : ↥W' → ↥W` is holomorphic.  This is Copy-4's
`π|_W : W → V` from the strict transform to the centre. -/
theorem contMDiff_restrictPreimage {Y : Type v} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y] {k' : ℕ} {W : Set X}
    (hk : k ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) {W' : Set Y} (hk' : k' ≤ m)
    (hW' : ∀ x ∈ W', RegularAtDim (n := m) W' x k') {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ π)
    (hπW : ∀ y ∈ W', π y ∈ W) :
    letI := chartedSpace hk hW
    letI := chartedSpace hk' hW'
    ContMDiff 𝓘(ℂ, ComplexModel k') 𝓘(ℂ, ComplexModel k) ∞
      (fun w : W' => (⟨π w.1, hπW w.1 w.2⟩ : W)) := by
  let := chartedSpace hk' hW'
  have := isComplexManifold_chartedSpace hk' hW'
  exact contMDiff_codRestrict hk hW (hπ.comp (contMDiff_val hk' hW')) fun w => hπW w.1 w.2

end

end Hironaka.SubmanifoldCodRestrict
