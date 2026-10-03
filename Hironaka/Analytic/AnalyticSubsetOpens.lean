/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.AnalyticDimensionBasics
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Manifold.LocalHolomorphicInverse
import Hironaka.Blowup.BlowupLocalSurjectivity
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Analytic subsets of an open subset of a complex manifold

An open subset `U` of a complex manifold `M` is a complex manifold (`TopologicalSpace.Opens`
with the restricted charts `(chartAt x).subtypeRestr`); the preferred chart of `U` at `x` is the
preferred chart of `M` at `x`, restricted.  This file transfers the analytic notions between `M`
and `U`:

* `regularAtDim_preimage_val_iff`: the regular points of `A ∩ U` (in `U`) and their dimensions are those of `A` (in
  `M`) lying in `U`; hence the dimension predicates of `AnalyticDimensionBasics` transfer;
-/

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka.AnalyticSubsetOpens

open AnalyticDimensionBasics

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- An open subset of a complex manifold is a complex manifold. -/
instance instIsComplexManifoldOpens (U : Opens M) : IsComplexManifold n U where

variable {U : Opens M}

/-! ### The restricted charts -/

theorem mem_chartAt_opens_source {x y : U} :
    y ∈ (chartAt (ComplexModel n) x).source ↔ (y : M) ∈ (chartAt (ComplexModel n) (x : M)).source := by
  rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]; rfl

theorem chartAt_opens_target_subset (x : U) :
    (chartAt (ComplexModel n) x).target ⊆ (chartAt (ComplexModel n) (x : M)).target :=
  OpenPartialHomeomorph.subtypeRestr_target_subset _ ⟨x⟩

/-- A point of the chart source of `M` whose image lies in the target of the restricted chart
belongs to `U`. -/
theorem mem_opens_of_chart_mem_target {x : U} {y : M}
    (hy : y ∈ (chartAt (ComplexModel n) (x : M)).source)
    (hv : chartAt (ComplexModel n) (x : M) y ∈ (chartAt (ComplexModel n) x).target) : y ∈ U := by
  have h := (chartAt (ComplexModel n) x).map_target hv
  have h2 := (chartAt (ComplexModel n) x).right_inv hv
  set z := (chartAt (ComplexModel n) x).symm (chartAt (ComplexModel n) (x : M) y) with hz
  have hz' : chartAt (ComplexModel n) (x : M) (z : M) = chartAt (ComplexModel n) (x : M) y := h2
  have hzs : (z : M) ∈ (chartAt (ComplexModel n) (x : M)).source := mem_chartAt_opens_source.mp h
  have : (z : M) = y := (chartAt (ComplexModel n) (x : M)).injOn hzs hy hz'
  exact this ▸ z.2

theorem isOpen_chartAt_opens_target (x : U) :
    IsOpen (chartAt (ComplexModel n) x).target :=
  (chartAt (ComplexModel n) x).open_target

/-! ### Regular points and dimension -/

/-- **Regular points transfer**: `x ∈ U` is a regular point of `A ∩ U` of dimension `k` (in `U`)
iff it is a regular point of `A` of dimension `k` (in `M`). -/
theorem regularAtDim_preimage_val_iff {A : Set M} {x : U} {k : ℕ} :
    RegularAtDim (n := n) ((↑) ⁻¹' A : Set U) x k ↔ RegularAtDim (n := n) A (x : M) k := by
  constructor
  · rintro ⟨hk, hxA, Φ, hΦt, hΦ0, hΦA⟩
    refine ⟨hk, hxA, Φ, hΦt.trans (chartAt_opens_target_subset x), hΦ0, ?_⟩
    intro y hy hyΦ
    have hyU : y ∈ U := mem_opens_of_chart_mem_target hy (hΦt hyΦ)
    exact hΦA (y := ⟨y, hyU⟩) (mem_chartAt_opens_source.mpr hy) hyΦ
  · rintro ⟨hk, hxA, Φ, hΦt, hΦ0, hΦA⟩
    set S := (chartAt (ComplexModel n) x).target with hS
    have hxS : chartAt (ComplexModel n) (x : M) x ∈ Φ.source ∩ S :=
      ⟨Φ.center_mem_source, (chartAt (ComplexModel n) x).map_source
        (mem_chart_source (ComplexModel n) x)⟩
    refine ⟨hk, hxA, Φ.restrict S (isOpen_chartAt_opens_target x) _ hxS, inter_subset_right,
      hΦ0, ?_⟩
    intro y hy hyΦ
    exact hΦA (y := (y : M)) (mem_chartAt_opens_source.mp hy) hyΦ.1

end Hironaka.AnalyticSubsetOpens
