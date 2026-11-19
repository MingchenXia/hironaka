import Hironaka.Analytic.AnalyticDimensionBasics
import Mathlib.Geometry.Manifold.ContMDiff.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Analytic subsets of an open subset of a complex manifold

Blueprint `rem:open-subset-analytic` (step toward `rem:analytic-image-dimension`,
`rem:fibre-dimension-lower-bound` and Remmert--Stein in `blueprint/src/remmert.tex`).

An open subset `U` of a complex manifold `M` is a complex manifold (`TopologicalSpace.Opens`
with the restricted charts `(chartAt x).subtypeRestr`); the preferred chart of `U` at `x` is the
preferred chart of `M` at `x`, restricted.  This file transfers the analytic notions between `M`
and `U`:

* `isComplexAnalyticSubset_preimage_val`: `A ∩ U` is analytic in `U` when `A` is analytic in `M`;
* `isComplexAnalyticSubset_of_forall_opens`: analyticity is local -- `A` is analytic in `M` as soon
  as every point has an open neighbourhood `U` with `A ∩ U` analytic in `U`;
  `isComplexAnalyticSubset_image_val`: a subset of `U` analytic in `U` and closed in `M` is analytic
  in `M`;
* `regularAtDim_preimage_val_iff`: the regular points of `A ∩ U` (in `U`) and their dimensions are
  those of `A` (in `M`) lying in `U`; hence the dimension predicates of `AnalyticDimensionBasics`
  transfer (`dimLE_preimage_val`, `dimLE_image_val_iff`, `locDimGE_preimage_val_iff`,
  `locDimLE_preimage_val_iff`, `isPureDim_image_val_iff`);
* `contMDiff_restrict`: a map holomorphic on `U` restricts to a holomorphic map on the manifold `U`.

Sorry-free.
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

theorem chartAt_opens_apply (x y : U) :
    chartAt (ComplexModel n) x y = chartAt (ComplexModel n) (x : M) y := rfl

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

theorem chart_mem_opens_target {x y : U}
    (hy : (y : M) ∈ (chartAt (ComplexModel n) (x : M)).source) :
    chartAt (ComplexModel n) (x : M) y ∈ (chartAt (ComplexModel n) x).target :=
  (chartAt (ComplexModel n) (x : M)).map_subtype_source ⟨x⟩ hy

theorem isOpen_chartAt_opens_target (x : U) :
    IsOpen (chartAt (ComplexModel n) x).target :=
  (chartAt (ComplexModel n) x).open_target

/-! ### Analytic subsets -/

/-- The trace on `U` of a presentation of `A` at a point of `U`. -/
def presentationPreimageVal {A : Set M} (x : U)
    (P : ComplexAnalyticPresentationAt (n := n) A (x : M)) :
    ComplexAnalyticPresentationAt (n := n) ((↑) ⁻¹' A : Set U) x where
  generatorCount := P.generatorCount
  generator := P.generator
  coordinateNeighborhood := P.coordinateNeighborhood ∩ (chartAt (ComplexModel n) x).target
  isOpen_coordinateNeighborhood :=
    P.isOpen_coordinateNeighborhood.inter (isOpen_chartAt_opens_target x)
  center_mem_coordinateNeighborhood :=
    ⟨P.center_mem_coordinateNeighborhood, (chartAt (ComplexModel n) x).map_source
      (mem_chart_source (ComplexModel n) x)⟩
  coordinateNeighborhood_subset_target := inter_subset_right
  generator_holomorphic i := (P.generator_holomorphic i).mono inter_subset_left
  zeroLocus := by
    intro y hy hyN
    exact P.zeroLocus (y := (y : M)) (mem_chartAt_opens_source.mp hy) hyN.1

/-- **Restriction**: `A ∩ U` is analytic in `U` when `A` is analytic in `M`. -/
theorem isComplexAnalyticSubset_preimage_val {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (U : Opens M) :
    IsComplexAnalyticSubset (n := n) ((↑) ⁻¹' A : Set U) :=
  fun x => ⟨presentationPreimageVal x (hA x).some⟩

/-- A presentation of `A ∩ U` in `U` at `x` is a presentation of `A` in `M` at `x`. -/
def presentationOfPreimageVal {A : Set M} (x : U)
    (P : ComplexAnalyticPresentationAt (n := n) ((↑) ⁻¹' A : Set U) x) :
    ComplexAnalyticPresentationAt (n := n) A (x : M) where
  generatorCount := P.generatorCount
  generator := P.generator
  coordinateNeighborhood := P.coordinateNeighborhood
  isOpen_coordinateNeighborhood := P.isOpen_coordinateNeighborhood
  center_mem_coordinateNeighborhood := P.center_mem_coordinateNeighborhood
  coordinateNeighborhood_subset_target :=
    P.coordinateNeighborhood_subset_target.trans (chartAt_opens_target_subset x)
  generator_holomorphic := P.generator_holomorphic
  zeroLocus := by
    intro y hy hyN
    have hyU : y ∈ U := mem_opens_of_chart_mem_target hy (P.coordinateNeighborhood_subset_target hyN)
    exact P.zeroLocus (y := ⟨y, hyU⟩) (mem_chartAt_opens_source.mpr hy) hyN

/-- **Analyticity is local**: if every point has an open neighbourhood `U` with `A ∩ U` analytic
in `U`, then `A` is analytic. -/
theorem isComplexAnalyticSubset_of_forall_opens {A : Set M}
    (h : ∀ x : M, ∃ U : Opens M, x ∈ U ∧
      IsComplexAnalyticSubset (n := n) ((↑) ⁻¹' A : Set U)) :
    IsComplexAnalyticSubset (n := n) A := by
  intro x
  obtain ⟨U, hxU, hU⟩ := h x
  exact ⟨presentationOfPreimageVal (⟨x, hxU⟩ : U) (hU ⟨x, hxU⟩).some⟩

theorem isComplexAnalyticSubset_iff_forall_opens {A : Set M} :
    IsComplexAnalyticSubset (n := n) A ↔ ∀ x : M, ∃ U : Opens M, x ∈ U ∧
      IsComplexAnalyticSubset (n := n) ((↑) ⁻¹' A : Set U) :=
  ⟨fun hA _ => ⟨⊤, trivial, isComplexAnalyticSubset_preimage_val hA ⊤⟩,
    isComplexAnalyticSubset_of_forall_opens⟩

/-- A subset of `U` which is analytic in `U` and closed in `M` is analytic in `M`. -/
theorem isComplexAnalyticSubset_image_val {B : Set U}
    (hB : IsComplexAnalyticSubset (n := n) B) (hc : IsClosed ((↑) '' B : Set M)) :
    IsComplexAnalyticSubset (n := n) ((↑) '' B : Set M) := by
  refine isComplexAnalyticSubset_of_forall_opens fun x => ?_
  by_cases hxU : x ∈ U
  · refine ⟨U, hxU, ?_⟩
    rwa [Subtype.val_injective.preimage_image]
  · refine ⟨⟨_, hc.isOpen_compl⟩, fun hx => hxU ?_, ?_⟩
    · obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    · have : ((↑) ⁻¹' ((↑) '' B : Set M) : Set (⟨_, hc.isOpen_compl⟩ : Opens M)) = ∅ := by
        ext y
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        exact y.2
      rw [this]
      exact fun y => ⟨ComplexAnalyticPresentationAt.empty y⟩

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

theorem regularAtDim_image_val_iff {B : Set U} {x : U} {k : ℕ} :
    RegularAtDim (n := n) ((↑) '' B : Set M) (x : M) k ↔ RegularAtDim (n := n) B x k := by
  rw [← regularAtDim_preimage_val_iff, Subtype.val_injective.preimage_image]

theorem mem_opens_of_regularAtDim_image_val {B : Set U} {y : M} {k : ℕ}
    (hy : RegularAtDim (n := n) ((↑) '' B : Set M) y k) : y ∈ U := by
  obtain ⟨z, -, rfl⟩ := hy.2.1
  exact z.2

theorem dimLE_preimage_val {A : Set M} {p : ℕ} (h : DimLE (n := n) A p) (U : Opens M) :
    DimLE (n := n) ((↑) ⁻¹' A : Set U) p :=
  fun y k hy => h y k (regularAtDim_preimage_val_iff.mp hy)

theorem dimLE_image_val_iff {B : Set U} {p : ℕ} :
    DimLE (n := n) ((↑) '' B : Set M) p ↔ DimLE (n := n) B p := by
  constructor
  · intro h y k hy
    exact h y k (regularAtDim_image_val_iff.mpr hy)
  · intro h y k hy
    have hyU := mem_opens_of_regularAtDim_image_val hy
    exact h ⟨y, hyU⟩ k (regularAtDim_image_val_iff.mp hy)

theorem isPureDim_image_val_iff {B : Set U} {k : ℕ} :
    IsPureDim (n := n) ((↑) '' B : Set M) k ↔ IsPureDim (n := n) B k := by
  constructor
  · intro h y j hy
    exact h y j (regularAtDim_image_val_iff.mpr hy)
  · intro h y j hy
    have hyU := mem_opens_of_regularAtDim_image_val hy
    exact h ⟨y, hyU⟩ j (regularAtDim_image_val_iff.mp hy)

theorem nhds_opens_eq_comap (x : U) : 𝓝 x = comap ((↑) : U → M) (𝓝 (x : M)) :=
  nhds_induced _ _

theorem locDimGE_preimage_val_iff {A : Set M} {x : U} {q : ℕ} :
    LocDimGE (n := n) ((↑) ⁻¹' A : Set U) x q ↔ LocDimGE (n := n) A (x : M) q := by
  constructor
  · intro h W hW
    have hV : ((↑) ⁻¹' W : Set U) ∈ 𝓝 x := by
      rw [nhds_opens_eq_comap]; exact preimage_mem_comap hW
    obtain ⟨y, hyV, k, hqk, hy⟩ := h _ hV
    exact ⟨y, hyV, k, hqk, regularAtDim_preimage_val_iff.mp hy⟩
  · intro h V hV
    rw [nhds_opens_eq_comap, mem_comap] at hV
    obtain ⟨W, hW, hWV⟩ := hV
    obtain ⟨y, ⟨hyW, hyU⟩, k, hqk, hy⟩ :=
      h (W ∩ U) (inter_mem hW (U.isOpen.mem_nhds x.2))
    exact ⟨⟨y, hyU⟩, hWV hyW, k, hqk, regularAtDim_preimage_val_iff.mpr hy⟩

theorem locDimLE_preimage_val_iff {A : Set M} {x : U} {p : ℕ} :
    LocDimLE (n := n) ((↑) ⁻¹' A : Set U) x p ↔ LocDimLE (n := n) A (x : M) p := by
  constructor
  · rintro ⟨V, hV, hVp⟩
    rw [nhds_opens_eq_comap, mem_comap] at hV
    obtain ⟨W, hW, hWV⟩ := hV
    refine ⟨W ∩ U, inter_mem hW (U.isOpen.mem_nhds x.2), fun y hy k hyk => ?_⟩
    exact hVp ⟨y, hy.2⟩ (hWV hy.1) k (regularAtDim_preimage_val_iff.mpr hyk)
  · rintro ⟨W, hW, hWp⟩
    refine ⟨((↑) : U → M) ⁻¹' W, ?_, fun y hy k hyk =>
      hWp y hy k (regularAtDim_preimage_val_iff.mp hyk)⟩
    rw [nhds_opens_eq_comap]; exact preimage_mem_comap hW

/-! ### Holomorphic maps -/

/-- A map holomorphic on the open set `U` is holomorphic on the manifold `U`. -/
theorem contMDiff_restrict {m : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) Y] {f : M → Y}
    (hf : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f U) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ (fun x : U => f x) := fun x =>
  contMDiffAt_subtype_iff.mpr ((hf x x.2).contMDiffAt (U.isOpen.mem_nhds x.2))

end Hironaka.AnalyticSubsetOpens
