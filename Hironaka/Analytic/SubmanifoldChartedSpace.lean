/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Manifold.LocalHolomorphicOpenPartialExact
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.RegularLocusDense
import Hironaka.Manifold.HolomorphicContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A closed complex submanifold is a complex manifold in its own right

Source: Copy-4, `sec:prelim`; Griffiths--Harris Chapter 0 §2 (the local description of a
submanifold).  Nothing here is new mathematics: the content is that the project's *pointwise*
flattening datum `RegularAtDim W x k` assembles into a genuine
`ChartedSpace (ComplexModel k) ↥W` with holomorphic transitions, so that `↥W` carries
`IsComplexManifold k`.

This is the structure the modification side has had to route around: the manuscript restricts
divisors, weights and currents to the strict transform `W_m`, and every such restriction needs
`W_m` itself to be a complex manifold.  Only the *ambient* description was available before.

## The charts

Fix `x ∈ W` and let `e = complexChartAt x`, `Φ` the flattening supplied by
`RegularAtDim W x k`, so that on `S = e.source ∩ e⁻¹ Φ.source` one has
`y ∈ W ↔ Φ (e y) ∈ complexCoordinatePlane n k`.  The chart of `↥W` is

  `p ↦ coordinateProjection n k (Φ (e p))`,   with inverse   `ζ ↦ e.symm (Φ.symm (ι ζ))`,

`ι = coordinateInclusion n k` being `ζ ↦ (ζ, 0)`.  Its target is `ι ⁻¹' Φ.target`, which is
open because `ι` is continuous; the two round trips are
`coordinateProjection_coordinateInclusion` and `coordinateInclusion_coordinateProjection`,
the latter applied to the point `Φ (e p)`, which lies in the coordinate plane exactly because
`p ∈ W`.

## What this file does NOT claim

`↥W` is given no metric, no compactness and no connectedness, and the dimension `k` is a
parameter: a submanifold whose components have different dimensions is not covered (that is
`IsClosedSubmanifold`, whose dimension varies; `IsClosedConnectedSubmanifold` is the case
treated here).
-/

open Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.SubmanifoldChartedSpace

open Hironaka.RegularLocusDense Hironaka.RegularPatchNeighborhood
open Hironaka.BlowupSequences

noncomputable section

variable {n k : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- One flattening datum for `W ⊆ X` of dimension `k`: an ambient chart `amb`, a
biholomorphism `flat` defined on an open subset of its target, and the statement that `flat`
carries `W` onto the standard `k`-plane there.  `base` is any point of `W`, used only to make
the inverse chart map total.

This is exactly the content of `RegularAtDim`, repackaged so that the chart of the subtype can
be built from it and so that two such data can be compared (`FlatData.differentiableOn_trans`).
-/
structure FlatData (n k : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] (W : Set X) where
  /-- The ambient chart in which the flattening is written. -/
  amb : ComplexChart n X
  /-- The flattening biholomorphism, in `amb`-coordinates. -/
  flat : OpenPartialHomeomorph (ComplexModel n) (ComplexModel n)
  differentiableOn_flat : DifferentiableOn ℂ flat flat.source
  differentiableOn_flat_symm : DifferentiableOn ℂ flat.symm flat.target
  flat_source_subset : flat.source ⊆ amb.val.target
  /-- `flat` straightens `W` onto the standard `k`-plane. -/
  mem_iff : ∀ y ∈ amb.val.source, amb.val y ∈ flat.source →
      (y ∈ W ↔ flat (amb.val y) ∈ complexCoordinatePlane n k)
  /-- A base point of `W`, used only as the fallback value of the inverse chart. -/
  base : X
  base_mem : base ∈ W

namespace FlatData

variable {W : Set X}

/-- The ambient open set on which the flattened chart is defined. -/
def ambSource (F : FlatData n k X W) : Set X :=
  F.amb.val.source ∩ F.amb.val ⁻¹' F.flat.source

theorem isOpen_ambSource (F : FlatData n k X W) : IsOpen F.ambSource :=
  F.amb.val.isOpen_inter_preimage F.flat.open_source

/-- The flattened coordinate of a point of `W`. -/
def toCoord (F : FlatData n k X W) (p : W) : ComplexModel k :=
  coordinateProjection n k (F.flat (F.amb.val p.1))

/-- The point of `X` recovered from a flattened coordinate. -/
def ofCoord (F : FlatData n k X W) (ζ : ComplexModel k) : X :=
  F.amb.val.symm (F.flat.symm (coordinateInclusion n k ζ))

/-- The target of the flattened chart. -/
def coordTarget (F : FlatData n k X W) : Set (ComplexModel k) :=
  coordinateInclusion n k ⁻¹' F.flat.target

theorem isOpen_coordTarget (F : FlatData n k X W) : IsOpen F.coordTarget :=
  F.flat.open_target.preimage (coordinateInclusion n k).continuous

theorem ofCoord_mem_ambSource (F : FlatData n k X W) {ζ : ComplexModel k}
    (hζ : ζ ∈ F.coordTarget) : F.ofCoord ζ ∈ F.ambSource := by
  have hw : F.flat.symm (coordinateInclusion n k ζ) ∈ F.flat.source := F.flat.map_target hζ
  refine ⟨F.amb.val.map_target (F.flat_source_subset hw), ?_⟩
  rw [mem_preimage]
  show F.amb.val (F.amb.val.symm (F.flat.symm (coordinateInclusion n k ζ))) ∈ F.flat.source
  rw [F.amb.val.right_inv (F.flat_source_subset hw)]
  exact hw

theorem flat_amb_ofCoord (F : FlatData n k X W) {ζ : ComplexModel k}
    (hζ : ζ ∈ F.coordTarget) :
    F.flat (F.amb.val (F.ofCoord ζ)) = coordinateInclusion n k ζ := by
  have hw : F.flat.symm (coordinateInclusion n k ζ) ∈ F.flat.source := F.flat.map_target hζ
  rw [ofCoord, F.amb.val.right_inv (F.flat_source_subset hw), F.flat.right_inv hζ]

theorem ofCoord_mem (F : FlatData n k X W) {ζ : ComplexModel k} (hζ : ζ ∈ F.coordTarget) :
    F.ofCoord ζ ∈ W := by
  have hsrc := F.ofCoord_mem_ambSource hζ
  rw [F.mem_iff _ hsrc.1 hsrc.2, F.flat_amb_ofCoord hζ]
  exact coordinateInclusion_mem_complexCoordinatePlane ζ

theorem toCoord_ofCoord (F : FlatData n k X W) (hk : k ≤ n) {ζ : ComplexModel k}
    (hζ : ζ ∈ F.coordTarget) (h : F.ofCoord ζ ∈ W) :
    F.toCoord ⟨F.ofCoord ζ, h⟩ = ζ := by
  rw [toCoord, F.flat_amb_ofCoord hζ]
  exact coordinateProjection_coordinateInclusion hk ζ

/-- On its source the flattened coordinate of a point of `W` lies in the `k`-plane. -/
theorem coordinateInclusion_toCoord (F : FlatData n k X W) (p : W)
    (hp : p.1 ∈ F.ambSource) :
    coordinateInclusion n k (F.toCoord p) = F.flat (F.amb.val p.1) :=
  coordinateInclusion_coordinateProjection ((F.mem_iff _ hp.1 hp.2).1 p.2)

theorem toCoord_mem_coordTarget (F : FlatData n k X W) (p : W) (hp : p.1 ∈ F.ambSource) :
    F.toCoord p ∈ F.coordTarget := by
  rw [coordTarget, mem_preimage, F.coordinateInclusion_toCoord p hp]
  exact F.flat.map_source hp.2

theorem ofCoord_toCoord (F : FlatData n k X W) (p : W) (hp : p.1 ∈ F.ambSource) :
    F.ofCoord (F.toCoord p) = p.1 := by
  rw [ofCoord, F.coordinateInclusion_toCoord p hp, F.flat.left_inv hp.2,
    F.amb.val.left_inv hp.1]

theorem continuousOn_toCoord (F : FlatData n k X W) :
    ContinuousOn F.toCoord (Subtype.val ⁻¹' F.ambSource) := by
  have h1 : ContinuousOn (fun p : W => F.amb.val p.1) (Subtype.val ⁻¹' F.ambSource) :=
    F.amb.val.continuousOn.comp continuous_subtype_val.continuousOn fun p hp => hp.1
  have h2 : ContinuousOn (fun p : W => F.flat (F.amb.val p.1)) (Subtype.val ⁻¹' F.ambSource) :=
    F.flat.continuousOn.comp h1 fun p hp => hp.2
  exact (coordinateProjection n k).continuous.comp_continuousOn h2

theorem continuousOn_ofCoord (F : FlatData n k X W) :
    ContinuousOn F.ofCoord F.coordTarget := by
  have h1 : ContinuousOn (fun ζ => F.flat.symm (coordinateInclusion n k ζ)) F.coordTarget :=
    F.flat.continuousOn_symm.comp (coordinateInclusion n k).continuous.continuousOn fun _ hζ => hζ
  exact F.amb.val.continuousOn_symm.comp h1 fun _ hζ =>
    F.flat_source_subset (F.flat.map_target hζ)

open Classical in
/-- The ambient point produced by the inverse chart, made total by falling back to the base
point of `W` outside the chart target. -/
def invPointVal (F : FlatData n k X W) (ζ : ComplexModel k) : X :=
  if F.ofCoord ζ ∈ W then F.ofCoord ζ else F.base

theorem invPointVal_mem (F : FlatData n k X W) (ζ : ComplexModel k) :
    F.invPointVal ζ ∈ W := by
  classical
  rw [invPointVal]
  split_ifs with h
  · exact h
  · exact F.base_mem

theorem invPointVal_of_mem (F : FlatData n k X W) {ζ : ComplexModel k}
    (h : F.ofCoord ζ ∈ W) : F.invPointVal ζ = F.ofCoord ζ := by
  classical
  rw [invPointVal, if_pos h]

/-- The inverse chart map of `↥W`. -/
def invPoint (F : FlatData n k X W) (ζ : ComplexModel k) : W :=
  ⟨F.invPointVal ζ, F.invPointVal_mem ζ⟩

theorem invPoint_val (F : FlatData n k X W) {ζ : ComplexModel k} (hζ : ζ ∈ F.coordTarget) :
    (F.invPoint ζ : X) = F.ofCoord ζ :=
  F.invPointVal_of_mem (F.ofCoord_mem hζ)

theorem continuousOn_invPoint (F : FlatData n k X W) :
    ContinuousOn F.invPoint F.coordTarget := by
  have h : ContinuousOn F.invPointVal F.coordTarget :=
    F.continuousOn_ofCoord.congr fun ζ hζ => F.invPointVal_of_mem (F.ofCoord_mem hζ)
  rw [continuousOn_iff_continuous_domRestrict] at h ⊢
  exact h.subtype_mk _

/-- The flattened chart of `↥W` attached to one flattening datum.  Its source is the part of
`W` lying in the ambient chart, its target the open set `ι ⁻¹' Φ.target ⊆ ℂᵏ`. -/
def chart (F : FlatData n k X W) (hk : k ≤ n) : OpenPartialHomeomorph W (ComplexModel k) where
  toFun := F.toCoord
  invFun := F.invPoint
  source := Subtype.val ⁻¹' F.ambSource
  target := F.coordTarget
  map_source' := fun p hp => F.toCoord_mem_coordTarget p hp
  map_target' := fun ζ hζ => by
    rw [mem_preimage, F.invPoint_val hζ]
    exact F.ofCoord_mem_ambSource hζ
  left_inv' := fun p hp => by
    have h : F.ofCoord (F.toCoord p) ∈ W := by rw [F.ofCoord_toCoord p hp]; exact p.2
    refine Subtype.ext ?_
    show F.invPointVal (F.toCoord p) = (p : X)
    rw [F.invPointVal_of_mem h]
    exact F.ofCoord_toCoord p hp
  right_inv' := fun ζ hζ => by
    have h := F.ofCoord_mem hζ
    have hv : F.invPoint ζ = (⟨F.ofCoord ζ, h⟩ : W) :=
      Subtype.ext (F.invPointVal_of_mem h)
    rw [hv]
    exact F.toCoord_ofCoord hk hζ h
  open_source := F.isOpen_ambSource.preimage continuous_subtype_val
  open_target := F.isOpen_coordTarget
  continuousOn_toFun := F.continuousOn_toCoord
  continuousOn_invFun := F.continuousOn_invPoint

@[simp] theorem chart_source (F : FlatData n k X W) (hk : k ≤ n) :
    (F.chart hk).source = Subtype.val ⁻¹' F.ambSource := rfl

@[simp] theorem chart_target (F : FlatData n k X W) (hk : k ≤ n) :
    (F.chart hk).target = F.coordTarget := rfl

@[simp] theorem chart_apply (F : FlatData n k X W) (hk : k ≤ n) (p : W) :
    F.chart hk p = F.toCoord p := rfl

theorem chart_symm_apply (F : FlatData n k X W) (hk : k ≤ n) (ζ : ComplexModel k) :
    (F.chart hk).symm ζ = F.invPoint ζ := rfl

/-! ### Holomorphy of the transitions -/

/-- The overlap of two flattened charts, read in the coordinates of the first. -/
def transSource (F G : FlatData n k X W) : Set (ComplexModel k) :=
  F.coordTarget ∩ F.ofCoord ⁻¹' G.ambSource

theorem isOpen_transSource (F G : FlatData n k X W) : IsOpen (transSource F G) :=
  F.continuousOn_ofCoord.isOpen_inter_preimage F.isOpen_coordTarget G.isOpen_ambSource

/-- The transition between two flattened charts is holomorphic on the overlap: it is
`proj_k ∘ Ψ ∘ (ambient transition) ∘ Φ.symm ∘ ι`, and each factor is holomorphic where it is
applied. -/
theorem differentiableOn_transMap (F G : FlatData n k X W) :
    DifferentiableOn ℂ
      (fun ζ => coordinateProjection n k (G.flat (G.amb.val (F.ofCoord ζ))))
      (transSource F G) := by
  have hmemtarget : ∀ ζ ∈ transSource F G,
      F.flat.symm (coordinateInclusion n k ζ) ∈ F.flat.source := fun _ hζ =>
    F.flat.map_target hζ.1
  have h1 : DifferentiableOn ℂ (fun ζ : ComplexModel k => coordinateInclusion n k ζ)
      (transSource F G) := (coordinateInclusion n k).differentiable.differentiableOn
  have h2 : DifferentiableOn ℂ (fun ζ => F.flat.symm (coordinateInclusion n k ζ))
      (transSource F G) :=
    F.differentiableOn_flat_symm.comp h1 fun _ hζ => hζ.1
  have h3 : DifferentiableOn ℂ
      (fun ζ => chartTransition F.amb G.amb (F.flat.symm (coordinateInclusion n k ζ)))
      (transSource F G) := by
    refine (differentiableOn_chartTransition F.amb G.amb).comp h2 fun ζ hζ => ?_
    have hw := hmemtarget ζ hζ
    refine ⟨F.flat_source_subset hw, ?_⟩
    rw [mem_preimage]
    exact hζ.2.1
  have h4 : DifferentiableOn ℂ
      (fun ζ => G.flat (G.amb.val (F.ofCoord ζ))) (transSource F G) := by
    refine G.differentiableOn_flat.comp h3 fun ζ hζ => ?_
    exact hζ.2.2
  exact (coordinateProjection n k).differentiable.comp_differentiableOn h4

theorem contDiffOn_transMap (F G : FlatData n k X W) :
    ContDiffOn ℂ ∞ (fun ζ => coordinateProjection n k (G.flat (G.amb.val (F.ofCoord ζ))))
      (transSource F G) :=
  contDiffOn_of_differentiableOn_complex (differentiableOn_transMap F G)
    (isOpen_transSource F G)

theorem chart_target_inter_preimage (F G : FlatData n k X W) (hk : k ≤ n) :
    (F.chart hk).target ∩ ((F.chart hk).symm ⁻¹' (G.chart hk).source) = transSource F G := by
  ext ζ
  simp only [chart_source, chart_target, mem_inter_iff, mem_preimage, transSource]
  refine and_congr_right fun hζ => ?_
  rw [show ((F.chart hk).symm ζ : X) = F.ofCoord ζ from F.invPoint_val hζ]

/-- The flattened transition equals the chart transition of `↥W` on the overlap. -/
theorem toCoord_invPoint_eqOn (F G : FlatData n k X W) :
    EqOn (fun ζ => G.toCoord (F.invPoint ζ))
      (fun ζ => coordinateProjection n k (G.flat (G.amb.val (F.ofCoord ζ))))
      (transSource F G) := fun ζ hζ => by
  show coordinateProjection n k (G.flat (G.amb.val (F.invPoint ζ).1)) = _
  rw [F.invPoint_val hζ.1]

/-! ### The flattening datum supplied by a regular point -/

/-- The flattening datum extracted from `RegularAtDim W x k`, in the preferred chart at `x`. -/
def ofRegularAtDim {W : Set X} {x : X} (h : RegularAtDim (n := n) W x k) :
    FlatData n k X W :=
  let Φ := h.2.2.choose
  { amb := complexChartAt (n := n) x
    flat := LocalHolomorphicEquivAt.toOpenPartialHomeomorph Φ
    differentiableOn_flat := Φ.toFun_holomorphic
    differentiableOn_flat_symm := Φ.invFun_holomorphic
    flat_source_subset := h.2.2.choose_spec.1
    mem_iff := fun _ hy hyΦ => h.2.2.choose_spec.2.2 hy hyΦ
    base := x
    base_mem := h.2.1 }

theorem mem_ambSource_ofRegularAtDim {W : Set X} {x : X} (h : RegularAtDim (n := n) W x k) :
    x ∈ (ofRegularAtDim (k := k) h).ambSource :=
  ⟨mem_complexChartAt_source x, h.2.2.choose.center_mem_source⟩

end FlatData

/-! ### The charted space -/

variable (n) in
/-- The atlas of `↥W`: all charts coming from a flattening datum. -/
def submanifoldAtlas (W : Set X) (k : ℕ) (hk : k ≤ n) :
    Set (OpenPartialHomeomorph W (ComplexModel k)) :=
  {e | ∃ F : FlatData n k X W, e = F.chart hk}

/-- **A closed complex submanifold of dimension `k` is a charted space over `ℂᵏ`.**  The charts
are the flattening charts of `FlatData`; the topology on `↥W` is the subspace topology, not a
new one. -/
@[instance_reducible] def chartedSpace {W : Set X} {k : ℕ} (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) : ChartedSpace (ComplexModel k) W where
  atlas := submanifoldAtlas n W k hk
  chartAt := fun p => (FlatData.ofRegularAtDim (hW p.1 p.2)).chart hk
  mem_chart_source := fun p => FlatData.mem_ambSource_ofRegularAtDim (hW p.1 p.2)
  chart_mem_atlas := fun _p => ⟨_, rfl⟩


/-! ### The complex structure -/

/-- The transitions of the flattened atlas are holomorphic, so `↥W` is a complex manifold in
mathlib's sense for the charted-space structure of `chartedSpace`. -/
theorem isManifold_chartedSpace {W : Set X} {k : ℕ} (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    IsManifold 𝓘(ℂ, ComplexModel k) ∞ W := by
  let := chartedSpace hk hW
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
  obtain ⟨F, rfl⟩ := he
  obtain ⟨G, rfl⟩ := he'
  have hsrc := FlatData.chart_target_inter_preimage F G hk
  simp only [mfld_simps]
  rw [hsrc]
  exact (FlatData.contDiffOn_transMap F G).congr (FlatData.toCoord_invPoint_eqOn F G)

/-- **A closed complex submanifold of dimension `k` of a complex manifold is itself a complex
manifold of dimension `k`.**  Hausdorffness and second countability are inherited from the
ambient manifold, the atlas is the flattening atlas, and the transitions are holomorphic. -/
theorem isComplexManifold_chartedSpace {W : Set X} {k : ℕ} (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    IsComplexManifold k W := by
  let := chartedSpace hk hW
  have := isManifold_chartedSpace hk hW
  exact { }

/-- The existence form, convenient for consumers: a closed complex submanifold of dimension `k`
carries a charted-space structure over `ℂᵏ` making it a complex manifold. -/
theorem exists_chartedSpace_isComplexManifold {W : Set X} {k : ℕ} (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) :
    ∃ cs : ChartedSpace (ComplexModel k) W,
      @IsComplexManifold k W _ cs :=
  ⟨chartedSpace hk hW, isComplexManifold_chartedSpace hk hW⟩

/-- `k ≤ n` is not an extra hypothesis for a closed *connected* submanifold: `W` is nonempty and
`RegularAtDim` carries the bound at any of its points. -/
theorem le_of_isClosedConnectedSubmanifold {W : Set X} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) : k ≤ n :=
  let ⟨y, hy⟩ := hW.2.1.nonempty
  (hW.2.2 y hy).1

/-- The dimension-`k` case of `IsClosedConnectedSubmanifold`. -/
theorem exists_chartedSpace_of_isClosedConnectedSubmanifold {W : Set X} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) :
    ∃ cs : ChartedSpace (ComplexModel k) W,
      @IsComplexManifold k W _ cs :=
  exists_chartedSpace_isComplexManifold (le_of_isClosedConnectedSubmanifold hW) hW.2.2

/-! ### The inclusion is holomorphic -/

section Inclusion

variable {W : Set X} {k : ℕ} (hk : k ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)

/-- Read in the flattening chart of `↥W` and the ambient chart it came from, the inclusion
`↥W → X` is `ζ ↦ Φ.symm (ι ζ)`. -/
theorem differentiableOn_flatSymmIncl (F : FlatData n k X W) :
    DifferentiableOn ℂ (fun ζ => F.flat.symm (coordinateInclusion n k ζ)) F.coordTarget :=
  F.differentiableOn_flat_symm.comp
    ((coordinateInclusion n k).differentiable.differentiableOn) fun _ hζ => hζ

theorem amb_ofCoord (F : FlatData n k X W) {ζ : ComplexModel k} (hζ : ζ ∈ F.coordTarget) :
    F.amb.val (F.ofCoord ζ) = F.flat.symm (coordinateInclusion n k ζ) :=
  F.amb.val.right_inv (F.flat_source_subset (F.flat.map_target hζ))

include hk hW in
theorem chart_mem_atlas (F : FlatData n k X W) :
    letI := chartedSpace hk hW
    F.chart hk ∈ atlas (ComplexModel k) W := ⟨F, rfl⟩

include hk hW in
theorem contMDiffOn_val (F : FlatData n k X W) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ContMDiffOn 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X)
      (F.chart hk).source := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  refine (contMDiffOn_iff_of_mem_maximalAtlas' (e := F.chart hk) (e' := F.amb.val)
    (IsManifold.subset_maximalAtlas (chart_mem_atlas hk hW F))
    (IsManifold.subset_maximalAtlas F.amb.property) le_rfl
    (fun q hq => (hq : q.1 ∈ F.ambSource).1)).2 ?_
  simp only [mfld_simps]
  rw [OpenPartialHomeomorph.image_source_eq_target, FlatData.chart_target]
  refine (contDiffOn_of_differentiableOn_complex (differentiableOn_flatSymmIncl F)
      F.isOpen_coordTarget).congr fun ζ hζ => ?_
  show F.amb.val (((F.chart hk).symm ζ : W) : X) = F.flat.symm (coordinateInclusion n k ζ)
  rw [show (((F.chart hk).symm ζ : W) : X) = F.ofCoord ζ from F.invPoint_val hζ]
  exact amb_ofCoord F hζ

include hk hW in
/-- **The inclusion of a closed complex submanifold is holomorphic.**  In the flattening chart
of `↥W` and the ambient chart it came from, the inclusion reads `ζ ↦ Φ.symm (ι ζ)`. -/
theorem contMDiff_val :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro p
  set F := FlatData.ofRegularAtDim (hW p.1 p.2) with hF
  have hp : p ∈ (F.chart hk).source := FlatData.mem_ambSource_ofRegularAtDim (hW p.1 p.2)
  exact (contMDiffOn_val hk hW F).contMDiffAt ((F.chart hk).open_source.mem_nhds hp)

end Inclusion

variable (n) in
/-- Holomorphy of the inclusion `↥W → X` for a *given* charted-space structure on the subtype.
Naming it lets the submanifold package be stated as one existential; `letI` cannot be used
inside a parenthesised subterm. -/
def InclusionHolomorphicFor (k : ℕ) (W : Set X) (cs : ChartedSpace (ComplexModel k) W) : Prop :=
  letI := cs
  ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X)

/-- **The submanifold package.**  A closed complex submanifold `W` of dimension `k` of a complex
manifold `X` carries a charted-space structure over `ℂᵏ` — on the subtype, with its subspace
topology — for which `↥W` is a complex manifold of dimension `k` and the inclusion `↥W → X` is
holomorphic.  No compactness, connectedness or Kähler hypothesis is used. -/
theorem exists_submanifoldStructure {W : Set X} {k : ℕ} (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) :
    ∃ cs : ChartedSpace (ComplexModel k) W,
      @IsComplexManifold k W _ cs ∧ InclusionHolomorphicFor n k W cs :=
  ⟨chartedSpace hk hW, isComplexManifold_chartedSpace hk hW, contMDiff_val hk hW⟩

/-- `exists_submanifoldStructure` for the project's `IsClosedConnectedSubmanifold`; `k ≤ n` comes
from `le_of_isClosedConnectedSubmanifold`. -/
theorem exists_submanifoldStructure_of_isClosedConnectedSubmanifold {W : Set X} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) :
    ∃ cs : ChartedSpace (ComplexModel k) W,
      @IsComplexManifold k W _ cs ∧ InclusionHolomorphicFor n k W cs :=
  exists_submanifoldStructure (le_of_isClosedConnectedSubmanifold hW) hW.2.2

end

end Hironaka.SubmanifoldChartedSpace
