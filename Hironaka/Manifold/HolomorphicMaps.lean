/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Manifold.ComplexManifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
/-!
# Holomorphic maps in actual manifold charts

The coordinate domain records both chart conditions. All differentiability
statements below follow from mathlib's `ContMDiff` predicate. In particular,
complex linearity of the real derivative is proved by restriction of scalars,
not postulated as an additional geometric compatibility condition.
-/

open scoped Manifold ContDiff Topology
open Set Filter

namespace Hironaka.HolomorphicMaps

noncomputable section

variable {k n : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- The actual coordinate representative of a map between complex manifolds. -/
def coordinateMap (f : V → M) (e : ComplexChart k V) (d : ComplexChart n M) :
    ComplexModel k → ComplexModel n := d.val ∘ f ∘ e.val.symm

/-- The open domain where both charts in a coordinate representative are valid. -/
def coordinateDomain (f : V → M) (e : ComplexChart k V) (d : ComplexChart n M) :
    Set (ComplexModel k) := e.val.target ∩ e.val.symm ⁻¹' (f ⁻¹' d.val.source)

theorem coordinateDomain_isOpen {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (e : ComplexChart k V) (d : ComplexChart n M) :
    IsOpen (coordinateDomain f e d) :=
  e.val.isOpen_inter_preimage_symm (d.val.open_source.preimage hf.continuous)

theorem mem_coordinateDomain {f : V → M} {e : ComplexChart k V}
    {d : ComplexChart n M} {x : V} (hx : x ∈ e.val.source)
    (hfx : f x ∈ d.val.source) : e.val x ∈ coordinateDomain f e d := by
  exact ⟨e.val.map_source hx, by simpa only [mem_preimage, e.val.left_inv hx] using hfx⟩

variable [IsComplexManifold k V] [IsComplexManifold n M]

theorem coordinateMap_contDiffAt {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (e : ComplexChart k V) (d : ComplexChart n M)
    {z : ComplexModel k} (hz : z ∈ coordinateDomain f e d) :
    ContDiffAt ℂ ∞ (coordinateMap f e d) z := by
  have h := (contMDiffAt_iff_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas e.property)
    (IsManifold.subset_maximalAtlas d.property)
    (e.val.map_target hz.1) hz.2).mp (hf (e.val.symm z))
  simpa [coordinateMap, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, e.val.right_inv hz.1,
    contDiffWithinAt_univ] using h.2

end

end Hironaka.HolomorphicMaps
