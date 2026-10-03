/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
/-!
# Complex manifolds and real differential forms in charts

The manifold structure is mathlib's holomorphic chart compatibility, together
with the usual Hausdorff and second-countability conditions. A real differential
form is represented by smooth continuous alternating forms in these charts,
with the ordinary real derivative in the change-of-coordinates equation.

Coefficient functions are extended arbitrarily outside their chart targets;
only their restrictions to those open targets have geometric meaning. No global
exterior-derivative operator or coordinate-independence theorem is assumed here.
-/

open scoped Manifold ContDiff
open Set

namespace Hironaka

noncomputable section

/-- The standard complex vector space of complex dimension `n`. -/
abbrev ComplexModel (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- A Hausdorff, second-countable complex manifold, using mathlib's actual
charts and holomorphic transition maps. This imposes no metric or compactness. -/
class IsComplexManifold (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] : Prop extends
    T2Space M, SecondCountableTopology M, IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M

instance (n : ℕ) : IsComplexManifold n (ComplexModel n) where

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- A chart belonging to the specified atlas (not an arbitrary homeomorphism). -/
abbrev ComplexChart (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] :=
  {e : OpenPartialHomeomorph M (ComplexModel n) // e ∈ atlas (ComplexModel n) M}

/-- The preferred chart around a point. -/
def complexChartAt (x : M) : ComplexChart n M :=
  ⟨chartAt (ComplexModel n) x, chart_mem_atlas (ComplexModel n) x⟩

theorem mem_complexChartAt_source (x : M) :
    x ∈ (complexChartAt (n := n) x).val.source :=
  mem_chart_source (ComplexModel n) x

/-- Change from `e`-coordinates to `f`-coordinates, on its actual overlap. -/
def chartTransition (e f : ComplexChart n M) :
    OpenPartialHomeomorph (ComplexModel n) (ComplexModel n) :=
  e.val.symm.trans f.val

/-- Holomorphic overlap compatibility comes from the manifold structure. -/
theorem chartTransition_mem_groupoid [IsComplexManifold n M]
    (e f : ComplexChart n M) :
    chartTransition e f ∈ contDiffGroupoid ∞ (𝓘(ℂ, ComplexModel n)) :=
  StructureGroupoid.compatible _ e.property f.property

end

end Hironaka
