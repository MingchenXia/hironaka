/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.StrictTransformSubvariety
import Hironaka.Analytic.SingularLocus
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Strict transforms along a sequence of blowups

The one-blowup strict-transform construction is iterated along an
`IsBlowupSequence`.  If the original subvariety is not contained in the image
of the exceptional locus of the complete sequence, the same is true at every
stage: exceptional images of earlier stages lie in that final image, and the
strict transform is not contained in the exceptional image of the next stage.

The resulting strict transform is a closed irreducible analytic subvariety.
Its carrier is connected without an additional resolution-theoretic input: an
irreducible analytic set is the closure of the regular component through any
of its regular points, and closures of connected sets are connected.
-/

open Set
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StrictTransformSubvarietySequence

open Hironaka.BlowupSequences RegularLocusComponent

noncomputable section

variable {n : ℕ}
  {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X]
  {Xt : Type u} [TopologicalSpace Xt] [ChartedSpace (ComplexModel n) Xt]
    [IsComplexManifold n Xt]

/-- Exceptional-image control by the singular locus ensures that an irreducible subvariety
has a point outside the exceptional image. -/
theorem not_subset_image_exceptionalLocus_of_image_exceptionalLocus_subset_singular
    (V : ClosedIrreducibleAnalyticSubvariety n X) {μ : Xt → X}
    (hExcS : μ '' exceptionalLocus n μ ⊆ singularLocus V) :
    ¬ V.carrier ⊆ μ '' exceptionalLocus n μ := by
  obtain ⟨x, hx⟩ := V.regularLocus_nonempty
  intro hV
  exact (hExcS (hV (regularLocus_subset _ _ hx))).2 hx

end

end Hironaka.StrictTransformSubvarietySequence
