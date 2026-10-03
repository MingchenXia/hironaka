/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.ExceptionalFibres
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Blowup.ExceptionalLocus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A blowup sequence is an isomorphism off the image of its exceptional locus

For a finite blowup sequence `f : Y → X`, every fibre through a point outside
`Exc(f)` is a singleton.  This follows by induction: for `f ∘ g`, the chain
rule identifies non-exceptionality of a point with non-exceptionality both for
`g` and for `f` at its image.  The two singleton-fibre statements then compose.

When `X` is compact, a blowup sequence is surjective.  Consequently an
exceptional-image containment `f(Exc(f)) ⊆ A` internally gives an isomorphism
over `Aᶜ`.  This is the structural part of the usual statement that a
modification is an isomorphism away from its exceptional image; it does not
assert that any finite truncation satisfies a global analytic identity.
-/

open Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.BlowupSequenceIsomorphismOff

open Hironaka.BlowupSequences

noncomputable section

variable {n : ℕ}
  {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y]

/-- A fibre of a blowup sequence through a non-exceptional point is a singleton. -/
theorem eq_of_apply_eq_of_not_mem_exceptionalLocus {f : Y → X}
    (hf : IsBlowupSequence n X Y f) {y y' : Y} (hy : y ∉ exceptionalLocus n f)
    (h : f y' = f y) : y' = y := by
  induction hf with
  | refl => simpa using h
  | step f C g hfg hg ih =>
      have hy' : y ∉ exceptionalLocus n g ∧ g y ∉ exceptionalLocus n f := by
        rw [exceptionalLocus_comp (hfg.contMDiff.mdifferentiable (by simp))
          (hg.contMDiff.mdifferentiable (by simp))] at hy
        simpa only [mem_union, mem_preimage, not_or] using hy
      have hgy : g y' = g y := ih hy'.2 h
      exact ExceptionalFibres.eq_of_apply_eq_of_not_mem_exceptionalLocus hg hy'.1 hgy

end

end Hironaka.BlowupSequenceIsomorphismOff
