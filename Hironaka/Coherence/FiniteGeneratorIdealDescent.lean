/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Manifold.ComplexManifold
/-!
# Descent of finite local generators to a coherent germ ideal

A finite family of local holomorphic generators determines a global germ ideal
when the spans of the generators agree on overlaps.  This is the coherence
bridge needed by finite Bergman presentations: the analytic estimate supplies
the bounded remainder, while the overlap statement below supplies the actual
ideal descent.
-/

set_option autoImplicit false

open scoped Manifold

namespace Hironaka.FiniteGeneratorIdealDescent

open Hironaka.HolomorphicIdealSheaves

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- Equality of two finitely generated germ spans follows by checking that each
generator of either family lies in the span of the other.  This is the form
directly supplied by holomorphic transition matrices on a chart overlap. -/
theorem isInSpanAt_iff_of_generators_mutually_in_span
    {x : M} {p q : ℕ} (f : Fin p → M → ℂ) (g : Fin q → M → ℂ)
    (hfg : ∀ i, IsInSpanAt (n := n) (· ∈ Set.range f) x (g i))
    (hgf : ∀ i, IsInSpanAt (n := n) (· ∈ Set.range g) x (f i))
    (h : M → ℂ) :
    IsInSpanAt (n := n) (· ∈ Set.range g) x h ↔
      IsInSpanAt (n := n) (· ∈ Set.range f) x h := by
  constructor
  · intro hh
    refine Hironaka.RelativePrincipalizationSpan.IsInSpanAt.trans
      (n := n) ?_ hh
    intro s hs
    obtain ⟨i, rfl⟩ := hs
    exact hfg i
  · intro hh
    refine Hironaka.RelativePrincipalizationSpan.IsInSpanAt.trans
      (n := n) ?_ hh
    intro s hs
    obtain ⟨i, rfl⟩ := hs
    exact hgf i

end

end Hironaka.FiniteGeneratorIdealDescent
