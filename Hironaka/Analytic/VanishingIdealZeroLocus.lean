/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.HolomorphicGermAlgebra

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The zero locus of a vanishing ideal is the set itself

Source: Copy-4, Step 5 of `prop:principalization`
(`transcendental-nakamaye-copy4-20260911`, `source/main-Nulllocus.tex:1845-1984`),
where the residual ideal `𝔟` of `eq:IV-H` is required to cut out *exactly* the
strict transform `W'`; blueprint `ana:principalization-data`.

`Copy4StepFiveExceptionalWeightData`
(`Pending/PrincipalizationCopy4StepFiveCoreReduction.lean:232`) records that
requirement as its field

  `psiIW_zeroLocus : psiIW_ideal.zeroLocus = W`,

and it had no producer.  When the ideal is taken to be `𝓘_W` — the choice the
modification side actually delivers, and the one
`AmbientIdealSourcesOfCoherentIdeals.exists_ambientIVLowerSource_of_vanishingIdeal_factorization`
already uses — the field is an elementary topological identity, *not* a
Nullstellensatz: by definition

  `𝓘_A.mem x g ↔ g holomorphic at x ∧ g = 0 on A near x`,
  `𝔞.zeroLocus = {x | ∀ g, 𝔞.mem x g → g x = 0}`.

One inclusion is `Filter.Eventually.self_of_nhds`; the other uses only that `A`
is closed, so that the constant germ `1` lies in `𝓘_A` at every point off `A`
(there `A` is empty near the point, and the vanishing condition is vacuous);
`HolomorphicGermAlgebra.holomorphicAt_const` supplies its holomorphy.

No analyticity, no coherence, and no compactness is needed, and the identity
fails for a non-closed `A`: for `A = M \ {x}` with `x` not isolated, `𝓘_A` at
`x` consists of the germs vanishing on a punctured neighbourhood, hence — by
continuity — vanishing at `x`, so `x ∈ 𝓘_A.zeroLocus \ A`.  That is why the
hypothesis is stated as `IsClosed`.

Everything here is sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.VanishingIdealZeroLocus

open Hironaka.HolomorphicIdealSheaves

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Every point of `A` lies in the zero locus of `𝓘_A`: a germ of `𝓘_A` at a
point of `A` vanishes on a neighbourhood intersected with `A`, in particular at
the point itself. -/
theorem subset_zeroLocus_vanishingIdeal (A : Set M) :
    A ⊆ (vanishingIdeal (n := n) A).zeroLocus := by
  intro x hx g hg
  exact hg.2.self_of_nhds hx

/-- Off a **closed** `A` the constant germ `1` belongs to `𝓘_A`, so the zero
locus of `𝓘_A` is contained in `A`. -/
theorem zeroLocus_vanishingIdeal_subset {A : Set M} (hA : IsClosed A) :
    (vanishingIdeal (n := n) A).zeroLocus ⊆ A := by
  intro x hx
  by_contra hxA
  have h1 : (vanishingIdeal (n := n) A).mem x (fun _ : M => (1 : ℂ)) := by
    refine ⟨holomorphicAt_const (n := n) (x := x) (1 : ℂ), ?_⟩
    filter_upwards [hA.isOpen_compl.mem_nhds hxA] with y hy hyA
    exact absurd hyA hy
  exact one_ne_zero (hx _ h1)

/-- **The residual ideal of `eq:IV-H` cuts out exactly the strict transform.**
For a closed `A`, `𝓘_A.zeroLocus = A`. -/
theorem zeroLocus_vanishingIdeal {A : Set M} (hA : IsClosed A) :
    (vanishingIdeal (n := n) A).zeroLocus = A :=
  subset_antisymm (zeroLocus_vanishingIdeal_subset hA)
    (subset_zeroLocus_vanishingIdeal A)

end

end Hironaka.VanishingIdealZeroLocus
