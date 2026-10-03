/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaPrincipalization
import Hironaka.Resolution.HironakaFromSeqInvariant
import Hironaka.Coherence.CartanIrreducible
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Invariant.RestrictEmptyTower
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Embedded resolution with a normal-crossings exceptional divisor (Hironaka)

Sources: Włodarczyk 2005 (`hiron.tex`), Theorem 1.0.2 (embedded desingularization); Bierstone--Milman 2008
(`bierstone-milman08-functoriality`), Theorem 1.2; Kollár 2007, Theorem 3.36.

**Statement.**  Let `X` be a compact complex manifold and `V ⊆ X` a closed irreducible analytic subvariety.  There is a finite
sequence of blowups with smooth centres `f : X' → X` and a divisor `E = (E₁, …, E_r)` on `X'` with simple normal crossings
such that

* the exceptional locus of `f` lies in `E₁ ∪ ⋯ ∪ E_r`, which lies over `V_sing`; so `f` is an isomorphism over `X \ V_sing`;
* the strict transform `V'` of `V` is a closed connected submanifold of dimension `dim V`;
* `V'` has only normal crossings with `E`.

(The divisor `E` is the support of the exceptional divisor of the tower, which lies over `V_sing`.

**Route.** The first-centre argument of `EmbeddedFromResolution` (`hir:embedded-from-resolution`) for the canonical
resolution of `(X, X, [], 𝓘_V, 1)` (`CanonicalCentres.canonicalInvariant`, coherence of `𝓘_V` by Cartan's theorem
`CartanIrreducible.cartanCoherence`): stop before the first centre `C` meeting the preimage of `X \ V_sing`; the
strict transform is the connected component of `C` through a point over `X \ V_sing`. New here: `C` is an admissible
centre of the transform, so it has only normal crossings with the transformed divisor, and so has each of its
connected components; the transformed divisor has simple normal crossings and its union is the support of the
exceptional divisor of the tower (`HironakaPrincipalization.support_exceptionalDivisor_eq_biUnion`), which contains
the exceptional locus and lies over `V_sing` because every centre so far does
(`support_exceptionalDivisor_subset_of_centresAvoid`).

## Main results

* `support_exceptionalDivisor_subset_of_centresAvoid`: if no centre of `T` meets the preimage of `U`, the support of the
  exceptional divisor of `T` lies over `X \ U`;
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold

universe u

namespace Hironaka.HironakaEmbeddedResolution

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings Hironaka.RestrictEmptyTower Hironaka.RegularLocusComponent Hironaka.EmbeddedFromResolution
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### The exceptional divisor of a tower whose centres avoid an open set -/

section Tower

variable {X : CMfd.{u} n}

/-- **If no centre of `T` meets the preimage of `U`, the support of the exceptional divisor of `T` lies over `X \ U`**: after
a blowup `π` along `C` the support is `π⁻¹(supp E_T) ∪ π⁻¹ C`, and `C` misses the preimage of `U`. -/
theorem support_exceptionalDivisor_subset_of_centresAvoid (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresAvoid U T →
      (BlowupTowerTransforms.exceptionalDivisor T).support ⊆ T.proj ⁻¹' (U : Set X)ᶜ
  | _, .refl, _ => by
      intro x hx
      exact absurd (hx (fun _ => (1 : ℂ)) (holomorphicAt_const 1)) one_ne_zero
  | _, .step T C π hπ, h => by
      obtain ⟨hT, hdisj⟩ : CentresAvoid U T ∧ Disjoint C (T.proj ⁻¹' (U : Set X)) := h
      have ih := support_exceptionalDivisor_subset_of_centresAvoid U T hT
      show (GermIdealTotalTransform.EffectiveDivisor.add
          (BlowupExceptionalDivisor.totalTransform hπ (BlowupTowerTransforms.exceptionalDivisor T))
          (BlowupExceptionalDivisor.exceptionalDivisor hπ)).support ⊆ _
      rw [HironakaPrincipalization.support_add, BlowupExceptionalDivisor.support_totalTransform,
        BlowupExceptionalDivisor.support_exceptionalDivisor]
      rintro z (hz | hz)
      · exact ih hz
      · exact fun hzU => Set.disjoint_left.mp hdisj hz hzU

end Tower

end

end Hironaka.HironakaEmbeddedResolution
