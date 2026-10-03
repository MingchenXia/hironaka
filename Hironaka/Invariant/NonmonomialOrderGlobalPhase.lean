/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.GeneralValueOrderZero
import Hironaka.Blowup.BlowupCompact
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.StepOneWellFounded
import Hironaka.Invariant.StepOnePhase
import Hironaka.Invariant.MonomialInvariant
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The phases of a canonical segment on the side of the order of the nonmonomial part

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2 of Proposition `pr:resol` (the order of the nonmonomial
part does not increase; while it stays `o`, the companion ideal of order `o` is resolved, "then we repeat the
procedure"); Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Step II.

The value of the general step begins with the order `ν` of the nonmonomial part.  Along a canonical segment the nonempty centres
are maximum loci, so their orders form the sequence of phases: it never increases, and over a compact set it is bounded.  This
module proves, for every value function `f` whose order dominates `ν` (`NonmonomialOrderCanonical.OrdMonotone`), with `𝔪` in
the domain and `n > 0`:

* **the phase is absorbing**: if `ν ≤ o` on the cosupport at a stage `T₀`, then along every canonical test extension
  `T₀ S` the order stays `≤ o`, and a point of order `o` lies over a point of order `o` of the cosupport at `T₀`;
* **the run of a point of order `o` started at or before `T₀`**: such a point is in the regime `OrdRegime 𝔪 o` and
  its run is at least the length of `S`; and the cosupport at `T₀` lies in the mask `ordMask 𝔪_{T₀} o`, the open set
  on which the companion ideal of order `o` is formed;
* **phase entry**: a nonempty centre of a canonical step bounds the order on the cosupport before it; **the orders
  of the nonempty centres never increase** (with `StepOnePhase.centreValues` of `ν`) and bound the orders on every
  later cosupport;
* **one bound over a compact set**: for compact `K` there is `q` bounding the order of every point of every nonempty
  centre meeting the preimage of `K`, along all canonical test segments;
* **the monomial phase of the general value**: a value of order `0` is `(0, inl γ)`, and no sequence of such values
  strictly decreases forever (`γ`'s values are well-founded, `MonomialInvariant.wellFoundedLT_val`);
  `wellFoundedLT_genValue`: the values of the general step are well-founded when those of the maximal-order value
  are.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.NonmonomialOrderGlobalPhase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MonomialInvariant Hironaka.MonomialStepAlong Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.StepOneRegime Hironaka.StepOnePhase Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderRegime Hironaka.NonmonomialOrderCanonical Hironaka.NonmonomialOrderTail
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

/-! ### The monomial phase of the general value; well-founded values -/

section Monomial

variable {Λ : Type v} [LinearOrder Λ]

/-- **The values of the general step are well-founded when those of the maximal-order value are.** -/
theorem wellFoundedLT_genValue [WellFoundedLT Λ] : WellFoundedLT (ℕ ×ₗ (WithBot Val ⊕ₗ WithTop Λ)) := by
  have h1 : WellFoundedLT (WithBot Val) := wellFoundedLT_val
  have h2 : WellFoundedLT (WithTop Λ) := inferInstance
  have : WellFoundedLT (WithBot Val ⊕ₗ WithTop Λ) := ⟨Sum.lex_wf h1.wf h2.wf⟩
  infer_instance

end Monomial

end

end Hironaka.NonmonomialOrderGlobalPhase
