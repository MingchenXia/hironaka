/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Blowup.NormalCrossings
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Marked ideals, admissible blowups, transforms and multiple test blowups

Sources: Bierstone--Milman 2008, Definitions 2.1--2.2 (marked ideal `(M, N, E, 𝓘, d)`, cosupport, admissible
blowing-up, transform) and Theorem 1.3; Włodarczyk 2005 §2.1--2.2 (marked ideals `(X, 𝓘, E, μ)`, resolutions,
multiple test blow-ups, controlled transforms).

## Encoding (decision D1)

* `N` is a SUBSET of the ambient manifold (a closed submanifold for well-formed data), never a
  separate manifold type: the ambient spaces of a tower are the only types.
* The ideal of `𝒪_N` is represented by an ambient `GermIdeal` (`ideal`); only the restrictions of its
  germs to `N` matter (`GermIdealOrder.VanishesToOrderOn`).  For `N = M` this is Włodarczyk's
  `(X, 𝓘, E, μ)`.
* `E` is a list of subsets; the transform appends the exceptional divisor `π⁻¹ C` as the LAST
  member (BM08: "introduced as the last member of `E'`"; Włodarczyk: "`D_i` is the maximal element").
* Strict transforms are taken relative to the centre, `closure (π⁻¹ (A \ C))`
  (`BlowupStrictSubmanifold.geoStrictTransform`), for `N` and for the members of `E`: along a centre of codimension
  one the blowup is a biholomorphism, and the strict transform `closure (π⁻¹ A \ Exc π)` would keep `A ∩ C`. The
  transform is therefore the same as `MarkedIdealGeoTransform.geoTransform`.
* The transform of the ideal is the ambient form of `𝓘' = 𝓘_{π⁻¹C}^{-d} π^*𝓘` on `N'`: the colon, along the strict
  transform `N'`, of `π^*𝓘` by `(π^* 𝓘_C)^d`.
* All data are raw (no proof fields); well-formedness (`IsWellFormed`) and admissibility are separate
  predicates, so transforms are total functions and the bookkeeping lemmas below are definitional.

## Main declarations

* `MarkedIdeal n M`, `cosupp`, `IsWellFormed`, `IsAdmissibleCentre`, `transform`;

No statement about the EXISTENCE of resolutions is made here.
-/

open Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.MarkedIdeals

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.NormalCrossings
open Hironaka.BlowupTowers Hironaka.IdealWeightPowers
open Hironaka.RestrictedIdealQuotient
open Hironaka.BlowupStrictSubmanifold

noncomputable section

/-- **A marked ideal** `(M, N, E, 𝓘, d)` on the ambient manifold `M` (BM08 Definitions 2.1): the
submanifold `N ⊆ M`, the ordered divisor `E = [H₁, …, H_s]`, an ambient representative `ideal` of the
ideal `𝓘 ⊆ 𝒪_N`, and the mark `d`. -/
structure MarkedIdeal (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] where
  /-- The submanifold carrying the ideal. -/
  N : Set M
  /-- The ordered normal crossings divisor (newest member last). -/
  E : List (Set M)
  /-- An ambient representative of the ideal of `𝒪_N`. -/
  ideal : GermIdeal n M
  /-- The mark. -/
  d : ℕ

namespace MarkedIdeal

section OneSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **The cosupport** `{x ∈ N | ord_x 𝓘 ≥ d}`. -/
def cosupp (𝔪 : MarkedIdeal n M) : Set M :=
  cosupport n 𝔪.N 𝔪.ideal 𝔪.d

theorem cosupp_subset_N (𝔪 : MarkedIdeal n M) : 𝔪.cosupp ⊆ 𝔪.N :=
  cosupport_subset _

variable [IsComplexManifold n M]

/-- **Well-formed marked ideal** (BM08 Definitions 2.1): `N` a closed submanifold, the ideal coherent,
`E` an ordered simple normal crossings divisor transverse to `N`. -/
structure IsWellFormed (𝔪 : MarkedIdeal n M) : Prop where
  isClosedSubmanifold_N : IsClosedSubmanifold n 𝔪.N
  isCoherent : 𝔪.ideal.IsCoherent
  isSNCDivisor : IsSNCDivisor n 𝔪.E
  isTransverse : IsTransverse n 𝔪.N 𝔪.E

/-- **An admissible centre** (BM08 Definitions 2.2; Włodarczyk §2.1 conditions (1)--(2)): a closed
submanifold contained in the cosupport and having only normal crossings with `E`. -/
def IsAdmissibleCentre (𝔪 : MarkedIdeal n M) (C : Set M) : Prop :=
  IsClosedSubmanifold n C ∧ C ⊆ 𝔪.cosupp ∧ HasNormalCrossings n C 𝔪.E

theorem IsAdmissibleCentre.subset_N {𝔪 : MarkedIdeal n M} {C : Set M}
    (h : 𝔪.IsAdmissibleCentre C) : C ⊆ 𝔪.N :=
  h.2.1.trans 𝔪.cosupp_subset_N

/-- The empty centre is admissible. -/
theorem isAdmissibleCentre_empty (𝔪 : MarkedIdeal n M) : 𝔪.IsAdmissibleCentre ∅ :=
  ⟨⟨isClosed_empty, fun _ h => absurd h (notMem_empty _)⟩, empty_subset _,
    fun _ h => absurd h (notMem_empty _)⟩

end OneSpace

end MarkedIdeal

end

end Hironaka.MarkedIdeals
