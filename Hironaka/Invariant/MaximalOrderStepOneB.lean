/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.MarkedIdeal.HomogenizedGlueingAlongTower
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1b of the maximal-order case: the value does not depend on the hypersurface of maximal contact

Source: Włodarczyk 2005 (arXiv `hiron.tex`), Proposition `pr:resol`, Step 1bb: the invariant at a point is computed
on a hypersurface of maximal contact, and by the Glueing Lemma `le:homo` it does not depend on the choice of the
hypersurface ("`φ_{pu}^*(..) = φ_{pv}^*(..)`" along the part of the resolution after the hypersurface is chosen).

Let `J̄ = 𝓒_N(𝓗_N(𝔞), μ)` (`stepOneMarked`) be the marked ideal Step 1 works with, `u` a tangent direction of
`(𝔞|_N, μ)` on an open set, `T₀` the stage at which Step 1b starts and `T₁` the rest of the segment. Step 1b
evaluates the inductive invariant (in dimension `≤ k - 1`) on `𝓢_{u,T₀}|_W = (Y, strict transform of N ∩ V(u), E,
𝓒(J̄_{T₀}), μ_𝓒)|_W` (`contactMarked`) along the restricted tail `T₁|_{T₀⁻¹W}`. tail form of the glueing lifts
gives, for two tangent directions `u`, `v` at `x`, an isomorphism of the restricted tails over the lift `Φ₀` of the
glueing biholomorphism with `Φ₀^*𝓢_u = 𝓢_v` and fixing the cosupport pointwise; property (6) of the inductive
invariant (`ResolutionInvariant.towerIso`) then identifies the two values.

## Main results

* `stepOneMarked`, `contactMarked`: abbreviations for `J̄` and `𝓢_{u,T₀}|_W` (the forms tail theorem transports);
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u w

namespace Hironaka.MaximalOrderStepOneB

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism HomogenizedIdealAlong CoefficientIdealRestriction TangentDirectionAlong BlowupTowerIsomorphism HomogenizedGlueingAlongTower BlowupTowerIsoTail ResolutionInvariantSpec
open HomogenizedGlueingTower (strictAlong)

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The marked ideal of Step 1**: `J̄ = 𝓒_N(𝓗_N(𝔞), μ)`, the coefficient marked ideal of the homogenized marked ideal
along `N`. -/
abbrev stepOneMarked (N : Set M) (𝔞 : GermIdeal n M) (μ : ℕ) : MarkedIdeal n M :=
  coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)

/-- **The marked ideal of Step 1b on an open set of the stage `T₀`**: `𝓢_{u,T₀}|_W`, the coefficient marked ideal of
`J̄_{T₀}` on the strict transform along `T₀` of `N ∩ V(u)`, restricted to the open `W` of the last stage of `T₀`. -/
def contactMarked (N : Set M) (𝔞 : GermIdeal n M) (μ : ℕ) (u : M → ℂ) {Y : CMfd.{u} n}
    (T₀ : BlowupTower (CMfd.of (n := n) M) Y) (W : Opens Y) : MarkedIdeal n W :=
  MarkedIdeal.pullback (Subtype.val : W → Y)
    (withN (coeffMarkedAlong (geoTransformAlong (stepOneMarked N 𝔞 μ) T₀)) (strictAlong T₀ (N ∩ {x | u x = 0})))

end

end Hironaka.MaximalOrderStepOneB
