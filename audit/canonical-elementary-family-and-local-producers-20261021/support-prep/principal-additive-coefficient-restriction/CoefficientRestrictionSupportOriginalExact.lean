/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.MarkedIdeal.CoefficientAmbientMarkedDataExact

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CoefficientIdealRestriction

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal
  IdealWeightPowers BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal DerivativeIdealTower CoefficientIdeal
  HomogenizedGlueing HomogenizedGlueingTower MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal RestrictedIdealWeight BlowupStrictSubmanifold

noncomputable section

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

/-- **A multiple test blow-up of a restriction `𝔟|_S` has its centres in the strict transforms of `S`.** -/
theorem centresIn_of_isGeoTestTower_withN (𝔟 : MarkedIdeal n X) (S : Set X) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower (withN 𝔟 S) T → CentresIn S T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
      refine ⟨centresIn_of_isGeoTestTower_withN 𝔟 S T hT0, fun x hx => ?_⟩
      rw [← N_geoTransformAlong_withN 𝔟 S T]
      exact hC.subset_N hx

theorem isCoherent_coeffMarked {𝔪 : MarkedIdeal n X} (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) :
    (coeffMarked 𝔪).ideal.IsCoherent :=
  (isAmbientFamily_derivMarked hN h𝔞).isCoherent_msum

/-- **Włodarczyk `le:S`, the support** (GGT Proposition 5.6.4, first statement): for `𝔪 = (X, X, E, 𝔞, μ)` with
`𝔞` coherent and `μ ≥ 1`, and ANY set `S`, `supp(𝔪) ∩ S = supp(𝓒(𝔪)|_S)`. -/
theorem cosupp_coeff_withN (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d)
    (S : Set X) : (withN (coeffMarked 𝔪) S).cosupp = 𝔪.cosupp ∩ S := by
  refine Subset.antisymm (fun x hx => ⟨cosupport_coeff_subset hN h𝔞 hd S hx, hx.1⟩) ?_
  have h0 := (coeff_tower 𝔪 hN h𝔞 hd (BlowupTower.refl : BlowupTower X X)).2 trivial
  rw [geoTransformAlong_refl, geoTransformAlong_refl] at h0
  rw [← h0]
  exact cosupp_inter_subset_cosupp_withN (𝔟 := coeffMarked 𝔪) hN S

end Tower

end

end Hironaka.CoefficientIdealRestriction
