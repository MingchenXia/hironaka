/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.DropMembers
import Hironaka.MarkedIdeal.CoefficientRestrictionTower
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The restricted coefficient ideal with the members containing `S` deleted

Source: Włodarczyk 2005, Lemmas `le:cf`, `le:S`, `le:S2` and Step 1a (the marked ideal `(S, 𝓒(𝓙)|_S, E_S, μ_𝓒)` with
`E_S` the members of `E` not containing `S`).

Step 1a needs the divisor `E_S` (the members containing `S` deleted); deleting them changes nothing along towers
with centres in the strict transforms of `S` (`DropMembers`). Combining the two:
-/

open Set

universe u

namespace Hironaka.CoefficientRestrictionDrop

open Hironaka.BlowupSequences NormalCrossings BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction CoefficientIdeal HomogenizedGlueingTower CoefficientRestrictionTower DropMembers

variable {n : ℕ} {X : CMfd.{u} n}

/-- The centres of a multiple test blow-up of a marked ideal with submanifold `S` lie in the strict transforms of `S`,
whatever its divisor. -/
theorem centresIn_of_isGeoTestTower_withN_withE (𝔟 : MarkedIdeal n X) (S : Set X) (E' : List (Set X)) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      IsGeoTestTower ({ withN 𝔟 S with E := E' } : MarkedIdeal n X) T → CentresIn S T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
      refine ⟨centresIn_of_isGeoTestTower_withN_withE 𝔟 S E' T hT0, fun x hx => ?_⟩
      have h1 := hC.subset_N hx
      rw [(geoTransformAlong_withE (withN 𝔟 S) E' T).1, N_geoTransformAlong_withN 𝔟 S T] at h1
      exact h1

end Hironaka.CoefficientRestrictionDrop
