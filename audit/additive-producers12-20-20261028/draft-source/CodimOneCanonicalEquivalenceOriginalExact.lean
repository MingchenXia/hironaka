/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.CodimOnePartCanonical

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CodimOnePartCanonical

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.HomogenizedGlueingTower Hironaka.MarkedIdealRestrictOpen
  Hironaka.CodimOneSupportAlong Hironaka.MarkedIdealBiholomorphism
  Hironaka.MarkedIdealTowerTransport Hironaka.BoundaryCount
  Hironaka.BlowupStrictSubmanifold Hironaka.GermIdealOrder
  Hironaka.MarkedIdealEquivalence

noncomputable section

variable {n : ℕ}

section Tower

variable {X X' : CMfd.{u} n} {𝔪 : MarkedIdeal n X}

/-- **Equivalent marked ideals with the same `N` have the same codimension-one part along every
multiple test blow-up** (property (7) for the replacement of `𝔪` by `𝓒(𝓗(𝔪))`). -/
theorem codimOnePartAlong_geoTransformAlong_of_wEquiv {𝔫 : MarkedIdeal n X}
    (h : MarkedIdealEquivalence.MarkedIdeal.WEquiv 𝔪 𝔫)
    (hN : 𝔪.N = 𝔫.N) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    codimOnePartAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).d =
      codimOnePartAlong (geoTransformAlong 𝔫 T).N (geoTransformAlong 𝔫 T).ideal
        (geoTransformAlong 𝔫 T).d :=
  codimOnePartAlong_congr (by rw [N_geoTransformAlong, N_geoTransformAlong, hN]) ((h.2 T).2 hT)

end Tower

end

end Hironaka.CodimOnePartCanonical
