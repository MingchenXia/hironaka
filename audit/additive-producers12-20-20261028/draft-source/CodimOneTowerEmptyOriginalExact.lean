/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.CodimOnePartTowerAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CodimOnePartTowerAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.HomogenizedGlueingTower Hironaka.MarkedIdealRestrictOpen
  Hironaka.CodimOneSupportAlong Hironaka.MarkedIdealBiholomorphism
  Hironaka.CodimOnePartCanonical Hironaka.GermIdealOrder
  Hironaka.HomogenizedIdealAlong Hironaka.TangentDirectionAlong
  Hironaka.MaximalContactAlongTower Hironaka.TransformOffCentre
  Hironaka.DivisorExponentAlong Hironaka.CoefficientIdealRestriction
  Hironaka.MarkedIdealEquivalence Hironaka.ContactEquivalenceAlong
  Hironaka.GiraudAlong Hironaka.BlowupStrictSubmanifold

noncomputable section

variable {n : ℕ}

/-! ### The codimension-one part along towers -/

section Tower

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)

/-- **If the codimension-one part along `N` is empty, it stays empty along every multiple test
blow-up** (`𝔪` well formed, of maximal order along `N`, `d ≥ 1`). -/
theorem codimOnePartAlong_geoTransformAlong_eq_empty (h𝔪 : 𝔪.IsWellFormed) (hμ : 1 ≤ 𝔪.d)
    (hmax : IsMaximalOrderAlong 𝔪.N 𝔪.ideal 𝔪.d) (hZ : codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d = ∅)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    codimOnePartAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal
      (geoTransformAlong 𝔪 T).d = ∅ := by
  have h := codimOnePartAlong_geoTransformAlong_subset 𝔪 h𝔪 hμ hmax T hT
  rw [hZ, preimage_empty] at h
  exact subset_empty_iff.mp h

end Tower

end

end Hironaka.CodimOnePartTowerAlong
