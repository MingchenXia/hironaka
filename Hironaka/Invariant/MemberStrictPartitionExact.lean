/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MemberInterTowerAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold
universe u
namespace Hironaka.MemberInterTowerAlong
open Hironaka Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MarkedIdeals.MarkedIdeal HomogenizedGlueingTower BlowupStrictSubmanifold
variable {n : ℕ} {X : CMfd.{u} n}

theorem disjoint_strictAlong {Y : CMfd.{u} n} (T : BlowupTower X Y) {A B : Set X} (hA : IsClosed A)
    (hB : IsClosed B) (hAB : Disjoint A B) : Disjoint (strictAlong T A) (strictAlong T B) :=
  Disjoint.mono (strictAlong_subset_preimage T hA) (strictAlong_subset_preimage T hB)
    (hAB.preimage T.proj)

theorem strictAlong_union : {Y : CMfd.{u} n} → (T : BlowupTower X Y) → (A B : Set X) →
    strictAlong T (A ∪ B) = strictAlong T A ∪ strictAlong T B
  | _, .refl, _, _ => rfl
  | _, .step T C π _, A, B => by
    rw [strictAlong_step, strictAlong_step, strictAlong_step, strictAlong_union T A B]
    unfold geoStrictTransform
    rw [union_sdiff_distrib, preimage_union, closure_union]

end Hironaka.MemberInterTowerAlong
