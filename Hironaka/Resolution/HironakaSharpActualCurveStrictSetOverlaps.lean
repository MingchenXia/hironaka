/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveLocalRangeBiholomorphism

/-! Actual OLD chosen transitions preserve original closed-set strict
transforms, before global strict-carrier or divisor descent is asserted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveStrictSetOverlaps
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerSplitIso BlowupTowerIsoTail MaxLocusLocal
  HironakaSharpActualCurveOverlapMaps HironakaSharpActualCurveCommonOpenCocycle
  HironakaSharpActualCurveChosenOverlapCocycle HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveEndpointGeometry HironakaSharpActualCurveOriginalRecipeAtlas
  HironakaSharpActualCurveEmptyPadding HomogenizedGlueingTower ContactEmptyPrefix
  MemberInterTowerAlong MemberInterLocusAlong
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

/-- Closed sets, not arbitrary nonclosed sets, are unchanged by the REAL
identity empty tail; all its actual positions remain present. -/
theorem strictAlong_identityEmptyTail {Y : CMfd.{u} n} {B : Set Y} (hB : IsClosed B) (r : ℕ) :
    strictAlong (identityEmptyTail Y r) B=B := by
  rw [strictAlong_of_isEmptyTower hB _ (identityEmptyTail_isEmptyTower Y r),identityEmptyTail_proj]
  rfl

/-- The actual padded restricted strict set is the trace of the SAME full
unpadded local prefix/tail strict set, with genuine closed-set normalization. -/
theorem localPaddedHistory_strictSet (U O : Opens X) {Y Z : CMfd.{u} n}
    (P : BlowupTower (CMfd.of (n := n) U) Y) (S : BlowupTower Y Z)
    (B : Set X) (hB : IsClosed B) (L : ℕ) :
    strictAlong (localPaddedHistory U O P S L)
      ((Subtype.val : nestedOpens U O → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' B)) =
      (Subtype.val : localEndpoint U O P S → Z) ⁻¹'
        strictAlong (P.append S) ((Subtype.val : U → X) ⁻¹' B) := by
  have hU : IsClosed ((Subtype.val : U → X) ⁻¹' B) := hB.preimage continuous_subtype_val
  have h0 : IsClosed ((Subtype.val : nestedOpens U O → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' B)) :=
    hU.preimage continuous_subtype_val
  dsimp only [localPaddedHistory,paddedHistory]
  rw [strictAlong_append,strictAlong_append,
    strictAlong_identityEmptyTail (isClosed_strictAlong _ (isClosed_strictAlong _ h0))]
  rw [strictAlong_restrict (nestedOpens U O) P,
    strictAlong_restrict (openPreimage P (nestedOpens U O)) S,strictAlong_append P _ S]

def localStrictSet (A : ActualEndpointHistories X J) (B : Set X) (i : J) : Set (A.finalSpace i) :=
  strictAlong ((A.prefixTower i).append (A.tail i)) ((Subtype.val : A.openSet i → X) ⁻¹' B)

/-- The OLD chosen stagewise comparison supplies strict-set compatibility
for every original closed B; no separate carrier/divisor dictionary is assumed. -/
theorem comparison_strictSet (A : ActualEndpointHistories X J) (B : Set X) (hB : IsClosed B)
    (i j : J) (z : localEndpoint (A.openSet i) (A.openSet i⊓A.openSet j) (A.prefixTower i) (A.tail i)) :
    (A.comparison i j z).val∈localStrictSet A B j ↔ z.val∈localStrictSet A B i := by
  have hInitial : (commonOpenBase (A.openSet i) (A.openSet j) (A.openSet i⊓A.openSet j)
      inf_le_left inf_le_right) ⁻¹'
      ((Subtype.val : nestedOpens (A.openSet j) (A.openSet i⊓A.openSet j) → A.openSet j) ⁻¹'
        ((Subtype.val : A.openSet j → X) ⁻¹' B)) =
      (Subtype.val : nestedOpens (A.openSet i) (A.openSet i⊓A.openSet j) → A.openSet i) ⁻¹'
        ((Subtype.val : A.openSet i → X) ⁻¹' B) := rfl
  have h := (A.stagewise i j).strictAlong_eq
    ((Subtype.val : nestedOpens (A.openSet j) (A.openSet i⊓A.openSet j) → A.openSet j) ⁻¹'
      ((Subtype.val : A.openSet j → X) ⁻¹' B))
  rw [hInitial,localPaddedHistory_strictSet (A.openSet i) (A.openSet i⊓A.openSet j)
    (A.prefixTower i) (A.tail i) B hB (A.cut i j),
    localPaddedHistory_strictSet (A.openSet j) (A.openSet i⊓A.openSet j)
      (A.prefixTower j) (A.tail j) B hB (A.cut i j)] at h
  exact (Set.ext_iff.mp h z).symm

theorem transition_strictSet (A : ActualEndpointHistories X J) (B : Set X) (hB : IsClosed B)
    (i j : J) (z : overlapOpen A i j) :
    (transition A i j z).val∈localStrictSet A B j ↔ z.val∈localStrictSet A B i :=
  comparison_strictSet A B hB i j (opensCongr (endpointOverlapOpen_eq_pair
    (A.openSet i) (A.openSet j) (A.prefixTower i) (A.tail i)) z)

theorem original_transition_strictSet (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : NormalCrossings.IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) (B : Set X) (hB : IsClosed B) (i j : X)
    (z : overlapOpen (originalEndpointHistories hn hW hE hdense hr) i j) :
    (transition (originalEndpointHistories hn hW hE hdense hr) i j z).val∈
        localStrictSet (originalEndpointHistories hn hW hE hdense hr) B j ↔
      z.val∈localStrictSet (originalEndpointHistories hn hW hE hdense hr) B i :=
  transition_strictSet _ B hB i j z

end
end Hironaka.HironakaSharpActualCurveStrictSetOverlaps
