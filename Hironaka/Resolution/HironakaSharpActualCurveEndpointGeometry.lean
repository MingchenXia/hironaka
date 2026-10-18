/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveChosenOverlapCocycle

/-! Actual endpoint projections, overlap domains and diagonal geometry
precede the global topological and complex-manifold descent construction. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveEndpointGeometry
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerSplitIso BlowupTowerIsoTail MaxLocusLocal
  HironakaSharpActualCurveOverlapMaps HironakaSharpActualCurveCommonOpenCocycle
  HironakaSharpActualCurveChosenOverlapCocycle HironakaSharpActualCurveEmptyPadding
  HironakaSharpActualCurveFiniteRecipeComparison
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- The actual endpoint projection to the ORIGINAL ambient manifold. -/
def endpointProjection (U : Opens X) {Y Z : CMfd.{u} n}
    (P : BlowupTower (CMfd.of (n := n) U) Y) (S : BlowupTower Y Z) : Z → X :=
  fun z => (P.proj (S.proj z) : X)

theorem endpointProjection_contMDiff (U : Opens X) {Y Z : CMfd.{u} n}
    (P : BlowupTower (CMfd.of (n := n) U) Y) (S : BlowupTower Y Z) :
    ContMDiff (𝓘(ℂ,ComplexModel n)) (𝓘(ℂ,ComplexModel n)) ∞ (endpointProjection U P S) :=
  contMDiff_subtype_val.comp (P.contMDiff_proj.comp S.contMDiff_proj)

/-- The true overlap is defined by the actual projection, before any comparison. -/
def endpointOverlapOpen (U V : Opens X) {Y Z : CMfd.{u} n}
    (P : BlowupTower (CMfd.of (n := n) U) Y) (S : BlowupTower Y Z) : Opens Z :=
  ⟨endpointProjection U P S ⁻¹' (V : Set X),
    V.isOpen.preimage (endpointProjection_contMDiff U P S).continuous⟩

theorem endpointOverlapOpen_eq_pair (U V : Opens X) {Y Z : CMfd.{u} n}
    (P : BlowupTower (CMfd.of (n := n) U) Y) (S : BlowupTower Y Z) :
    endpointOverlapOpen U V P S = openPreimage S (openPreimage P (nestedOpens U (U⊓V))) := by
  apply Opens.ext
  ext z
  change (P.proj (S.proj z) : X) ∈ V ↔ (P.proj (S.proj z) : X) ∈ U⊓V
  exact ⟨fun h => ⟨(P.proj (S.proj z)).property,h⟩,fun h => h.2⟩

/-- Real empty padding and both real restrictions leave the underlying projection intact. -/
theorem localPaddedHistory_projection (U O : Opens X) {Y Z : CMfd.{u} n}
    (P : BlowupTower (CMfd.of (n := n) U) Y) (S : BlowupTower Y Z) (L : ℕ)
    (z : localEndpoint U O P S) :
    (((localPaddedHistory U O P S L).proj z : CMfd.of (n := n) U) : X) =
      endpointProjection U P S z.val := by
  simp only [localPaddedHistory,paddedHistory,BlowupTower.proj_append,
    identityEmptyTail_proj,Function.comp_apply,id_eq]
  rw [proj_restrict (nestedOpens U O) P,proj_restrict (openPreimage P (nestedOpens U O)) S]
  rfl

theorem endpointOverlapOpen_eq_reversed_pair (U V : Opens X) {Y Z : CMfd.{u} n}
    (P : BlowupTower (CMfd.of (n := n) V) Y) (S : BlowupTower Y Z) :
    openPreimage S (openPreimage P (nestedOpens V (U⊓V))) = endpointOverlapOpen V U P S := by
  rw [inf_comm]
  exact (endpointOverlapOpen_eq_pair V U P S).symm

/-- Actual equal-open biholomorphisms transport the OLD chosen map to the TRUE overlap opens. -/
def endpointTransition (U V : Opens X) {Y1 Y2 Z1 Z2 : CMfd.{u} n}
    (P1 : BlowupTower (CMfd.of (n := n) U) Y1) (P2 : BlowupTower (CMfd.of (n := n) V) Y2)
    (S1 : BlowupTower Y1 Z1) (S2 : BlowupTower Y2 Z2)
    (χ : localEndpoint U (U⊓V) P1 S1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      localEndpoint V (U⊓V) P2 S2) :
    CMfd.of (n := n) (endpointOverlapOpen U V P1 S1)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (endpointOverlapOpen V U P2 S2) :=
  ((opensCongr (endpointOverlapOpen_eq_pair U V P1 S1)).trans χ).trans
    (opensCongr (endpointOverlapOpen_eq_reversed_pair U V P2 S2))

theorem endpointTransition_projection (U V : Opens X) {Y1 Y2 Z1 Z2 : CMfd.{u} n}
    (P1 : BlowupTower (CMfd.of (n := n) U) Y1) (P2 : BlowupTower (CMfd.of (n := n) V) Y2)
    (S1 : BlowupTower Y1 Z1) (S2 : BlowupTower Y2 Z2) (L : ℕ)
    (χ : localEndpoint U (U⊓V) P1 S1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      localEndpoint V (U⊓V) P2 S2)
    (h : IsTowerIso (commonOpenBase U V (U⊓V) inf_le_left inf_le_right)
      (localPaddedHistory U (U⊓V) P1 S1 L) (localPaddedHistory V (U⊓V) P2 S2 L) χ)
    (z : endpointOverlapOpen U V P1 S1) :
    endpointProjection V P2 S2 (endpointTransition U V P1 P2 S1 S2 χ z).val =
      endpointProjection U P1 S1 z.val := by
  let q : localEndpoint U (U⊓V) P1 S1 := opensCongr (endpointOverlapOpen_eq_pair U V P1 S1) z
  have hproj := congrArg (fun p : nestedOpens V (U⊓V) => ((p : V) : X)) (h.proj_comm q)
  rw [localPaddedHistory_projection] at hproj
  change (((localPaddedHistory U (U⊓V) P1 S1 L).proj q : U) : X) =
    endpointProjection V P2 S2 (χ q).val at hproj
  rw [localPaddedHistory_projection] at hproj
  exact hproj.symm

theorem endpointOverlapOpen_self (U : Opens X) {Y Z : CMfd.{u} n}
    (P : BlowupTower (CMfd.of (n := n) U) Y) (S : BlowupTower Y Z) :
    endpointOverlapOpen U U P S = ⊤ := by
  apply Opens.ext
  ext z
  change (P.proj (S.proj z) : X) ∈ U ↔ True
  exact ⟨fun _ => trivial,fun _ => (P.proj (S.proj z)).property⟩

theorem commonOpenBase_self (U O : Opens X) (hOU : O≤U) :
    commonOpenBase U U O hOU hOU =
      Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (nestedOpens U O)) ∞ := by
  apply Diffeomorph.ext
  intro z
  rfl

/-- Diagonal identity uses genuine stagewise comparison uniqueness of the SAME finite history. -/
theorem endpointTransition_self (U : Opens X) {Y Z : CMfd.{u} n}
    (P : BlowupTower (CMfd.of (n := n) U) Y) (S : BlowupTower Y Z) (L : ℕ)
    (χ : localEndpoint U (U⊓U) P S ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      localEndpoint U (U⊓U) P S)
    (h : IsTowerIso (commonOpenBase U U (U⊓U) inf_le_left inf_le_right)
      (localPaddedHistory U (U⊓U) P S L) (localPaddedHistory U (U⊓U) P S L) χ) :
    endpointTransition U U P P S S χ =
      Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (endpointOverlapOpen U U P S)) ∞ := by
  rw [commonOpenBase_self] at h
  have hχ := actual_tower_comparison_unique h (IsTowerIso.refl_self (localPaddedHistory U (U⊓U) P S L))
  rw [hχ]
  apply Diffeomorph.ext
  intro z
  apply Subtype.ext
  rfl

end
end Hironaka.HironakaSharpActualCurveEndpointGeometry
