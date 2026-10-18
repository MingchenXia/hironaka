/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGlobalPrefixTests
import Hironaka.Resolution.HironakaSharpActualCurveCompactGlobalFiniteEndpoint

/-! Ordinary compactness constructs a genuine finite original-family
admissible sharp history, coupled to the SAME complete original endpoint. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveCompactAdmissibleHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaSharpActualCurveGlobalPrefixTests HironakaSharpActualCurveCompactGlobalFiniteEndpoint
  HironakaSharpActualCurveCompactSubsetStopping HironakaSharpActualCurveStoppedOpenGluing
  HironakaSharpActualCurveGlobalPrefixTowers HironakaSharpActualCurveGlobalSuccessorCentre
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveUniformStageAtlas
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveGlobalSharpEndpointData
  HironakaSharpOriginalMemberProductDomain HironakaSharpActualCurveGlobalStrictClosure
  HironakaSharpActualCurveFullAmbientBoundary HironakaSharpActualFiniteChronologicalHistory
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Whole conventional strict transforms, including all exceptional points. -/
theorem strictTransform_biholomorphic_source
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (f : Y → X) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (S : Set X) : strictTransform n (f ∘ e) S=e ⁻¹' strictTransform n f S := by
  have he : exceptionalLocus n e=∅ := eq_empty_iff_forall_notMem.mpr fun z =>
    MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
      e.contMDiff e.symm.contMDiff e.apply_symm_apply e.symm_apply_apply z
  rw [StrictTransformComposition.strictTransform_comp hf e.contMDiff]
  change closure (e ⁻¹' strictTransform n f S \ exceptionalLocus n e)=e ⁻¹' strictTransform n f S
  rw [he,sdiff_empty]
  exact (isClosed_closure.preimage e.contMDiff.continuous).closure_eq

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- All history, sharp geometry and endpoint equivalence are OUTPUTS from
ONLY original geometry and ordinary ambient compactness. -/
theorem exists_original_compact_admissible_sharp_history [CompactSpace X] :
    ∃ (N : ℕ) (Y : CMfd.{u} n) (T : BlowupTower X Y) (G : GlobalSharpCurveEndpoint W E)
      (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G.ambient),
      T.length=N+1 ∧ IsGeoTestTower (originalMemberProductMarked W E 1) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E ∧
      (∀ z : Y,G.projection (e z)=T.proj z) ∧
      (geoTransformAlong (originalMemberProductMarked W E 1) T).N=strictTransform n T.proj W ∧
      strictTransform n T.proj W=e ⁻¹' strictTransform n G.projection W ∧
      T.proj '' strictTransform n T.proj W=W ∧
      ∀ k,N+1≤k → originalUniformCentre hn hW hE hdense hr k=∅ := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  obtain ⟨N,hN⟩ := exists_compact_stopped_open_bound A hc (univ : Set X) isCompact_univ
  have hAll : ∀ x : X,x∈stoppedBaseOpen A (N+1) := fun x => hN (mem_univ x)
  let Y := endpointManifold (uniformStageHistories A (N+1)) hc
  let T : BlowupTower X Y := uniformOriginalPositiveTower A hc N
  let G := originalGlobalSharpCurveEndpoint hn hW hE hdense hr
  let e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G.ambient :=
    wholePositivePrefixTerminalBiholomorphism A hc N hAll
  have hTest : IsGeoTestTower (originalMemberProductMarked W E 1) T :=
    originalUniformPositiveTower_test hn hW hE hdense hr N
  have hAmbient := original_curve_history_full_ambient_boundary hn hW hE hdense hr T hTest
  have hSquare (z : Y) : G.projection (e z)=T.proj z :=
    wholePositivePrefixTerminalBiholomorphism_projection A hc N hAll z
  have hDom : ResolutionInvariantSpec.IsInvDomain 1 (originalMemberProductMarked W E 1) :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hCarrier := carrier_eq_strictTransform _ hDom rfl T hTest
  have hStrict : strictTransform n T.proj W=e ⁻¹' strictTransform n G.projection W := by
    have hFun : G.projection ∘ e=T.proj := funext hSquare
    exact (congrArg (fun f => strictTransform n f W) hFun).symm.trans
      (strictTransform_biholomorphic_source e G.projection G.holomorphic W)
  have hImage : T.proj '' strictTransform n T.proj W=W := by
    apply Subset.antisymm
    · rintro x ⟨z,hz,rfl⟩
      have hzG : e z∈strictTransform n G.projection W := by
        rw [hStrict] at hz
        exact hz
      have hp : G.projection (e z)∈W := Eq.mp
        (congrArg (fun S : Set X => G.projection (e z)∈S) G.strict_image) ⟨e z,hzG,rfl⟩
      exact (hSquare z) ▸ hp
    · intro x hx
      have hxG : x∈G.projection '' strictTransform n G.projection W :=
        Eq.mpr (congrArg (fun S : Set X => x∈S) G.strict_image) hx
      obtain ⟨z,hz,hzx⟩ := hxG
      refine ⟨e.symm z,?_,?_⟩
      · rw [hStrict]
        change e (e.symm z)∈strictTransform n G.projection W
        exact (e.apply_symm_apply z).symm ▸ hz
      · exact (hSquare (e.symm z)).symm.trans
          ((congrArg G.projection (e.apply_symm_apply z)).trans hzx)
  refine ⟨N,Y,T,G,e,uniformOriginalPositiveTower_length A hc N,hTest,
    hAmbient.2.1,hAmbient.2.2,hSquare,hCarrier,hStrict,hImage,?_⟩
  intro k hk
  have hh := globalCentres_avoid_subset_of_stopped_open A (univ : Set X) (N+1) hN k hk
  apply Subset.antisymm ?_ (empty_subset _)
  intro z hz
  exact disjoint_left.mp hh hz (mem_univ _)

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveCompactAdmissibleHistory
