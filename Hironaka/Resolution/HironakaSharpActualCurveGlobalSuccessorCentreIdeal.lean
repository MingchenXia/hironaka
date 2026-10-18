/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGlobalSuccessorCentre
import Hironaka.Support.OriginalInvertibleOpenCoverExact

/-! Entire actual centre-ideal pullback identities precede genuine global
invertibility; no principalization or blowup certificate is an input. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveGlobalSuccessorCentreIdeal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveUniformStageAtlas HironakaSharpActualCurveUniformSuccessorComparison
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGlobalManifold
  HironakaSharpActualCurveLocalRangeBiholomorphism HironakaSharpActualCurveOriginalRecipeAtlas
  HironakaSharpActualCurveGlobalSuccessorMap HironakaSharpActualCurveGlobalSuccessorGeometry
  HironakaSharpActualCurveGlobalSuccessorCentre GermIdealPullbackCalculus
  VanishingIdealCoherent BlowupRestrictOpen
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

theorem localInclusion_pullback_vanishingCentre (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (i : J) :
    GermIdeal.pullback (m := n)
      (endpointLocalInclusion (uniformStageHistories A k) i : (uniformStageHistories A k).finalSpace i →
        endpointManifold (uniformStageHistories A k) hc)
      (vanishingIdeal (n := n) (globalUniformCentre A k))=
      vanishingIdeal (n := n) (localUniformCentre A k i) := by
  let e := localBiholomorphism (uniformStageHistories A k) hc i
  let C : Set (endpointManifold (uniformStageHistories A k) hc) := globalUniformCentre A k
  let U := localRangeOpen (uniformStageHistories A k) hc i
  have hCentre : e ⁻¹' ((Subtype.val : U → endpointManifold (uniformStageHistories A k) hc) ⁻¹' C)=
      localUniformCentre A k i := by
    ext z
    exact mem_globalUniformCentre_iff A k i z
  have h := MarkedIdealBiholomorphism.pullback_vanishingIdeal_preimage
    e.contMDiff e.symm.contMDiff e.apply_symm_apply e.symm_apply_apply
    (g := id) contMDiff_id ((Subtype.val : U → endpointManifold (uniformStageHistories A k) hc) ⁻¹' C)
  rw [hCentre] at h
  have hId : GermIdeal.pullback (m := n) id (vanishingIdeal (n := n) (localUniformCentre A k i))=
      vanishingIdeal (n := n) (localUniformCentre A k i) :=
    BlowupControlledTransform.pullback_id
      (isCoherent_vanishingIdeal (actualUniformSuccessor ((A.prefixTower i).append (A.tail i)) k).blowup.1)
  have hOpen := pullback_vanishingIdeal_opens (n := n) (m := n) U e C
  exact hOpen.symm.trans (hId.symm.trans h).symm

theorem localSuccessor_pullback_globalCentre (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (i : J) :
    GermIdeal.pullback (m := n)
      (endpointLocalInclusion (uniformStageHistories A (k+1)) i : (uniformStageHistories A (k+1)).finalSpace i →
        endpointManifold (uniformStageHistories A (k+1)) hc)
      (GermIdeal.pullback (m := n)
        (globalUniformSuccessor A k : endpointManifold (uniformStageHistories A (k+1)) hc →
          endpointManifold (uniformStageHistories A k) hc)
        (vanishingIdeal (n := n) (globalUniformCentre A k)))=
      GermIdeal.pullback (m := n) (localUniformSuccessor A k i)
        (vanishingIdeal (n := n) (localUniformCentre A k i)) := by
  let I : GermIdeal n (endpointManifold (uniformStageHistories A k) hc) :=
    vanishingIdeal (n := n) (globalUniformCentre A k)
  have hI : I.IsCoherent := isCoherent_vanishingIdeal (isClosedSubmanifold_globalUniformCentre A hc k)
  have hMap : (globalUniformSuccessor A k : endpointManifold (uniformStageHistories A (k+1)) hc →
      endpointManifold (uniformStageHistories A k) hc) ∘ endpointLocalInclusion (uniformStageHistories A (k+1)) i=
      (endpointLocalInclusion (uniformStageHistories A k) i : (uniformStageHistories A k).finalSpace i →
        endpointManifold (uniformStageHistories A k) hc) ∘ localUniformSuccessor A k i :=
    funext (globalUniformSuccessor_local A k i)
  let f : endpointManifold (uniformStageHistories A (k+1)) hc →
      endpointManifold (uniformStageHistories A k) hc := globalUniformSuccessor A k
  let ι₁ : (uniformStageHistories A (k+1)).finalSpace i → endpointManifold (uniformStageHistories A (k+1)) hc :=
    endpointLocalInclusion (uniformStageHistories A (k+1)) i
  let ι₀ : (uniformStageHistories A k).finalSpace i → endpointManifold (uniformStageHistories A k) hc :=
    endpointLocalInclusion (uniformStageHistories A k) i
  have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f := globalUniformSuccessor_contMDiff A hc k
  have hι₁ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ι₁ :=
    localInclusion_contMDiff (uniformStageHistories A (k+1)) hc i
  have hι₀ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ι₀ :=
    localInclusion_contMDiff (uniformStageHistories A k) hc i
  exact ((GermIdealTotalTransform.pullback_comp hf hι₁ hI).symm.trans
    ((congrArg (fun f => GermIdeal.pullback (m := n) f I) hMap).trans
      (GermIdealTotalTransform.pullback_comp hι₀ (localUniformSuccessor_contMDiff A k i) hI))).trans
    (congrArg (GermIdeal.pullback (m := n) (localUniformSuccessor A k i))
      (localInclusion_pullback_vanishingCentre A hc k i))

theorem localRange_pullback_globalCentre (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (i : J) :
    GermIdeal.pullback (m := n)
      (Subtype.val : localRangeOpen (uniformStageHistories A (k+1)) hc i →
        endpointManifold (uniformStageHistories A (k+1)) hc)
      (GermIdeal.pullback (m := n)
        (globalUniformSuccessor A k : endpointManifold (uniformStageHistories A (k+1)) hc →
          endpointManifold (uniformStageHistories A k) hc)
        (vanishingIdeal (n := n) (globalUniformCentre A k)))=
      GermIdeal.pullback (m := n) (localBiholomorphism (uniformStageHistories A (k+1)) hc i).symm
        (GermIdeal.pullback (m := n) (localUniformSuccessor A k i)
          (vanishingIdeal (n := n) (localUniformCentre A k i))) := by
  let I : GermIdeal n (endpointManifold (uniformStageHistories A k) hc) :=
    vanishingIdeal (n := n) (globalUniformCentre A k)
  let f : endpointManifold (uniformStageHistories A (k+1)) hc →
      endpointManifold (uniformStageHistories A k) hc := globalUniformSuccessor A k
  have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f := globalUniformSuccessor_contMDiff A hc k
  let G : GermIdeal n (endpointManifold (uniformStageHistories A (k+1)) hc) := GermIdeal.pullback (m := n) f I
  have hG : G.IsCoherent := isCoherent_pullback hf
    (isCoherent_vanishingIdeal (isClosedSubmanifold_globalUniformCentre A hc k))
  have hMap : (endpointLocalInclusion (uniformStageHistories A (k+1)) i :
      (uniformStageHistories A (k+1)).finalSpace i → endpointManifold (uniformStageHistories A (k+1)) hc) ∘
      (localBiholomorphism (uniformStageHistories A (k+1)) hc i).symm=
      (Subtype.val : localRangeOpen (uniformStageHistories A (k+1)) hc i →
        endpointManifold (uniformStageHistories A (k+1)) hc) :=
    funext (localHomeomorphism_inverse_point (uniformStageHistories A (k+1)) hc i)
  let ι : (uniformStageHistories A (k+1)).finalSpace i → endpointManifold (uniformStageHistories A (k+1)) hc :=
    endpointLocalInclusion (uniformStageHistories A (k+1)) i
  have hι : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ι :=
    localInclusion_contMDiff (uniformStageHistories A (k+1)) hc i
  exact ((congrArg (fun f => GermIdeal.pullback (m := n) f G) hMap.symm).trans
    (GermIdealTotalTransform.pullback_comp hι
      (localBiholomorphism (uniformStageHistories A (k+1)) hc i).symm.contMDiff hG)).trans
    (congrArg (GermIdeal.pullback (m := n) (localBiholomorphism (uniformStageHistories A (k+1)) hc i).symm)
      (localSuccessor_pullback_globalCentre A hc k i))

private theorem actual_smooth_ideal_coherent (Y : CMfd.{u} n) (C : Set Y)
    (hC : IsClosedSubmanifold n C) : (vanishingIdeal (n := n) C).IsCoherent :=
  isCoherent_vanishingIdeal hC

theorem isInvertible_globalSuccessorCentrePullback (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) :
    (GermIdeal.pullback (m := n)
      (globalUniformSuccessor A k : endpointManifold (uniformStageHistories A (k+1)) hc →
        endpointManifold (uniformStageHistories A k) hc)
      (vanishingIdeal (n := n) (globalUniformCentre A k))).IsInvertible := by
  let f : endpointManifold (uniformStageHistories A (k+1)) hc →
      endpointManifold (uniformStageHistories A k) hc := globalUniformSuccessor A k
  have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f := globalUniformSuccessor_contMDiff A hc k
  have hI : (vanishingIdeal (n := n) (globalUniformCentre A k :
      Set (endpointManifold (uniformStageHistories A k) hc))).IsCoherent :=
    actual_smooth_ideal_coherent (endpointManifold (uniformStageHistories A k) hc)
      (globalUniformCentre A k) (isClosedSubmanifold_globalUniformCentre A hc k)
  apply HironakaOriginalGlobalPrincipalization.isInvertible_of_open_cover
    (Y := endpointManifold (uniformStageHistories A (k+1)) hc)
    (isCoherent_pullback hf hI)
    (localRangeOpen (uniformStageHistories A (k+1)) hc)
  · intro z
    obtain ⟨i,y,hy⟩ := endpointLocalInclusion_jointly_surjective (uniformStageHistories A (k+1)) z
    exact ⟨i,y,hy⟩
  · intro i
    have hInv : (GermIdeal.pullback (m := n)
        (localBiholomorphism (uniformStageHistories A (k+1)) hc i).symm
        (GermIdeal.pullback (m := n) (localUniformSuccessor A k i)
          (vanishingIdeal (n := n) (localUniformCentre A k i)))).IsInvertible := by
      apply GermIdealTotalTransform.isInvertible_pullback
        (localBiholomorphism (uniformStageHistories A (k+1)) hc i).symm.contMDiff
        _ (actualUniformSuccessor ((A.prefixTower i).append (A.tail i)) k).blowup.2.2.2.1
      have he : exceptionalLocus n (localBiholomorphism (uniformStageHistories A (k+1)) hc i).symm=∅ :=
        eq_empty_iff_forall_notMem.mpr (MarkedIdealTowerTransport.notMem_exceptionalLocus _)
      rw [he,interior_empty]
    exact Eq.mpr (congrArg GermIdeal.IsInvertible (localRange_pullback_globalCentre A hc k i)) hInv

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

theorem originalUniformSuccessor_centre_isInvertible (k : ℕ) :
    (GermIdeal.pullback (m := n) (originalUniformSuccessor hn hW hE hdense hr k)
      (vanishingIdeal (n := n) (originalUniformCentre hn hW hE hdense hr k))).IsInvertible :=
  isInvertible_globalSuccessorCentrePullback (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) k

def originalUniformCentreDivisor (k : ℕ) :
    EffectiveDivisor n (originalUniformStageManifold hn hW hE hdense hr (k+1)) where
  ideal := GermIdeal.pullback (m := n) (originalUniformSuccessor hn hW hE hdense hr k)
    (vanishingIdeal (n := n) (originalUniformCentre hn hW hE hdense hr k))
  isInvertible := originalUniformSuccessor_centre_isInvertible hn hW hE hdense hr k

theorem originalUniformCentreDivisor_support (k : ℕ) :
    (originalUniformCentreDivisor hn hW hE hdense hr k).support=
      (originalUniformSuccessor hn hW hE hdense hr k) ⁻¹' originalUniformCentre hn hW hE hdense hr k := by
  change (GermIdeal.pullback (m := n) (originalUniformSuccessor hn hW hE hdense hr k)
    (vanishingIdeal (n := n) (originalUniformCentre hn hW hE hdense hr k))).zeroLocus=_
  rw [BlowupExceptionalDivisor.zeroLocus_pullback (originalUniformSuccessor_contMDiff hn hW hE hdense hr k)
    (isCoherent_vanishingIdeal (isClosedSubmanifold_originalUniformCentre hn hW hE hdense hr k)),
    BlowupExceptionalDivisor.zeroLocus_vanishingIdeal
      (isClosedSubmanifold_originalUniformCentre hn hW hE hdense hr k).1]

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveGlobalSuccessorCentreIdeal
