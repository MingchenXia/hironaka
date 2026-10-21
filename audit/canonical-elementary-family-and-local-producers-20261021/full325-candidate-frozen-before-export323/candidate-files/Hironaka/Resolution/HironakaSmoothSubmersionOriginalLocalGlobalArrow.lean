/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalLocalChartArrow
/-! Full original global-target Cartesian laws for the actual original local
smooth arrows. Complete mathematics preceded code. Actual saturation and the
proved local range inverse supply every true global-target cone internally;
source descent and overlap compatibility remain subsequent producers. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalLocalGlobalArrow
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms CanonicalCentres
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalTerminalLocalBiholomorphism HironakaSmoothSubmersionOriginalLocalChartArrow
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaSmoothSubmersionCartesianTower
open ResolutionInvariantSpec (IsInvDomain)
attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold
variable {n m : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
section Original
variable (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
  (M : MarkedIdeal n X) (hM : IsInvDomain n M)

/-- This is the actual original source chart base map into the original X. -/
def originalSmoothChartOriginalBaseMap (i : Y) (j : X) :
    actualSmoothChartNestedOpen hf
      ((actualLocalTerminalAtlas (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM)).openSet i)
      ((actualLocalTerminalAtlas M hM).openSet j) → X := fun y => f y.val.val

def originalLocalTerminalSmoothGlobalArrow (i : Y) (j : X) :
    originalLocalSmoothChartArrowSourceOpen hf M hM i j → originalTerminalManifold M hM :=
  (originalTerminalLocalInclusion M hM j) ∘ originalLocalTerminalSmoothChartArrow hf M hM i j

theorem originalLocalTerminalSmoothGlobalArrow_properties (i : Y) (j : X) :
    let A := actualLocalTerminalAtlas (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM)
    let B := actualLocalTerminalAtlas M hM
    let V := actualSmoothChartNestedOpen hf (A.openSet i) (B.openSet j)
    let G := originalLocalTerminalSmoothGlobalArrow hf M hM i j
    ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
      (∀ y, originalTerminalGluedProjection M hM (G y)=f (((A.tower i).proj y.val).val)) ∧
      HolomorphicSquarePullback (originalSmoothChartOriginalBaseMap hf M hM i j) G
        (restrict V (A.tower i)).proj (originalTerminalGluedProjection M hM) := by
  dsimp only
  let A := actualLocalTerminalAtlas (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM)
  let B := actualLocalTerminalAtlas M hM
  let V := actualSmoothChartNestedOpen hf (A.openSet i) (B.openSet j)
  let g := originalLocalTerminalSmoothChartArrow hf M hM i j
  have hlocal : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
      (∀ y, ((B.tower j).proj (g y)).val=f (((A.tower i).proj y.val).val)) ∧
      HolomorphicSquarePullback (actualSmoothChartBaseMap hf (A.openSet i) (B.openSet j)) g
        (restrict V (A.tower i)).proj (B.tower j).proj :=
    originalLocalTerminalSmoothChartArrow_properties hf M hM i j
  refine ⟨(originalTerminalLocalInclusion_contMDiff M hM j).comp hlocal.1.contMDiff,?_,?_⟩
  · intro y
    exact (originalTerminalGluedProjection_local M hM j (g y)).trans (hlocal.2.1 y)
  · intro k W a b ha hb hcone
    have hbrange : ∀ z, b z ∈ originalTerminalLocalRangeOpen M hM j := by
      intro z
      change b z ∈ range (originalTerminalLocalInclusion M hM j)
      rw [originalTerminalLocalInclusion_range]
      change originalTerminalGluedProjection M hM (b z) ∈ B.openSet j
      rw [← hcone z]
      exact (actualSmoothChartBaseMap hf (A.openSet i) (B.openSet j) (a z)).property
    let brange : W → originalTerminalLocalRangeOpen M hM j := fun z => ⟨b z,hbrange z⟩
    have hbrangeHol : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ brange :=
      BlowupRestrictOpen.contMDiff_opens_mk hb hbrange
    let blocal : W → B.finalSpace j := (originalTerminalLocalBiholomorphism M hM j).symm ∘ brange
    have hblocal : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ blocal :=
      (originalTerminalLocalBiholomorphism M hM j).symm.contMDiff.comp hbrangeHol
    have hinc : ∀ z, originalTerminalLocalInclusion M hM j (blocal z)=b z :=
      fun z => originalTerminalLocalHomeomorphism_inverse_point M hM j (brange z)
    have hbase : ∀ z, actualSmoothChartBaseMap hf (A.openSet i) (B.openSet j) (a z)=
        (B.tower j).proj (blocal z) := by
      intro z
      apply Subtype.ext
      have hp := originalTerminalGluedProjection_local M hM j (blocal z)
      rw [hinc z] at hp
      exact (hcone z).trans hp
    obtain ⟨w,hw,huniq⟩ := hlocal.2.2 k W a blocal ha hblocal hbase
    refine ⟨w,⟨hw.1,hw.2.1,?_,⟩,?_⟩
    · intro z
      change originalTerminalLocalInclusion M hM j (g (w z))=b z
      exact (congrArg (originalTerminalLocalInclusion M hM j) (hw.2.2 z)).trans (hinc z)
    · intro v hv
      apply huniq v
      refine ⟨hv.1,hv.2.1,?_⟩
      intro z
      apply (originalTerminalLocalInclusion_openEmbedding M hM j).injective
      exact (hv.2.2 z).trans (hinc z).symm

end Original
end
end Hironaka.HironakaSmoothSubmersionOriginalLocalGlobalArrow
