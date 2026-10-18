/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGlobalSuccessorCentreIdeal

/-! Genuine saturated ranges and actual range biholomorphisms identify the
whole restricted global successor as the blowup of the actual centre trace. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveSuccessorLocalBlowup
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveUniformStageAtlas HironakaSharpActualCurveUniformSuccessorComparison
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveLocalRangeBiholomorphism
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveGlobalSuccessorMap
  HironakaSharpActualCurveGlobalSuccessorCentre HironakaSharpActualCurveGlobalSuccessorGeometry
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

/-- The full original universal property survives a genuine source biholomorphism. -/
theorem isBlowupAlong_comp_diffeomorph {Y Y' : CMfd.{u} n}
    (e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) :
    IsBlowupAlong n C (π ∘ e) := by
  refine ⟨hπ.1,hπ.2.1,hπ.contMDiff.comp e.contMDiff,?_,?_⟩
  · rw [GermIdealTotalTransform.pullback_comp hπ.contMDiff e.contMDiff
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hπ.1)]
    apply GermIdealTotalTransform.isInvertible_pullback e.contMDiff _ hπ.2.2.2.1
    have he : exceptionalLocus n e=∅ :=
      eq_empty_iff_forall_notMem.mpr (MarkedIdealTowerTransport.notMem_exceptionalLocus e)
    rw [he,interior_empty]
  · intro m Z _ _ _ g hg hginv
    obtain ⟨h,⟨hh,hπh⟩,huniq⟩ := hπ.2.2.2.2 m Z g hg hginv
    refine ⟨e.symm ∘ h,⟨e.symm.contMDiff.comp hh,?_⟩,?_⟩
    · funext z
      change π (e (e.symm (h z)))=g z
      exact (congrArg π (e.apply_symm_apply (h z))).trans (congrFun hπh z)
    · rintro h' ⟨hh',hComp⟩
      have heq : e ∘ h'=h := huniq (e ∘ h') ⟨e.contMDiff.comp hh',hComp⟩
      funext z
      exact e.injective ((congrFun heq z).trans (e.apply_symm_apply (h z)).symm)

theorem globalUniformSuccessor_preimage_range (A : ActualEndpointHistories X J) (k : ℕ) (i : J) :
    (globalUniformSuccessor A k) ⁻¹' range (endpointLocalInclusion (uniformStageHistories A k) i)=
      range (endpointLocalInclusion (uniformStageHistories A (k+1)) i) := by
  ext z
  rw [Set.mem_preimage,localInclusion_range,localInclusion_range]
  change gluedProjection (uniformStageHistories A k) (globalUniformSuccessor A k z)∈A.openSet i ↔
    gluedProjection (uniformStageHistories A (k+1)) z∈A.openSet i
  rw [globalUniformSuccessor_projection]

def localRangeUniformSuccessor (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (i : J) :
    localRangeOpen (uniformStageHistories A (k+1)) hc i → localRangeOpen (uniformStageHistories A k) hc i :=
  fun q => ⟨globalUniformSuccessor A k q.val,
    (Set.ext_iff.mp (globalUniformSuccessor_preimage_range A k i) q.val).mpr q.property⟩

theorem localRangeUniformSuccessor_formula (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (i : J)
    (q : localRangeOpen (uniformStageHistories A (k+1)) hc i) :
    localRangeUniformSuccessor A hc k i q=
      localBiholomorphism (uniformStageHistories A k) hc i
        (localUniformSuccessor A k i ((localBiholomorphism (uniformStageHistories A (k+1)) hc i).symm q)) := by
  apply Subtype.ext
  change globalUniformSuccessor A k q.val=endpointLocalInclusion (uniformStageHistories A k) i
    (localUniformSuccessor A k i ((localBiholomorphism (uniformStageHistories A (k+1)) hc i).symm q))
  exact (congrArg (globalUniformSuccessor A k)
    (localHomeomorphism_inverse_point (uniformStageHistories A (k+1)) hc i q)).symm.trans
    (globalUniformSuccessor_local A k i _)

theorem isBlowupAlong_localRangeUniformSuccessor (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (i : J) :
    IsBlowupAlong n
      ((Subtype.val : localRangeOpen (uniformStageHistories A k) hc i →
        endpointManifold (uniformStageHistories A k) hc) ⁻¹' globalUniformCentre A k)
      (localRangeUniformSuccessor A hc k i) := by
  let e₀ := localBiholomorphism (uniformStageHistories A k) hc i
  let e₁ := localBiholomorphism (uniformStageHistories A (k+1)) hc i
  let D := actualUniformSuccessor ((A.prefixTower i).append (A.tail i)) k
  have hBase := MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse
    e₀.symm.contMDiff e₀.contMDiff e₀.symm_apply_apply e₀.apply_symm_apply D.blowup
  have hFull := isBlowupAlong_comp_diffeomorph e₁.symm hBase
  have hTrace : e₀.symm ⁻¹' D.centre=
      (Subtype.val : localRangeOpen (uniformStageHistories A k) hc i →
        endpointManifold (uniformStageHistories A k) hc) ⁻¹' globalUniformCentre A k := by
    ext q
    have hMem := mem_globalUniformCentre_iff A k i (e₀.symm q)
    have hPoint := localHomeomorphism_inverse_point (uniformStageHistories A k) hc i q
    exact hMem.symm.trans (Iff.of_eq (congrArg (fun z => z∈globalUniformCentre A k) hPoint))
  have hMap : localRangeUniformSuccessor A hc k i=(e₀ ∘ D.map) ∘ e₁.symm :=
    funext (localRangeUniformSuccessor_formula A hc k i)
  have hCentre := congrArg (fun C => IsBlowupAlong n C ((e₀ ∘ D.map) ∘ e₁.symm)) hTrace
  exact Eq.mpr (congrArg (IsBlowupAlong n
    ((Subtype.val : localRangeOpen (uniformStageHistories A k) hc i →
      endpointManifold (uniformStageHistories A k) hc) ⁻¹' globalUniformCentre A k)) hMap)
    (Eq.mp hCentre hFull)

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

theorem isBlowupAlong_originalLocalRangeUniformSuccessor (k : ℕ) (i : X) :
    IsBlowupAlong n
      ((Subtype.val : localRangeOpen (uniformStageHistories (originalEndpointHistories hn hW hE hdense hr) k)
        (originalEndpointHistories_cover hn hW hE hdense hr) i →
          originalUniformStageManifold hn hW hE hdense hr k) ⁻¹' originalUniformCentre hn hW hE hdense hr k)
      (localRangeUniformSuccessor (originalEndpointHistories hn hW hE hdense hr)
        (originalEndpointHistories_cover hn hW hE hdense hr) k i) :=
  isBlowupAlong_localRangeUniformSuccessor (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) k i

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveSuccessorLocalBlowup
