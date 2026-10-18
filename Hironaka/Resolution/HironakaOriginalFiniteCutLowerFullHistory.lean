/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteCutPreparedLower
import Hironaka.Resolution.HironakaOriginalFiniteFullCutSmoothHistory
/-! The ENTIRE original lower full-cut history is internally constructed
by real upper history induction, without a lower recipe or canonicality field. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFiniteCutLowerFullHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism HomogenizedIdealAlong CanonicalCentres StepOneLowerDomain StepOneValue StepOneValueMasked StepOneRegime StepOneCanonicalTail
  HironakaOriginalFrozenRecursiveLower HironakaOriginalFiniteLevelCutLowerTests
  HironakaOriginalFiniteStepOneCutMaskAvoidance HironakaOriginalFiniteCutPreparedLower
  HironakaOriginalFiniteFullCutSmoothHistory
open ResolutionInvariantSpec (IsInvDomain)
open ResolutionDriver (maxLocus)
variable {n : ℕ} {X : CMfd.{u} n}

/-- Every genuine lower trace constructor is proved from actual next
admissibility and the ENTIRE original FULL cut, not assumed as lower data. -/
theorem finite_cut_lower_full_history_at_level (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsStepOneCutTower hn (d+2) M T) :
    ∀ z∈(geoTransformAlong M T).cosupp,∀ s : ℕ,
      let r := regimeRun (stepRegime M s) T z
      let H := head T r
      let S := tail T r
      let W := lowerMask M s H (S.proj z)
      IsFullCutTower hn d (lowerMarkedM M s H (S.proj z)) (restrict W S) := by
  induction T with
  | refl => intro z hz s;trivial
  | step T C π hπ ih =>
    intro z hz s
    have hUpper := levelCutTower_geoTest M T (stepOneCutTower_levelCut hn M T hT.1)
    have hWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM.isWellFormed T hUpper
    have hOldPoint : π z∈(geoTransformAlong M T).cosupp :=
      proj_mem_cosupp_of_mem_cosupp hWF.isClosedSubmanifold_N hWF.isCoherent
        (.step .refl C π hπ) ⟨trivial,hT.2.1⟩ hz
    by_cases hOld : stepRegime M s T (π z)
    · have hIH := ih hT.1 (π z) hOldPoint s
      let F : ℕ → Prop := fun ℓ =>
        let r := regimeRun (stepRegime M ℓ) T (π z)
        let H := head T r
        let S := tail T r
        let W := lowerMask M ℓ H (S.proj (π z))
        let K := lowerMarkedM M ℓ H (S.proj (π z))
        IsGeoTestTower K (restrict W (.step S C π hπ)) ∧
          (fun q : openPreimage S W => q.val) ⁻¹' C⊆
            maxLocus ((invFamily hn (d+2)).inv K (restrict W S))
              (geoTransformAlong K (restrict W S)).cosupp
      have hPrep := finite_cut_prepared_lower_data hn (d+1) M hM hmax T hT.1
        (π z) hOldPoint hOld.2 C hT.2.1 π hπ hT.2.2
      have hF : F (level M T (π z)) := ⟨hPrep.2.2.1,hPrep.2.2.2.2.2⟩
      have hFixed : F s := (congrArg F hOld.1).mp hF
      rw [regimeRun_step_of (stepRegime M s) T C π hπ hOld]
      refine ⟨hIH,hFixed.1.2,?_⟩
      intro p hp c hc
      exact (hFixed.2 hc).2 p hp
    · rw [regimeRun_step_of_not (stepRegime M s) T C π hπ hOld]
      trivial

/-- Actual current domain, TEST, point and entire cosupport are combined
with an independently constructed original lower FULL-cut history. -/
theorem finite_cut_current_lower_full_history_data (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsStepOneCutTower hn (d+2) M T)
    (z : Y) (hz : z∈(geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T z) :
    IsInvDomain 1 (lowerAt M T z) ∧ IsGeoTestTower (lowerAt M T z) (lowerTailAt M T z) ∧
      IsFullCutTower hn d (lowerAt M T z) (lowerTailAt M T z) ∧
      IsInvDomain 1 (geoTransformAlong (lowerAt M T z) (lowerTailAt M T z)) ∧
      ∃ hp : z∈patchAt M T z,
        (⟨z,hp⟩ : patchAt M T z)∈(geoTransformAlong (lowerAt M T z) (lowerTailAt M T z)).cosupp ∧
        ∀ p : patchAt M T z,p∈(geoTransformAlong (lowerAt M T z) (lowerTailAt M T z)).cosupp ↔
          p.val∈(geoTransformAlong M T).cosupp ∧ level M T p.val=level M T z := by
  obtain ⟨hD,hTest,hCurrent,hp,hPoint,hDict⟩ := levelCutTower_current_lower_data hn M hM hmax T
    (stepOneCutTower_levelCut hn M T hT) z hz hns
  have hFull := finite_cut_lower_full_history_at_level hn d M hM hmax T hT z hz (level M T z)
  exact ⟨hD,hTest,hFull,hCurrent,hp,hPoint,hDict⟩

end
end Hironaka.HironakaOriginalFiniteCutLowerFullHistory
