/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalZeroOwnCurveValues
/-! Exact unchanged sequence-aware original Step One values on ANY original
TEST in the zero nonspecial regime, under actual equal-dimension smooth maps. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalZeroStepOneEtaleValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms CanonicalCentres
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneLowerDomain
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionPositiveMemberHistory HironakaSmoothSubmersionAllBranchHistory
  HironakaOriginalZeroOwnCurveValues
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y D : CMfd.{u} n}

/-- ONLY original data supply the SAME actual source history and OWN lower
geometry before exact unchanged ORIGINAL Step One values at EVERY positive depth. -/
theorem exists_original_any_test_zero_step_one_etale_values {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    ∃ (D' : CMfd.{u} n) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧ IsGeoTestTower (markedPullback (m := n) f M) Q ∧
      ∀ z : D',g z ∈ (geoTransformAlong M T).cosupp → ¬IsSpecial M T (g z) → level M T (g z)=0 →
        ∀ k : ℕ,Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) (markedPullback (m := n) f M) Q z=
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z) := by
  obtain ⟨D',Q,g,h,hQ,hValues⟩ := exists_original_zero_own_curve_values hf hn M hM hmax T hT
  refine ⟨D',Q,g,h,hQ,fun z hy hns hl k => ?_⟩
  obtain ⟨hp,hpOwn,_hJ,_hJT,_hOwn,_hOwnT,_hOwnPoint,hFull⟩ := hValues z hy hns hl
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 T).1.mpr hT
  have hLevel : level (markedPullback (m := n) f M) Q z=0 :=
    (IsActualTowerPullback.bar_level_dictionary h M hM.isWellFormed hBar z).trans hl
  have hNS : ¬IsSpecial (markedPullback (m := n) f M) Q z := fun hs =>
    hns ((IsActualTowerPullback.all_isSpecial_dictionary h M hM.isWellFormed hBar z).mp hs)
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_neg hNS,if_neg hns,hLevel,hl]
  congr 1
  rw [Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hpOwn,
    Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp]
  exact congrArg (fun a : ValTy (k+1) => ((0 : ℕ),(a : WithTop (ValTy (k+1))))) (hFull k)

end
end Hironaka.HironakaOriginalZeroStepOneEtaleValues
