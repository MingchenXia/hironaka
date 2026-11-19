/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalStepOnePreparedLowerFullValues
import Hironaka.Resolution.HironakaOriginalPreparedCurrentLower
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalRecursiveFamily
/-! Actual computed current lower FULL values split the genuine run into
increment and reset, rather than identifying it with an old frozen reference. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedCurrentLowerFullValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres HomogenizedIdealAlong StepOneValue StepOneValueMasked StepOneRegime InvDomainTowerAlong StepOneLowerDomain
  HironakaOriginalFrozenRecursiveLower HironakaOriginalPreparedCurrentLower
  HironakaOriginalStepOnePreparedLowerFullValues HironakaSmoothSubmersionOriginalRecursiveFamily
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCanonicalValueDimensionShift
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m : ℕ} {X Y Z : CMfd.{u} n} {A B : CMfd.{u} m}

private theorem domain_two_at_depth (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (d : ℕ) :
    IsInvDomain (d+2) M := by
  refine ⟨hM.isWellFormed,?_,hM.one_le_d,hM.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨j,hj,hreg⟩ := hM.dimLE x hx
  exact ⟨j,by omega,hreg⟩

private theorem reflexive_lower_full_values (hn : 0<n) (hm : 0<m)
    (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J)
    {f : A → X} {g : B → X} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q .refl g) (z : B) (hz : g z ∈ J.cosupp) (d : ℕ) :
    (invFamily hm ((m-n)+d+2)).inv (markedPullback (m := m) f J) Q z=
      familyDimensionMap (m-n) (d+2) ((invFamily hn (d+2)).inv J .refl (g z)) := by
  have hcan : IsCanonical J ((invFamily hn (d+2)).inv J) .refl := trivial
  exact (IsActualTowerPullback.original_recursive_family hn hm h J
    (domain_two_at_depth J hJ d) hcan).2 z hz

/-- BOTH real run branches internally supply numerical naturality of the
exact CURRENT lower, after its genuine DOMAIN and TEST are constructed. -/
theorem current_lower_full_smooth_values_after_stepone_cut
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T c)
    (y : Z) (hy : y ∈ (geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) y) :
    let P := .step T C π hπ
    let J := lowerAt M P y
    let R := lowerTailAt M P y
    IsInvDomain 2 J ∧ IsGeoTestTower J R ∧
      ∀ {f : A → maskAt M P y} {g : B → patchAt M P y} {Q : BlowupTower A B},
        IsActualTowerPullback f Q R g → ∀ z : B,
          g z ∈ (geoTransformAlong J R).cosupp → ∀ d : ℕ,
            (invFamily hm ((m-n)+d+2)).inv (markedPullback (m := m) f J) Q z=
              familyDimensionMap (m-n) (d+2) ((invFamily hn (d+2)).inv J R (g z)) := by
  let P : BlowupTower X Z := .step T C π hπ
  have hData := current_lower_data_after_cut (k := 2) hn M hM hmax T hcan C hC π hπ hCuts y hy hns
  refine ⟨hData.1,hData.2.1,?_⟩
  let F : ℕ → ℕ → Prop := fun ℓ r =>
    let H := head P r
    let S := tail P r
    let W := lowerMask M ℓ H (S.proj y)
    let J := lowerMarkedM M ℓ H (S.proj y)
    let R := restrict W S
    IsInvDomain 2 J →
      ∀ {f : A → W} {g : B → openPreimage S W} {Q : BlowupTower A B},
        IsActualTowerPullback f Q R g → ∀ z : B,
          g z ∈ (geoTransformAlong J R).cosupp → ∀ d : ℕ,
            (invFamily hm ((m-n)+d+2)).inv (markedPullback (m := m) f J) Q z=
              familyDimensionMap (m-n) (d+2) ((invFamily hn (d+2)).inv J R (g z))
  have hValues : F (level M P y) (runAt M P y) := by
    let ℓ := level M P y
    change F ℓ (regimeRun (stepRegime M ℓ) (.step T C π hπ) y)
    by_cases hOld : stepRegime M ℓ T (π y)
    · rw [regimeRun_step_of (stepRegime M ℓ) T C π hπ hOld]
      have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
        (k := 3) (invFamily hn 2) M hM hmax hn T hcan
      have hWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM.isWellFormed T hb.2.1
      have hOldPoint : π y ∈ (geoTransformAlong M T).cosupp :=
        proj_mem_cosupp_of_mem_cosupp hWF.isClosedSubmanifold_N hWF.isCoherent
          (.step .refl C π hπ) ⟨trivial,hC⟩ hy
      let G : ℕ → Prop := fun a => F a (regimeRun (stepRegime M a) T (π y)+1)
      have hOldValue : G (level M T (π y)) := by
        intro _hJ f g Q h z hz d
        exact original_stepone_bound_three_prepared_lower_smooth_values hn hm M hM hmax T hcan
          (π y) hOldPoint hOld.2 C hC π hπ hCuts h z hz d
      exact (congrArg G hOld.1).mp hOldValue
    · rw [regimeRun_step_of_not (stepRegime M ℓ) T C π hπ hOld]
      intro hJ f g Q h z hz d
      exact reflexive_lower_full_values hn hm _ hJ h z hz d
  intro f g Q h z hz d
  exact hValues hData.1 h z hz d

end
end Hironaka.HironakaOriginalPreparedCurrentLowerFullValues
