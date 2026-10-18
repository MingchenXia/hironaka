/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedBoundThreeFullEtaleValues
import Hironaka.Resolution.HironakaOriginalStepOnePreparedLowerFullValues
import Hironaka.Resolution.HironakaOriginalPreparedCurrentLower
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalRecursiveFamily
/-! Actual computed current lower FULL values split the genuine run into
increment and reset, rather than identifying it with an old frozen reference. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedBoundFourCurrentLowerValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres HomogenizedIdealAlong StepOneValue StepOneValueMasked StepOneRegime InvDomainTowerAlong StepOneLowerDomain
  HironakaOriginalFrozenRecursiveLower HironakaOriginalPreparedCurrentLower
  HironakaOriginalStepOnePreparedLowerFullValues HironakaOriginalPreparedBoundThreeFullEtaleValues
  HironakaSmoothSubmersionOriginalRecursiveFamily BlowupRestrictOpen
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaOriginalAllStepOneEtaleValues
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y Z A B : CMfd.{u} n}

private theorem domain_three_at_depth (M : MarkedIdeal n X) (hM : IsInvDomain 3 M) (d : ℕ) :
    IsInvDomain (d+3) M := by
  refine ⟨hM.isWellFormed,?_,hM.one_le_d,hM.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨j,hj,hreg⟩ := hM.dimLE x hx
  exact ⟨j,by omega,hreg⟩

private theorem full_value_cast_depth (hn : 0<n) {a b : ℕ} (hab : a=b)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (z : Y) :
    congrArg ValTy hab ▸ (invFamily hn a).inv M T z=(invFamily hn b).inv M T z := by
  cases hab
  rfl

private theorem reflexive_lower_full_values (hn : 0<n)
    (J : MarkedIdeal n X) (hJ : IsInvDomain 3 J)
    {f : A → X} {g : B → X} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q .refl g) (z : B) (hz : g z∈J.cosupp) (d : ℕ) :
    (invFamily hn (d+3)).inv (markedPullback (m := n) f J) Q z=
      (invFamily hn (d+3)).inv J .refl (g z) := by
  have hcan : IsCanonical J ((invFamily hn (d+3)).inv J) .refl := trivial
  have hv := (IsActualTowerPullback.original_recursive_family hn hn h J
    (domain_three_at_depth J hJ d) hcan).2 z hz
  rw [Nat.sub_self] at hv
  have hCast := congrArg
    (fun v : ValTy (0+(d+3)) => congrArg ValTy (Nat.zero_add (d+3)) ▸ v) hv
  have hSourceCast := full_value_cast_depth hn (Nat.zero_add (d+3))
    (markedPullback (m := n) f J) Q z
  exact hSourceCast.symm.trans (hCast.trans
    (familyDimensionMap_zero (d+3) ((invFamily hn (d+3)).inv J .refl (g z))))

/-- Upper DOMAIN4 inputs construct lower DOMAIN3, OLD CAN, the actual
restricted centre and its full cut BEFORE the SAME lower Cartesian history
is used in the genuine prepared FULL-value comparison. -/
theorem original_stepone_bound_four_prepared_lower_etale_values
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 4 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 3) M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 3) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 3) M T c)
    {f : A → maskAt M T y}
    {g : B → openPreimage (.step (tail T (runAt M T y)) C π hπ) (maskAt M T y)}
    {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q
      (restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ)) g)
    (z : B) (hz : g z ∈ (geoTransformAlong (lowerAt M T y)
      (restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ))).cosupp) (d : ℕ) :
    (invFamily hn (d+3)).inv (markedPullback (m := n) f (lowerAt M T y)) Q z=
      (invFamily hn (d+3)).inv (lowerAt M T y)
        (restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ)) (g z) := by
  have hData := original_stepone_cut_actual_lower_preparation (k := 3) hn M hM hmax T hcan
    y hy hns C hC π hπ hCuts
  let J := lowerAt M T y
  let R := lowerTailAt M T y
  let V := patchAt M T y
  let C' : Set V := (Subtype.val : V → Y) ⁻¹' C
  let W := openPreimage (.step (tail T (runAt M T y)) C π hπ) (maskAt M T y)
  let π' : W → V := fun w => ⟨π w.val,w.property⟩
  have hπ' : IsBlowupAlong n C' π' :=
    isBlowupAlong_restrict hπ V (V.isOpen.preimage hπ.contMDiff.continuous)
  exact prepared_bound_three_full_etale_values
    (X := CMfd.of (n := n) (maskAt M T y)) (D := CMfd.of (n := n) V)
    (Z := CMfd.of (n := n) W) hn J hData.1 R hData.2.1 C' hData.2.2.1
    π' hπ' hData.2.2.2 h z hz d


/-- BOTH real run branches internally supply numerical naturality of the
exact CURRENT lower, after its genuine DOMAIN and TEST are constructed. -/
theorem current_lower_full_etale_values_after_bound_four_stepone_cut
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 4 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 3) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 3) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 3) M T c)
    (y : Z) (hy : y ∈ (geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) y) :
    let P := .step T C π hπ
    let J := lowerAt M P y
    let R := lowerTailAt M P y
    IsInvDomain 3 J ∧ IsGeoTestTower J R ∧
      ∀ {f : A → maskAt M P y} {g : B → patchAt M P y} {Q : BlowupTower A B},
        IsActualTowerPullback f Q R g → ∀ z : B,
          g z ∈ (geoTransformAlong J R).cosupp → ∀ d : ℕ,
            (invFamily hn (d+3)).inv (markedPullback (m := n) f J) Q z=
              (invFamily hn (d+3)).inv J R (g z) := by
  let P : BlowupTower X Z := .step T C π hπ
  have hData := current_lower_data_after_cut (k := 3) hn M hM hmax T hcan C hC π hπ hCuts y hy hns
  refine ⟨hData.1,hData.2.1,?_⟩
  let F : ℕ → ℕ → Prop := fun ℓ r =>
    let H := head P r
    let S := tail P r
    let W := lowerMask M ℓ H (S.proj y)
    let J := lowerMarkedM M ℓ H (S.proj y)
    let R := restrict W S
    IsInvDomain 3 J →
      ∀ {f : A → W} {g : B → openPreimage S W} {Q : BlowupTower A B},
        IsActualTowerPullback f Q R g → ∀ z : B,
          g z ∈ (geoTransformAlong J R).cosupp → ∀ d : ℕ,
            (invFamily hn (d+3)).inv (markedPullback (m := n) f J) Q z=
              (invFamily hn (d+3)).inv J R (g z)
  have hValues : F (level M P y) (runAt M P y) := by
    let ℓ := level M P y
    change F ℓ (regimeRun (stepRegime M ℓ) (.step T C π hπ) y)
    by_cases hOld : stepRegime M ℓ T (π y)
    · rw [regimeRun_step_of (stepRegime M ℓ) T C π hπ hOld]
      have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
        (k := 4) (invFamily hn 3) M hM hmax hn T hcan
      have hWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM.isWellFormed T hb.2.1
      have hOldPoint : π y ∈ (geoTransformAlong M T).cosupp :=
        proj_mem_cosupp_of_mem_cosupp hWF.isClosedSubmanifold_N hWF.isCoherent
          (.step .refl C π hπ) ⟨trivial,hC⟩ hy
      let G : ℕ → Prop := fun a => F a (regimeRun (stepRegime M a) T (π y)+1)
      have hOldValue : G (level M T (π y)) := by
        intro _hJ f g Q h z hz d
        exact original_stepone_bound_four_prepared_lower_etale_values hn M hM hmax T hcan
          (π y) hOldPoint hOld.2 C hC π hπ hCuts h z hz d
      exact (congrArg G hOld.1).mp hOldValue
    · rw [regimeRun_step_of_not (stepRegime M ℓ) T C π hπ hOld]
      intro hJ f g Q h z hz d
      exact reflexive_lower_full_values hn _ hJ h z hz d
  intro f g Q h z hz d
  exact hValues hData.1 h z hz d

end
end Hironaka.HironakaOriginalPreparedBoundFourCurrentLowerValues
