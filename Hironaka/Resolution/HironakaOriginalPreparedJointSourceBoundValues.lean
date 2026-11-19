/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedZeroOwnLargeRelativeOneValues
import Hironaka.Resolution.HironakaOriginalPreparedGeneralSmoothValues
import Hironaka.Resolution.HironakaOriginalPreparedPositiveStepOneValues
import Hironaka.Resolution.HironakaOriginalStepOnePreparedLowerFullValues
import Hironaka.Resolution.HironakaOriginalPreparedCurrentLower
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalRecursiveFamily
/-! Actual computed current lower FULL values split the genuine run into
increment and reset, rather than identifying it with an old frozen reference. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedJointSourceBoundValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HironakaOriginalPreparedCompanionSmoothDiagram GeneralCompare HironakaSmoothSubmersionActualFamilyMonomialLeaf
  HironakaOriginalPreparedGeneralSmoothValues GeneralValue NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  HironakaOriginalFullCutInheritedCompanion HironakaOriginalPreparedCurrentCompanion
  CanonicalCentres MaxLocusLocal HomogenizedIdealAlong HomogenizedIdealAlongTower BlowupTowerIsomorphism StepOneValue StepOneValueMasked StepOneRegime InvDomainTowerAlong StepOneLowerDomain
  HironakaOriginalFrozenRecursiveLower HironakaOriginalPreparedCurrentLower
  HironakaOriginalStepOnePreparedLowerFullValues
  HironakaSmoothSubmersionOriginalRecursiveFamily BlowupRestrictOpen
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaOriginalAllStepOneEtaleValues
  HironakaSmoothSubmersionPositiveLowerHistory HironakaSmoothSubmersionPositiveMemberHistory
  HironakaSmoothSubmersionAllBranchHistory HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionRelativeGeometry
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ContactStageKept ContactStageInvDomain
  HironakaOriginalGivenSmoothZeroChoices HironakaOriginalSourceChoiceCartesian HironakaOriginalZeroOwnSmallSmoothValues
  HironakaOriginalActualSmoothZeroMaskHistories HironakaOriginalUntestedCurveSmoothValues
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m k b : ℕ} {X Y Z : CMfd.{u} n} {A B : CMfd.{u} m}

private theorem domain_at_depth {j : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain j M) (d : ℕ) :
    IsInvDomain (d+j) M := by
  refine ⟨hM.isWellFormed,?_,hM.one_le_d,hM.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨j,hj,hreg⟩ := hM.dimLE x hx
  exact ⟨j,by omega,hreg⟩

/-- This is the actual original FULL goal at one SOURCE bound, used only
inside genuine strong induction. It supplies no replacement object. -/
private def PreparedFullAt (b : ℕ) : Prop :=
  ∀ {n m : ℕ} {X D Z : CMfd.{u} n} {A B : CMfd.{u} m}
    (hn : 0<n) (hm : 0<m) (j : ℕ), 2≤j → j+(m-n)=b →
    ∀ (M : MarkedIdeal n X), IsInvDomain j M → ∀ (T : BlowupTower X D),
    IsCanonical M ((invFamily hn j).inv M) T → ∀ (C : Set D),
    (geoTransformAlong M T).IsAdmissibleCentre C → ∀ (π : Z → D) (hπ : IsBlowupAlong n C π),
    (∀ x∈(geoTransformAlong M T).cosupp,∀ c∈C,
      (invFamily hn j).inv M T x≤(invFamily hn j).inv M T c) →
    ∀ {f : A → X} {g : B → Z} {Q : BlowupTower A B},
      IsActualTowerPullback f Q (.step T C π hπ) g → ∀ z : B,
      g z∈(geoTransformAlong M (.step T C π hπ)).cosupp → ∀ d : ℕ,
      (invFamily hm ((m-n)+(d+j))).inv (markedPullback (m := m) f M) Q z=
        familyDimensionMap (m-n) (d+j) ((invFamily hn (d+j)).inv M (.step T C π hπ) (g z))

/-- Apply the induction hypothesis on abstract manifold objects before any
open-subtype instance is instantiated in the actual lower consumer. -/
private theorem previous_full_values
    (ih : ∀ a<b,PreparedFullAt.{u} a) (hn : 0<n) (hm : 0<m) (j : ℕ)
    (hj : 2≤j) (hB : j+(m-n)<b) (M : MarkedIdeal n X) (hM : IsInvDomain j M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((invFamily hn j).inv M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x∈(geoTransformAlong M T).cosupp,∀ c∈C,
      (invFamily hn j).inv M T x≤(invFamily hn j).inv M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q (.step T C π hπ) g)
    (z : B) (hz : g z∈(geoTransformAlong M (.step T C π hπ)).cosupp) (d : ℕ) :
    (invFamily hm ((m-n)+(d+j))).inv (markedPullback (m := m) f M) Q z=
      familyDimensionMap (m-n) (d+j) ((invFamily hn (d+j)).inv M (.step T C π hπ) (g z)) := by
  exact ih (j+(m-n)) hB hn hm j hj rfl M hM T hc C hC π hπ hCuts h z hz d

private theorem reflexive_lower_full_values (hn : 0<n) (hm : 0<m) {j : ℕ}
    (J : MarkedIdeal n X) (hJ : IsInvDomain j J)
    {f : A → X} {g : B → X} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q .refl g) (z : B) (hz : g z∈J.cosupp) (d : ℕ) :
    (invFamily hm ((m-n)+(d+j))).inv (markedPullback (m := m) f J) Q z=
      familyDimensionMap (m-n) (d+j) ((invFamily hn (d+j)).inv J .refl (g z)) := by
  have hcan : IsCanonical J ((invFamily hn (d+j)).inv J) .refl := trivial
  exact (IsActualTowerPullback.original_recursive_family hn hm h J
    (domain_at_depth J hJ d) hcan).2 z hz

/-- Genuine original lower preparation reduces the SOURCE bound by one. -/
private theorem frozen_lower_values_of_smaller_source_bound
    (ih : ∀ a<b,PreparedFullAt.{u} a) (hBound : k+3+(m-n)≤b)
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain (k+3) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T c)
    {f : A → maskAt M T y}
    {g : B → openPreimage (.step (tail T (runAt M T y)) C π hπ) (maskAt M T y)}
    {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q
      (restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ)) g)
    (z : B) (hz : g z ∈ (geoTransformAlong (lowerAt M T y)
      (restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ))).cosupp) (d : ℕ) :
    (invFamily hm ((m-n)+(d+(k+2)))).inv (markedPullback (m := m) f (lowerAt M T y)) Q z=
      familyDimensionMap (m-n) (d+(k+2)) ((invFamily hn (d+(k+2))).inv (lowerAt M T y)
        (restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ)) (g z)) := by
  have hData := original_stepone_cut_actual_lower_preparation (k := k+2) hn M hM hmax T hcan
    y hy hns C hC π hπ hCuts
  let J := lowerAt M T y
  let R := lowerTailAt M T y
  let V := patchAt M T y
  let C' : Set V := (Subtype.val : V → Y) ⁻¹' C
  let W := openPreimage (.step (tail T (runAt M T y)) C π hπ) (maskAt M T y)
  let π' : W → V := fun w => ⟨π w.val,w.property⟩
  have hπ' : IsBlowupAlong n C' π' :=
    isBlowupAlong_restrict hπ V (V.isOpen.preimage hπ.contMDiff.continuous)
  let RNext : BlowupTower (CMfd.of (n := n) (maskAt M T y)) (CMfd.of (n := n) W) :=
    .step R C' π' hπ'
  have hTower : restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ)=RNext := rfl
  have hCart : IsActualTowerPullback f Q RNext g := by
    rw [←hTower]
    exact h
  have hz' : g z∈(geoTransformAlong J RNext).cosupp := by
    rw [←hTower]
    exact hz
  have hResult := previous_full_values
    (X := CMfd.of (n := n) (maskAt M T y)) (Y := CMfd.of (n := n) V)
    (Z := CMfd.of (n := n) W) ih hn hm (k+2) (by omega) (by omega) J hData.1 R hData.2.1
      C' hData.2.2.1 π' hπ' hData.2.2.2 hCart z hz' d
  have hTowerBack : (.step R C' π' hπ')=
      restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ) := hTower.symm
  rw [hTowerBack] at hResult
  exact hResult


/-- BOTH real run branches internally supply numerical naturality of the
exact CURRENT lower, after its genuine DOMAIN and TEST are constructed. -/
private theorem current_lower_values_of_smaller_source_bound
    (ih : ∀ a<b,PreparedFullAt.{u} a) (hBound : k+3+(m-n)≤b)
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain (k+3) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T c)
    (y : Z) (hy : y ∈ (geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) y) :
    let P := .step T C π hπ
    let J := lowerAt M P y
    let R := lowerTailAt M P y
    IsInvDomain (k+2) J ∧ IsGeoTestTower J R ∧
      ∀ {f : A → maskAt M P y} {g : B → patchAt M P y} {Q : BlowupTower A B},
        IsActualTowerPullback f Q R g → ∀ z : B,
          g z ∈ (geoTransformAlong J R).cosupp → ∀ d : ℕ,
            (invFamily hm ((m-n)+(d+(k+2)))).inv (markedPullback (m := m) f J) Q z=
              familyDimensionMap (m-n) (d+(k+2)) ((invFamily hn (d+(k+2))).inv J R (g z)) := by
  let P : BlowupTower X Z := .step T C π hπ
  have hData := current_lower_data_after_cut (k := k+2) hn M hM hmax T hcan C hC π hπ hCuts y hy hns
  refine ⟨hData.1,hData.2.1,?_⟩
  let F : ℕ → ℕ → Prop := fun ℓ r =>
    let H := head P r
    let S := tail P r
    let W := lowerMask M ℓ H (S.proj y)
    let J := lowerMarkedM M ℓ H (S.proj y)
    let R := restrict W S
    IsInvDomain (k+2) J →
      ∀ {f : A → W} {g : B → openPreimage S W} {Q : BlowupTower A B},
        IsActualTowerPullback f Q R g → ∀ z : B,
          g z ∈ (geoTransformAlong J R).cosupp → ∀ d : ℕ,
            (invFamily hm ((m-n)+(d+(k+2)))).inv (markedPullback (m := m) f J) Q z=
              familyDimensionMap (m-n) (d+(k+2)) ((invFamily hn (d+(k+2))).inv J R (g z))
  have hValues : F (level M P y) (runAt M P y) := by
    let ℓ := level M P y
    change F ℓ (regimeRun (stepRegime M ℓ) (.step T C π hπ) y)
    by_cases hOld : stepRegime M ℓ T (π y)
    · rw [regimeRun_step_of (stepRegime M ℓ) T C π hπ hOld]
      have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
        (k := k+3) (invFamily hn (k+2)) M hM hmax hn T hcan
      have hWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM.isWellFormed T hb.2.1
      have hOldPoint : π y ∈ (geoTransformAlong M T).cosupp :=
        proj_mem_cosupp_of_mem_cosupp hWF.isClosedSubmanifold_N hWF.isCoherent
          (.step .refl C π hπ) ⟨trivial,hC⟩ hy
      let G : ℕ → Prop := fun a => F a (regimeRun (stepRegime M a) T (π y)+1)
      have hOldValue : G (level M T (π y)) := by
        intro _hJ f g Q h z hz d
        exact frozen_lower_values_of_smaller_source_bound ih hBound hn hm M hM hmax T hcan
          (π y) hOldPoint hOld.2 C hC π hπ hCuts h z hz d
      exact (congrArg G hOld.1).mp hOldValue
    · rw [regimeRun_step_of_not (stepRegime M ℓ) T C π hπ hOld]
      intro hJ f g Q h z hz d
      exact reflexive_lower_full_values hn hm _ hJ h z hz d
  intro f g Q h z hz d
  exact hValues hData.1 h z hz d


/-- Genuine current lower membership and actual ALL4 positive-record transport
precede EVERY numerical comparison of the independently computed source lower. -/
private theorem positive_lower_values_of_smaller_source_bound
    (ih : ∀ a<b,PreparedFullAt.{u} a) (hBound : k+3+(m-n)≤b)
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain (k+3) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q (.step T C π hπ) g) (s : ℕ) (z : B)
    (hy : g z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) (g z)) (hl : level M (.step T C π hπ) (g z)=s+1) :
    let P := .step T C π hπ
    let r := runAt M P (g z)
    let U := lowerMask M (s+1) (head P r) ((tail P r).proj (g z))
    let V := lowerMask (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
    let J := lowerMarkedM M (s+1) (head P r) ((tail P r).proj (g z))
    let J' := lowerMarkedM (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
    ∃ hp : (tail P r).proj (g z) ∈ U,∃ hp' : (tail Q r).proj z ∈ V,∀ d : ℕ,
      (invFamily hm ((m-n)+(d+(k+2)))).inv J' (restrict V (tail Q r)) ⟨z,hp'⟩=
        familyDimensionMap (m-n) (d+(k+2))
          ((invFamily hn (d+(k+2))).inv J (restrict U (tail P r)) ⟨g z,hp⟩) := by
  let P : BlowupTower X Z := .step T C π hπ
  let r := runAt M P (g z)
  let U := lowerMask M (s+1) (head P r) ((tail P r).proj (g z))
  let V := lowerMask (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  let J := lowerMarkedM M (s+1) (head P r) ((tail P r).proj (g z))
  let J' := lowerMarkedM (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (k := k+3) (invFamily hn (k+2)) M hM hmax hn T hcan
  have hP : IsGeoTestTower M P := ⟨hb.2.1,hC⟩
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) P := (he.2 P).1.mpr hP
  have hData := current_lower_data_after_cut (k := k+2) hn M hM hmax T hcan C hC π hπ hCuts (g z) hy hns
  have hNum := current_lower_values_of_smaller_source_bound
    (A := CMfd.of (n := m) V) (B := CMfd.of (n := m) (openPreimage (tail Q r) V))
    ih hBound hn hm M hM hmax T hcan C hC π hπ hCuts (g z) hy hns
  let F : ℕ → Prop := fun a =>
    let W := lowerMask M a (head P r) ((tail P r).proj (g z))
    let K := lowerMarkedM M a (head P r) ((tail P r).proj (g z))
    let R := restrict W (tail P r)
    ∃ hp : (tail P r).proj (g z) ∈ W,
      (⟨g z,hp⟩ : openPreimage (tail P r) W) ∈ (geoTransformAlong K R).cosupp ∧
      ∀ {p : V → W} {q : openPreimage (tail Q r) V → openPreimage (tail P r) W}
        {S : BlowupTower (CMfd.of (n := m) V) (CMfd.of (n := m) (openPreimage (tail Q r) V))},
        IsActualTowerPullback p S R q → ∀ w : openPreimage (tail Q r) V,
          q w ∈ (geoTransformAlong K R).cosupp → ∀ d : ℕ,
            (invFamily hm ((m-n)+(d+(k+2)))).inv (markedPullback (m := m) p K) S w=
              familyDimensionMap (m-n) (d+(k+2)) ((invFamily hn (d+(k+2))).inv K R (q w))
  have hCurrent : F (level M P (g z)) := by
    obtain ⟨hp,hPoint,_hDict⟩ := hData.2.2.2
    refine ⟨hp,hPoint,?_⟩
    intro p q S hS w hw d
    exact hNum.2.2 hS w hw d
  have hFixed : F (s+1) := (congrArg F hl).mp hCurrent
  obtain ⟨hp,hPoint,hValues⟩ := hFixed
  obtain ⟨hH,_hR⟩ := (isGeoTestTower_iff_head_tail (barMarked M) P r).mp hBar
  obtain ⟨a,hHead,hTail,p,q,_hpSmooth,_hpcoord,hqcoord,hRecord,hRestr⟩ :=
    IsActualTowerPullback.exists_split_actual_positive_lower_diagram h M hM.isWellFormed hBar r s z
  have hPre := IsActualTowerPullback.all_maskA_dictionary hHead M hM.isWellFormed hH ((tail Q r).proj z)
  rw [←hTail.proj_comm z] at hPre
  have hV : (V : Set (split Q r).1)=a ⁻¹' (U : Set (split P r).1) := hPre
  have hp' : (tail Q r).proj z ∈ V := by
    change (tail Q r).proj z ∈ (V : Set (split Q r).1)
    rw [hV]
    change a ((tail Q r).proj z) ∈ U
    rw [←hTail.proj_comm z]
    exact hp
  let zV : openPreimage (tail Q r) V := ⟨z,hp'⟩
  let yU : openPreimage (tail P r) U := ⟨g z,hp⟩
  have hq : q zV=yU := Subtype.ext (hqcoord zV)
  have hTarget : q zV ∈ (geoTransformAlong J (restrict U (tail P r))).cosupp := by
    rw [hq]
    exact hPoint
  refine ⟨hp,hp',fun d => ?_⟩
  have hv := hValues hRestr zV hTarget d
  change markedPullback (m := m) p J=J' at hRecord
  rw [hRecord,hq] at hv
  exact hv

/-- Actual source lower records and points precede literal substitution in
the unchanged ORIGINAL sequence-aware positive StepOne definition. -/
private theorem positive_stepone_values_of_smaller_source_bound
    (ih : ∀ a<b,PreparedFullAt.{u} a) (hBound : k+3+(m-n)≤b)
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain (k+3) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q (.step T C π hπ) g) (s : ℕ) (z : B)
    (hy : g z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) (g z)) (hl : level M (.step T C π hπ) (g z)=s+1) (d : ℕ) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+(d+(k+2)))) (markedPullback (m := m) f M) Q z=
      stepDimensionMap (familyDimensionMap (m-n) (d+(k+2)))
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+(k+2))) M (.step T C π hπ) (g z)) := by
  let P : BlowupTower X Z := .step T C π hπ
  let r := runAt M P (g z)
  let U := lowerMask M (s+1) (head P r) ((tail P r).proj (g z))
  let V := lowerMask (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  let J := lowerMarkedM M (s+1) (head P r) ((tail P r).proj (g z))
  let J' := lowerMarkedM (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  obtain ⟨hp,hp',hValues⟩ := positive_lower_values_of_smaller_source_bound ih hBound hn hm M hM hmax T hcan C hC π hπ hCuts
    h s z hy hns hl
  let yU : openPreimage (tail P r) U := ⟨g z,hp⟩
  let zV : openPreimage (tail Q r) V := ⟨z,hp'⟩
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (k := k+3) (invFamily hn (k+2)) M hM hmax hn T hcan
  have hP : IsGeoTestTower M P := ⟨hb.2.1,hC⟩
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) P := (he.2 P).1.mpr hP
  have hLevel := IsActualTowerPullback.bar_level_dictionary h M hM.isWellFormed hBar z
  have hRun : regimeRun
      (stepRegime (markedPullback (m := m) f M) (level (markedPullback (m := m) f M) Q z)) Q z=r := by
    rw [hLevel]
    exact IsActualTowerPullback.all_stepRegime_run h M hM.isWellFormed hBar _ z
  have hnsSource : ¬IsSpecial (markedPullback (m := m) f M) Q z :=
    fun hs => hns ((IsActualTowerPullback.all_isSpecial_dictionary h M hM.isWellFormed hBar z).mp hs)
  have hSource : Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+(d+(k+2))))
      (markedPullback (m := m) f M) Q z=
      toLex (s+1,((invFamily hm ((m-n)+(d+(k+2)))).inv J' (restrict V (tail Q r)) zV :
        WithTop (ValTy ((m-n)+(d+(k+2)))))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hnsSource,hRun,hLevel,hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp']
  have hTarget : Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+(k+2))) M P (g z)=
      toLex (s+1,((invFamily hn (d+(k+2))).inv J (restrict U (tail P r)) yU : WithTop (ValTy (d+(k+2))))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hns]
    change toLex (level M P (g z),Seq.StepOneValueMasked.lowerValueL (invFamily hn (d+(k+2))) M
      (lowerMarkedM M) (level M P (g z)) (head P r) (tail P r) (g z))=_
    rw [hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp]
  rw [hSource,hTarget]
  unfold stepDimensionMap
  simp only [ofLex_toLex,WithTop.map_coe]
  exact congrArg (fun v : ValTy ((m-n)+(d+(k+2))) => toLex (s+1,(v : WithTop (ValTy ((m-n)+(d+(k+2))))))) (hValues d)


private theorem zero_current_lower_values_of_smaller_source_bound
    (ih : ∀ a<b,PreparedFullAt.{u} a) (hBound : k+3+(m-n)≤b)
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain (k+3) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T c)
    (y : Z) (hy : y ∈ (geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) y) (hl : level M (.step T C π hπ) y=0) :
    let P := .step T C π hπ
    let r := regimeRun (stepRegime M 0) P y
    let U := lowerMask M 0 (head P r) ((tail P r).proj y)
    let J := lowerMarkedM M 0 (head P r) ((tail P r).proj y)
    ∀ {f : A → U} {g : B → openPreimage (tail P r) U} {Q : BlowupTower A B},
      IsActualTowerPullback f Q (restrict U (tail P r)) g → ∀ z : B,
        g z ∈ (geoTransformAlong J (restrict U (tail P r))).cosupp → ∀ d : ℕ,
          (invFamily hm ((m-n)+(d+(k+2)))).inv (markedPullback (m := m) f J) Q z=
            familyDimensionMap (m-n) (d+(k+2))
              ((invFamily hn (d+(k+2))).inv J (restrict U (tail P r)) (g z)) := by
  let P : BlowupTower X Z := .step T C π hπ
  let F : ℕ → Prop := fun a =>
    let r := regimeRun (stepRegime M a) P y
    let U := lowerMask M a (head P r) ((tail P r).proj y)
    let J := lowerMarkedM M a (head P r) ((tail P r).proj y)
    ∀ {f : A → U} {g : B → openPreimage (tail P r) U} {Q : BlowupTower A B},
      IsActualTowerPullback f Q (restrict U (tail P r)) g → ∀ z : B,
        g z ∈ (geoTransformAlong J (restrict U (tail P r))).cosupp → ∀ d : ℕ,
          (invFamily hm ((m-n)+(d+(k+2)))).inv (markedPullback (m := m) f J) Q z=
            familyDimensionMap (m-n) (d+(k+2))
              ((invFamily hn (d+(k+2))).inv J (restrict U (tail P r)) (g z))
  have hNum := current_lower_values_of_smaller_source_bound
    (A := A) (B := B) ih hBound hn hm M hM hmax T hcan C hC π hπ hCuts y hy hns
  have hCurrent : F (level M P y) := by
    intro f g Q h z hz d
    exact hNum.2.2 h z hz d
  have hZero : F 0 := (congrArg F hl).mp hCurrent
  change F 0
  exact hZero

private theorem own_small_cartesian_geometry {D₀ : CMfd.{u} n} {Y₀ E₀ : CMfd.{u} m}
    (J : MarkedIdeal n X) (hJ : IsInvDomain (k+2) J) (R : BlowupTower X D₀) (hR : IsGeoTestTower J R)
    (S : BlowupTower Y₀ E₀) (V W Vu Vv : Opens Y₀) (hVuV : Vu≤V) (hVvW : Vv≤W)
    (JOwn : MarkedIdeal m W) (p : V → X) (q : openPreimage S V → D₀)
    (hp : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ p)
    (hCart : IsActualTowerPullback p (restrict V S) R q)
    (ψ : CMfd.of (n := m) Vv ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ CMfd.of (n := m) Vu)
    (ξ : CMfd.of (n := m) (openPreimage S Vv) ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯
      CMfd.of (n := m) (openPreimage S Vu))
    (hIso : IsTowerIso ψ (restrict Vv S) (restrict Vu S) ξ)
    (hParent : MarkedIdeal.pullback ψ (MarkedIdeal.pullback
      (fun b : Vu => (⟨b.val,hVuV b.property⟩ : V)) (markedPullback (m := m) p J))=
        MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn)
    (z : E₀) (hzu : S.proj z ∈ Vu) (hzv : S.proj z ∈ Vv)
    (hFix : ξ ⟨z,hzv⟩=⟨z,hzu⟩) (y : D₀) (hy : y ∈ (geoTransformAlong J R).cosupp)
    (hPoint : q ⟨z,hVuV hzu⟩=y) :
    ∃ (φ : Vv → X) (η : openPreimage S Vv → D₀),
      let K := MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn
      IsActualTowerPullback φ (restrict Vv S) R η ∧ markedPullback (m := m) φ J=K ∧ η ⟨z,hzv⟩=y ∧
      IsGeoTestTower K (restrict Vv S) ∧
        (⟨z,hzv⟩ : openPreimage S Vv) ∈ (geoTransformAlong K (restrict Vv S)).cosupp := by
  let iVu : Vu → V := fun b => ⟨b.val,hVuV b.property⟩
  let pFlat : Vu → X := p ∘ iVu
  let qFlat : openPreimage S Vu → D₀ := fun b => q ⟨b.val,hVuV b.property⟩
  have hFlat := IsActualTowerPullback.restrict_source_inside_open hVuV hCart
  change IsActualTowerPullback pFlat (restrict Vu S) R qFlat at hFlat
  have hiVu : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ iVu :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val (fun b => hVuV b.property)
  have hpFlat : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ pFlat := hp.contMDiff.comp hiVu
  let φ := pFlat ∘ ψ
  let η := qFlat ∘ ξ
  let K := MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn
  have hOwn : markedPullback (m := m) φ J=K := by
    change markedPullback (m := m) (pFlat ∘ ψ) J=K
    rw [whole_markedPullback_comp (f := pFlat) hpFlat ψ.contMDiff J hJ.isWellFormed.isCoherent]
    have hInner : markedPullback (m := m) pFlat J=
        markedPullback (m := m) iVu (markedPullback (m := m) p J) :=
      whole_markedPullback_comp (f := p) (g := iVu) hp.contMDiff hiVu J hJ.isWellFormed.isCoherent
    rw [hInner]
    exact hParent
  have hChoice := HironakaOriginalSourceChoiceCartesian.IsActualTowerPullback.source_isomorphism hFlat hIso
  have hEndpoint : η (⟨z,hzv⟩ : openPreimage S Vv)=y := by
    change qFlat (ξ ⟨z,hzv⟩)=y
    rw [hFix]
    exact hPoint
  have hTest := (IsActualTowerPullback.relative_marked_dictionary hChoice J hJ.isWellFormed hR).1
  rw [hOwn] at hTest
  have hCos := IsActualTowerPullback.relative_cosupport_dictionary hChoice J hJ.isWellFormed hR
  rw [hOwn] at hCos
  have hKPoint : (⟨z,hzv⟩ : openPreimage S Vv) ∈ (geoTransformAlong K (restrict Vv S)).cosupp := by
    rw [hCos]
    change η ⟨z,hzv⟩ ∈ (geoTransformAlong J R).cosupp
    rw [hEndpoint]
    exact hy
  exact ⟨φ,η,hChoice,hOwn,hEndpoint,hTest,hKPoint⟩

/-- The independent source OWN tangent and true small history are retained;
actual Cartesian geometry and point membership precede all FULL values. -/
private theorem zero_own_small_values_of_smaller_source_bound
    (ih : ∀ a<b,PreparedFullAt.{u} a) (hBound : k+3+(m-n)≤b)
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain (k+3) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (hCart : IsActualTowerPullback f Q (.step T C π hπ) g) :
    IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      ∀ z : B,g z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp →
        ¬IsSpecial M (.step T C π hπ) (g z) → level M (.step T C π hπ) (g z)=0 →
        let P := .step T C π hπ
        let K := markedPullback (m := m) f M
        let r := regimeRun (stepRegime M 0) P (g z)
        let U := lowerMask M 0 (head P r) ((tail P r).proj (g z))
        let J := lowerMarkedM M 0 (head P r) ((tail P r).proj (g z))
        let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
        let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
        ∃ (hp : (tail P r).proj (g z) ∈ U) (Vv : Opens (split Q r).1)
          (hVvW : Vv≤W) (hzv : (tail Q r).proj z ∈ Vv)
          (φ : Vv → U) (η : openPreimage (tail Q r) Vv → openPreimage (tail P r) U),
          let JSmall := MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn
          IsActualTowerPullback φ (restrict Vv (tail Q r)) (restrict U (tail P r)) η ∧
          markedPullback (m := m) φ J=JSmall ∧ η ⟨z,hzv⟩=⟨g z,hp⟩ ∧
          IsGeoTestTower JSmall (restrict Vv (tail Q r)) ∧
          (⟨z,hzv⟩ : openPreimage (tail Q r) Vv) ∈
            (geoTransformAlong JSmall (restrict Vv (tail Q r))).cosupp ∧
          ∀ d : ℕ,(invFamily hm ((m-n)+(d+(k+2)))).inv JSmall (restrict Vv (tail Q r)) ⟨z,hzv⟩=
            familyDimensionMap (m-n) (d+(k+2)) ((invFamily hn (d+(k+2))).inv J
              (restrict U (tail P r)) ⟨g z,hp⟩) := by
  let P : BlowupTower X Z := .step T C π hπ
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (k := k+3) (invFamily hn (k+2)) M hM hmax hn T hcan
  have hP : IsGeoTestTower M P := ⟨hb.2.1,hC⟩
  obtain ⟨hQ,hData⟩ := actual_zero_choices_with_endpoint (k := k+1) hn M hM hmax P hP hCart
  refine ⟨hQ,?_⟩
  intro z hy hns hl
  let K := markedPullback (m := m) f M
  let r := regimeRun (stepRegime M 0) P (g z)
  let U := lowerMask M 0 (head P r) ((tail P r).proj (g z))
  let J := lowerMarkedM M 0 (head P r) ((tail P r).proj (g z))
  let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
  let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
  obtain ⟨hp,hJD,hJT,_hDict,hJP,_hJCurrent⟩ :=
    actual_original_test_zero_mask_history (k := k+1) hn M hM hmax P hP (g z) hy hns hl
  obtain ⟨_hJ,a,V,p,q,_hHead,_hV,_hpV,_hpW,hpSmooth,hRecord,hR,hqcoord,
    _hCommonD,_hOwnD,_hCommonT,_hOwnT,Vu,Vv,hzu,hzv,ψ,ξ,hVuV,hVvW,hIso,hFix,
    hNestedCommon,hNestedOwn,hParent,_hAT,_hBT,_hCurrent,_hHeads⟩ := hData z hy hns hl
  have hParent' : MarkedIdeal.pullback ψ (MarkedIdeal.pullback
      (fun b : Vu => (⟨b.val,hVuV b.property⟩ : V)) (markedPullback (m := m) p J))=
      MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn := by
    rw [hRecord,hNestedCommon]
    exact hParent.trans hNestedOwn.symm
  have hPoint : q (⟨z,hVuV hzu⟩ : openPreimage (tail Q r) V)=
      (⟨g z,hp⟩ : openPreimage (tail P r) U) := Subtype.ext (hqcoord ⟨z,hVuV hzu⟩)
  obtain ⟨φ,η,hChoice,hOwn,hEndpoint,hTest,hBPoint⟩ :=
    own_small_cartesian_geometry (X := CMfd.of (n := n) U) (Y₀ := (split Q r).1)
      J hJD (restrict U (tail P r)) hJT (tail Q r) V W Vu Vv hVuV hVvW JOwn p q
      hpSmooth hR ψ ξ hIso hParent' z hzu hzv hFix ⟨g z,hp⟩ hJP hPoint
  let JSmall := MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn
  refine ⟨hp,Vv,hVvW,hzv,φ,η,hChoice,hOwn,hEndpoint,hTest,hBPoint,?_⟩
  intro d
  have hyModel : η (⟨z,hzv⟩ : openPreimage (tail Q r) Vv) ∈
      (geoTransformAlong J (restrict U (tail P r))).cosupp := by
    rw [hEndpoint]
    exact hJP
  have hv := zero_current_lower_values_of_smaller_source_bound
    (A := CMfd.of (n := m) Vv) (B := CMfd.of (n := m) (openPreimage (tail Q r) Vv))
    ih hBound hn hm M hM hmax T hcan C hC π hπ hCuts
    (g z) hy hns hl hChoice ⟨z,hzv⟩ hyModel d
  rw [hOwn,hEndpoint] at hv
  exact hv


private theorem family_value_cast_depth (hn : 0<n) {a c : ℕ} (hac : a=c)
    (J : MarkedIdeal n X) (T : BlowupTower X Y) (z : Y) :
    congrArg ValTy hac ▸ (invFamily hn a).inv J T z=(invFamily hn c).inv J T z := by
  cases hac
  rfl

private theorem actual_full_zero_map_elim (hn : 0<n) (J : MarkedIdeal n X)
    (Q : BlowupTower X Y) (z : Y) (j : ℕ) (v : ValTy j)
    (h : (invFamily hn ((n-n)+j)).inv J Q z=familyDimensionMap (n-n) j v) :
    (invFamily hn j).inv J Q z=v := by
  rw [Nat.sub_self] at h
  have hCast := congrArg (fun w : ValTy (0+j) => congrArg ValTy (Nat.zero_add j) ▸ w) h
  have hSourceCast := family_value_cast_depth hn (Nat.zero_add j) J Q z
  exact hSourceCast.symm.trans (hCast.trans (familyDimensionMap_zero j v))

private theorem actual_nested_small_cartesian {D E : CMfd.{u} n}
    (S : BlowupTower D E) (W V : Opens D) (hVW : V≤W) :
    IsActualTowerPullback (fun p : V => (⟨p.val,hVW p.property⟩ : W))
      (restrict V S) (restrict W S)
      (fun z : openPreimage S V => (⟨z.val,hVW z.property⟩ : openPreimage S W)) := by
  have hNested := open_inclusion_actual_tower (nestedOpens W V) (restrict W S)
  have hIso := isTowerIso_restrict_nestedOpens (n := n) hVW S
  have hFlat := HironakaOriginalSourceChoiceCartesian.IsActualTowerPullback.source_isomorphism hNested hIso.symm
  exact hFlat

private theorem source_zero_current_model
    (ih : ∀ a<b,PreparedFullAt.{u} a) (hBound : k+3≤b) (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+3) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hc : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T c)
    (y : Z) (hy : y∈(geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) y)
    (hl : level M (.step T C π hπ) y=0) (r : ℕ)
    (hr : regimeRun (stepRegime M 0) (.step T C π hπ) y=r) :
    let P := .step T C π hπ
    let W := lowerMask M 0 (head P r) ((tail P r).proj y)
    let J := lowerMarkedM M 0 (head P r) ((tail P r).proj y)
    let R := restrict W (tail P r)
    ∃ hp : (tail P r).proj y∈W,
      IsInvDomain (k+2) J ∧ IsGeoTestTower J R ∧
      (⟨y,hp⟩ : openPreimage (tail P r) W)∈(geoTransformAlong J R).cosupp ∧
      ∀ {D E : CMfd.{u} n} {f : D → W} {g : E → openPreimage (tail P r) W}
        {Q : BlowupTower D E},IsActualTowerPullback f Q R g →
        ∀ z : E,g z∈(geoTransformAlong J R).cosupp → ∀ d : ℕ,
          (invFamily hn (d+(k+2))).inv (markedPullback (m := n) f J) Q z=
            (invFamily hn (d+(k+2))).inv J R (g z) := by
  let P : BlowupTower X Z := .step T C π hπ
  let F : ℕ → ℕ → Prop := fun ℓ j =>
    let W := lowerMask M ℓ (head P j) ((tail P j).proj y)
    let J := lowerMarkedM M ℓ (head P j) ((tail P j).proj y)
    let R := restrict W (tail P j)
    ∃ hp : (tail P j).proj y∈W,
      IsInvDomain (k+2) J ∧ IsGeoTestTower J R ∧
      (⟨y,hp⟩ : openPreimage (tail P j) W)∈(geoTransformAlong J R).cosupp ∧
      ∀ {D E : CMfd.{u} n} {f : D → W} {g : E → openPreimage (tail P j) W}
        {Q : BlowupTower D E},IsActualTowerPullback f Q R g →
        ∀ z : E,g z∈(geoTransformAlong J R).cosupp → ∀ d : ℕ,
          (invFamily hn (d+(k+2))).inv (markedPullback (m := n) f J) Q z=
            (invFamily hn (d+(k+2))).inv J R (g z)
  have hData := current_lower_data_after_cut (k := k+2) hn M hM hmax T hc C hC π hπ hCuts y hy hns
  obtain ⟨hp,hPoint,_hDict⟩ := hData.2.2.2
  have hCurrent : F (level M P y) (runAt M P y) := by
    refine ⟨hp,hData.1,hData.2.1,hPoint,?_⟩
    intro D E f g Q h z hz d
    have hv := (current_lower_values_of_smaller_source_bound
      (A := D) (B := E) ih (by omega) hn hn M hM hmax T hc C hC π hπ hCuts y hy hns).2.2 h z hz d
    exact actual_full_zero_map_elim hn _ _ _ _ _ hv
  have hIndex : runAt M P y=r := by
    unfold runAt
    rw [hl]
    exact hr
  have hZero : F 0 (runAt M P y) := (congrArg (fun ℓ => F ℓ (runAt M P y)) hl).mp hCurrent
  change F 0 r
  exact (congrArg (F 0) hIndex).mp hZero

private theorem full_values_eq_of_depth (hn : 0<n) {a b : ℕ} (hab : a=b)
    {U V D E : CMfd.{u} n} (K : MarkedIdeal n U) (L : MarkedIdeal n V)
    (R : BlowupTower U D) (S : BlowupTower V E) (x : D) (y : E)
    (h : (invFamily hn b).inv K R x=(invFamily hn b).inv L S y) :
    (invFamily hn a).inv K R x=(invFamily hn a).inv L S y := by
  cases hab
  exact h

private theorem actual_source_preparation (hn : 0<n) (hm : 0<m)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+3) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hc : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M) T)
    {f : A → X} {g : B → Y} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q T g)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (hCuts : ∀ x∈(geoTransformAlong M T).cosupp,∀ c∈C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T c) :
    let K := markedPullback (m := m) f M
    IsInvDomain ((m-n)+k+3) K ∧ IsMaximalOrderAlong K.N K.ideal K.d ∧ IsGeoTestTower K Q ∧
      IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+2)) K) Q ∧
      (geoTransformAlong K Q).IsAdmissibleCentre (g ⁻¹' C) ∧
      ∀ x∈(geoTransformAlong K Q).cosupp,∀ c∈g ⁻¹' C,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+2)) K Q x≤
          Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+2)) K Q c := by
  exact HironakaOriginalStepOneCutSourcePreparation.original_stepone_cut_source_data
    (k := k+1) hn hm M hM hmax hc h C hC hCuts

/-- Genuine small/large reflection on the SAME independent source OWN record;
the genuine SOURCE-bound induction controls the actual source lower. -/
private theorem zero_own_large_values_of_smaller_source_bound
    (ih : ∀ a<b,PreparedFullAt.{u} a) (hBound : k+3+(m-n)≤b)
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain (k+3) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (hCart : IsActualTowerPullback f Q (.step T C π hπ) g) :
    IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      ∀ z : B,g z∈(geoTransformAlong M (.step T C π hπ)).cosupp →
        ¬IsSpecial M (.step T C π hπ) (g z) → level M (.step T C π hπ) (g z)=0 →
        let P := .step T C π hπ
        let K := markedPullback (m := m) f M
        let r := regimeRun (stepRegime M 0) P (g z)
        let U := lowerMask M 0 (head P r) ((tail P r).proj (g z))
        let J := lowerMarkedM M 0 (head P r) ((tail P r).proj (g z))
        let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
        let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
        ∃ (hp : (tail P r).proj (g z)∈U) (hpOwn : (tail Q r).proj z∈W),
          ∀ d : ℕ,(invFamily hm ((m-n)+(d+(k+2)))).inv JOwn (restrict W (tail Q r)) ⟨z,hpOwn⟩=
            familyDimensionMap (m-n) (d+(k+2)) ((invFamily hn (d+(k+2))).inv J (restrict U (tail P r)) ⟨g z,hp⟩) := by
  cases hCart with
  | @step D' D Z' Z Q₀ T₀ g₀ h hg C₀ π₀ hπ₀ ρ hρ =>
    let P : BlowupTower X Z := .step T C π hπ
    let QS : BlowupTower A B := .step Q₀ (g₀ ⁻¹' C) ρ hρ
    let gS := HironakaSmoothSubmersionBlowupLift.actualLift hg hπ hρ
    have hPost : IsActualTowerPullback f QS P gS := .step h hg hπ hρ
    let K := markedPullback (m := m) f M
    have hSource := actual_source_preparation hn hm M hM hmax T hcan h C hC hCuts
    have hKD : IsInvDomain ((m-n)+k+3) K := hSource.1
    have hKM : IsMaximalOrderAlong K.N K.ideal K.d := hSource.2.1
    have hKC : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+2)) K) Q₀ := hSource.2.2.2.1
    have hCC : (geoTransformAlong K Q₀).IsAdmissibleCentre (g₀ ⁻¹' C) := hSource.2.2.2.2.1
    have hKCuts := hSource.2.2.2.2.2
    have hP : IsGeoTestTower M P := ⟨(Seq.StepOneBridge.isGeoTestTower_of_isCanonical
      (invFamily hn (k+2)) M hM hmax hn T hcan).2.1,hC⟩
    have hCoeff := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.one_le_d
    have hBar : IsGeoTestTower (barMarked M) P := (hCoeff.2 P).1.mpr hP
    have hSmall := zero_own_small_values_of_smaller_source_bound ih hBound hn hm M hM hmax T hcan C hC π hπ hCuts hPost
    refine ⟨hSmall.1,?_⟩
    intro z hy hns hl
    let r := regimeRun (stepRegime M 0) P (gS z)
    have hyK : z∈(geoTransformAlong K QS).cosupp := by
      rw [IsActualTowerPullback.relative_cosupport_dictionary hPost M hM.isWellFormed hP]
      exact hy
    have hnsK : ¬IsSpecial K QS z := fun hs =>
      hns ((IsActualTowerPullback.all_isSpecial_dictionary hPost M hM.isWellFormed hBar z).mp hs)
    have hlK : level K QS z=0 :=
      (IsActualTowerPullback.bar_level_dictionary hPost M hM.isWellFormed hBar z).trans hl
    have hrK : regimeRun (stepRegime K 0) QS z=r :=
      IsActualTowerPullback.all_stepRegime_run hPost M hM.isWellFormed hBar 0 z
    obtain ⟨hpOwn,hOwnD,_hOwnT,hOwnPoint,hValues⟩ :=
      source_zero_current_model (k := (m-n)+k) ih (by omega) hm K hKD hKM Q₀ hKC (g₀ ⁻¹' C) hCC ρ hρ hKCuts z hyK hnsK hlK r hrK
    obtain ⟨hp,Vv,hVW,hzv,φ,η,_hCartSmall,_hRecordSmall,_hEndpointSmall,_hTestSmall,_hPointSmall,hSmallValues⟩ :=
      hSmall.2 z hy hns hl
    refine ⟨hp,hpOwn,?_⟩
    intro d
    have hOpen := actual_nested_small_cartesian (tail QS r)
      (lowerMask K 0 (head QS r) ((tail QS r).proj z)) Vv hVW
    have hSmallLarge := hValues hOpen (⟨z,hzv⟩ : openPreimage (tail QS r) Vv) hOwnPoint d
    have hDepth : (m-n)+(d+(k+2))=d+((m-n)+k+2) := by omega
    have hSmallLarge' := full_values_eq_of_depth hm hDepth _ _ _ _ _ _ hSmallLarge
    exact hSmallLarge'.symm.trans (hSmallValues d)


/-- Genuine independent OWN-large values and actual mask memberships precede
literal evaluation of the unchanged original zero StepOne branch. -/
private theorem zero_stepone_values_of_smaller_source_bound
    (ih : ∀ a<b,PreparedFullAt.{u} a) (hBound : k+3+(m-n)≤b)
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain (k+3) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q (.step T C π hπ) g) (z : B)
    (hy : g z∈(geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) (g z))
    (hl : level M (.step T C π hπ) (g z)=0) (d : ℕ) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+(d+(k+2)))) (markedPullback (m := m) f M) Q z=
      stepDimensionMap (familyDimensionMap (m-n) (d+(k+2)))
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+(k+2))) M (.step T C π hπ) (g z)) := by
  let P : BlowupTower X Z := .step T C π hπ
  let K := markedPullback (m := m) f M
  let r := regimeRun (stepRegime M 0) P (g z)
  let U := lowerMask M 0 (head P r) ((tail P r).proj (g z))
  let V := lowerMask K 0 (head Q r) ((tail Q r).proj z)
  let J := lowerMarkedM M 0 (head P r) ((tail P r).proj (g z))
  let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
  obtain ⟨hp,hpOwn,hValues⟩ := (zero_own_large_values_of_smaller_source_bound
    ih hBound hn hm M hM hmax T hcan C hC π hπ hCuts h).2 z hy hns hl
  let yU : openPreimage (tail P r) U := ⟨g z,hp⟩
  let zV : openPreimage (tail Q r) V := ⟨z,hpOwn⟩
  have hP : IsGeoTestTower M P := ⟨(Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn (k+2)) M hM hmax hn T hcan).2.1,hC⟩
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) P := (he.2 P).1.mpr hP
  have hLevel := IsActualTowerPullback.bar_level_dictionary h M hM.isWellFormed hBar z
  have hRun : regimeRun (stepRegime K (level K Q z)) Q z=r := by
    rw [hLevel,hl]
    exact IsActualTowerPullback.all_stepRegime_run h M hM.isWellFormed hBar 0 z
  have hnsSource : ¬IsSpecial K Q z := fun hs =>
    hns ((IsActualTowerPullback.all_isSpecial_dictionary h M hM.isWellFormed hBar z).mp hs)
  have hSource : Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+(d+(k+2)))) K Q z=
      toLex (0,((invFamily hm ((m-n)+(d+(k+2)))).inv JOwn (restrict V (tail Q r)) zV : WithTop (ValTy ((m-n)+(d+(k+2)))))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hnsSource,hRun,hLevel,hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hpOwn]
  have hTarget : Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+(k+2))) M P (g z)=
      toLex (0,((invFamily hn (d+(k+2))).inv J (restrict U (tail P r)) yU : WithTop (ValTy (d+(k+2))))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hns,hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp]
  rw [hSource,hTarget]
  unfold stepDimensionMap
  simp only [ofLex_toLex,WithTop.map_coe]
  exact congrArg (fun v : ValTy ((m-n)+(d+(k+2))) =>
    toLex (0,(v : WithTop (ValTy ((m-n)+(d+(k+2))))))) (hValues d)



/-- The SAME GIVEN actual source history precedes all points, depths and
special/zero/positive branches. No next canonicality is assumed. -/
private theorem all_stepone_values_of_smaller_source_bound
    (ih : ∀ a<b,PreparedFullAt.{u} a) (hBound : k+3+(m-n)≤b)
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain (k+3) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q (.step T C π hπ) g) :
    IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      ∀ z : B,g z∈(geoTransformAlong M (.step T C π hπ)).cosupp → ∀ d : ℕ,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+(d+(k+2)))) (markedPullback (m := m) f M) Q z=
          stepDimensionMap (familyDimensionMap (m-n) (d+(k+2)))
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+(k+2))) M (.step T C π hπ) (g z)) := by
  let P : BlowupTower X Z := .step T C π hπ
  have hP : IsGeoTestTower M P := ⟨(Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn (k+2)) M hM hmax hn T hcan).2.1,hC⟩
  have hQ := (IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hP).1
  refine ⟨hQ,?_⟩
  intro z hy d
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) P := (he.2 P).1.mpr hP
  have hLevel := IsActualTowerPullback.bar_level_dictionary h M hM.isWellFormed hBar z
  by_cases hsp : IsSpecial M P (g z)
  · have hSource := (IsActualTowerPullback.all_isSpecial_dictionary h M hM.isWellFormed hBar z).mpr hsp
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_pos hSource,if_pos hsp,hLevel]
    simp only [stepDimensionMap,ofLex_toLex,WithTop.map_top]
  · by_cases hl : level M P (g z)=0
    · exact zero_stepone_values_of_smaller_source_bound ih hBound hn hm M hM hmax T hcan C hC π hπ hCuts h z hy hsp hl d
    · obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero hl
      exact positive_stepone_values_of_smaller_source_bound ih hBound hn hm M hM hmax T hcan
        C hC π hπ hCuts h s z hy hsp hs d


private theorem reflexive_stepone_values (hn : 0<n) (hm : 0<m)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+3) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    {f : A → X} {g : B → X} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q .refl g) (z : B) (hz : g z∈M.cosupp) (d : ℕ) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+(d+(k+2)))) (markedPullback (m := m) f M) Q z=
      stepDimensionMap (familyDimensionMap (m-n) (d+(k+2)))
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+(k+2))) M .refl (g z)) := by
  exact (HironakaOriginalSourceStepOneCanonicalSmoothHistory.IsActualTowerPullback.original_stepOne_family
    (k := d+k+1) hn hm h M (domain_at_depth M hM d) hmax trivial).2 z hz

private theorem frozen_companion_stepone_values
    (ih : ∀ a<b,PreparedFullAt.{u} a) (hBound : k+3+(m-n)≤b) (hn : 0<n) (hm : 0<m)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+3) M) (T : BlowupTower X Y)
    (hc : IsCanonical M ((invFamily hn (k+3)).inv M) T)
    (y : Y) (hy : y∈(geoTransformAlong M T).cosupp) (hq : 1≤HironakaOriginalFrozenCompanionPresentation.orderAt M T y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      (invFamily hn (k+3)).inv M T x≤(invFamily hn (k+3)).inv M T c)
    {f : A → HironakaOriginalFrozenCompanionPresentation.maskAt M T y}
    {g : B → openPreimage (.step (tail T (HironakaOriginalFrozenCompanionPresentation.runAt M T y)) C π hπ) (HironakaOriginalFrozenCompanionPresentation.maskAt M T y)}
    {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q
      (restrict (HironakaOriginalFrozenCompanionPresentation.maskAt M T y) (.step (tail T (HironakaOriginalFrozenCompanionPresentation.runAt M T y)) C π hπ)) g)
    (z : B) (hz : g z∈(geoTransformAlong (HironakaOriginalFrozenCompanionPresentation.companionAt M T y)
      (restrict (HironakaOriginalFrozenCompanionPresentation.maskAt M T y) (.step (tail T (HironakaOriginalFrozenCompanionPresentation.runAt M T y)) C π hπ))).cosupp) (d : ℕ) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+(d+(k+2))))
        (markedPullback (m := m) f (HironakaOriginalFrozenCompanionPresentation.companionAt M T y)) Q z=
      stepDimensionMap (familyDimensionMap (m-n) (d+(k+2)))
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+(k+2))) (HironakaOriginalFrozenCompanionPresentation.companionAt M T y)
          (restrict (HironakaOriginalFrozenCompanionPresentation.maskAt M T y) (.step (tail T (HironakaOriginalFrozenCompanionPresentation.runAt M T y)) C π hπ)) (g z)) := by
  have hData := original_full_cut_prepared_companion_data (k := k+2) hn M hM T hc y hy hq C hC π hπ hCuts
  let J := HironakaOriginalFrozenCompanionPresentation.companionAt M T y
  let R := HironakaOriginalFrozenCompanionPresentation.companionTailAt M T y
  let V := HironakaOriginalFrozenCompanionPresentation.patchAt M T y
  let C' : Set V := (Subtype.val : V → Y) ⁻¹' C
  let W := openPreimage (.step (tail T (HironakaOriginalFrozenCompanionPresentation.runAt M T y)) C π hπ) (HironakaOriginalFrozenCompanionPresentation.maskAt M T y)
  let π' : W → V := fun w => ⟨π w.val,w.property⟩
  have hπ' : IsBlowupAlong n C' π' :=
    isBlowupAlong_restrict hπ V (V.isOpen.preimage hπ.contMDiff.continuous)
  have hC' : (geoTransformAlong J R).IsAdmissibleCentre C' := hData.2.2.2.1.2
  have hCuts' : ∀ p∈(geoTransformAlong J R).cosupp,∀ c∈C',
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) J R p≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+2)) J R c := by
    intro p hp c hcC
    exact (hData.2.2.2.2.2 hcC).2 p hp
  exact (all_stepone_values_of_smaller_source_bound
    (X := CMfd.of (n := n) (HironakaOriginalFrozenCompanionPresentation.maskAt M T y)) (Y := CMfd.of (n := n) V)
    (Z := CMfd.of (n := n) W) ih hBound hn hm J hData.1 hData.2.1 R hData.2.2.1 C' hC' π' hπ' hCuts' h).2 z hz d

/-- The actual current order-run data precede numerical comparisons; old
persistence and genuine reset are proved internally and kept separate. -/
private theorem current_companion_stepone_values
    (ih : ∀ a<b,PreparedFullAt.{u} a) (hBound : k+3+(m-n)≤b)
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain (k+3) M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((invFamily hn (k+3)).inv M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      (invFamily hn (k+3)).inv M T x≤(invFamily hn (k+3)).inv M T c)
    (y : Z) (hy : y∈(geoTransformAlong M (.step T C π hπ)).cosupp)
    (hp : 0<nmOrd (geoTransformAlong M (.step T C π hπ)) y) :
    let P := .step T C π hπ
    let q := nmOrd (geoTransformAlong M P) y
    let r := regimeRun (OrdRegime M q) P y
    let U := ordMask (geoTransformAlong M (head P r)) q
    let J := compAt M q (head P r)
    let R := restrict U (tail P r)
    IsInvDomain (k+3) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧ IsGeoTestTower J R ∧
      ∀ {A B : CMfd.{u} m} {f : A → U} {g : B → openPreimage (tail P r) U}
        {Q : BlowupTower A B},IsActualTowerPullback f Q R g →
        ∀ z : B,g z∈(geoTransformAlong J R).cosupp → ∀ d : ℕ,
          Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+(d+(k+2)))) (markedPullback (m := m) f J) Q z=
            stepDimensionMap (familyDimensionMap (m-n) (d+(k+2)))
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+(k+2))) J R (g z)) := by
  let P : BlowupTower X Z := .step T C π hπ
  let q := nmOrd (geoTransformAlong M P) y
  have hData := current_compAt_data_after_full_cut (k := k+2) hn M hM T hc C hC π hπ
    (fun x hx _ => hCuts x hx) y hy hp
  refine ⟨hData.1,hData.2.1,hData.2.2.1,?_⟩
  let F : ℕ → ℕ → Prop := fun o r =>
    let U := ordMask (geoTransformAlong M (head P r)) o
    let J := compAt M o (head P r)
    let R := restrict U (tail P r)
    IsInvDomain (k+3) J → IsMaximalOrderAlong J.N J.ideal J.d →
      ∀ {A B : CMfd.{u} m} {f : A → U} {g : B → openPreimage (tail P r) U}
        {Q : BlowupTower A B},IsActualTowerPullback f Q R g →
        ∀ z : B,g z∈(geoTransformAlong J R).cosupp → ∀ d : ℕ,
          Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+(d+(k+2)))) (markedPullback (m := m) f J) Q z=
            stepDimensionMap (familyDimensionMap (m-n) (d+(k+2)))
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+(k+2))) J R (g z))
  have hValues : F q (regimeRun (OrdRegime M q) P y) := by
    by_cases hOld : OrdRegime M q T (π y)
    · rw [regimeRun_step_of (OrdRegime M q) T C π hπ hOld]
      have hpOld : 1≤HironakaOriginalFrozenCompanionPresentation.orderAt M T (π y) := by
        change 1≤nmOrd (geoTransformAlong M T) (π y)
        rw [hOld.2]
        exact hp
      let G : ℕ → Prop := fun o => F o (regimeRun (OrdRegime M o) T (π y)+1)
      have hFrozen : G (HironakaOriginalFrozenCompanionPresentation.orderAt M T (π y)) := by
        intro _hJ _hMax A B f g Q h z hz d
        exact frozen_companion_stepone_values ih hBound hn hm M hM T hc (π y) hOld.1 hpOld C hC π hπ hCuts h z hz d
      exact (congrArg G hOld.2).mp hFrozen
    · rw [regimeRun_step_of_not (OrdRegime M q) T C π hπ hOld]
      intro hJ hMax A B f g Q h z hz d
      exact reflexive_stepone_values hn hm _ hJ hMax h z hz d
  intro A B f g Q h z hz d
  exact hValues hData.1 hData.2.1 h z hz d


/-- Actual CURRENT companion geometry and values precede literal GENERAL;
no next canonicality or old/current companion equality is assumed. -/
private theorem prepared_full_values_from_smaller_bound
    (ih : ∀ a<b,PreparedFullAt.{u} a) (hBound : k+3+(m-n)≤b)
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain (k+3) M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((invFamily hn (k+3)).inv M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      (invFamily hn (k+3)).inv M T x≤(invFamily hn (k+3)).inv M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q (.step T C π hπ) g)
    (z : B) (hz : g z∈(geoTransformAlong M (.step T C π hπ)).cosupp) (d : ℕ) :
    (invFamily hm ((m-n)+(d+(k+3)))).inv (markedPullback (m := m) f M) Q z=
      familyDimensionMap (m-n) (d+(k+3))
        ((invFamily hn (d+(k+3))).inv M (.step T C π hπ) (g z)) := by
  let P : BlowupTower X Z := .step T C π hπ
  have hT := (invFamily hn (k+3)).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  have hP : IsGeoTestTower M P := ⟨hT,hC⟩
  by_cases hZero : nmOrd (geoTransformAlong M P) (g z)=0
  · exact (IsActualTowerPullback.actual_family_monomial_leaf hn hm h M
      (domain_at_depth M hM d) hP z hZero).2
  have hPos : 0<nmOrd (geoTransformAlong M P) (g z) := Nat.pos_of_ne_zero hZero
  obtain ⟨hOrd,hRun,hp,hp',p,q,hRecord,hCart,_hCoord,hPoint,hDom,hMax,hTest,
    _hCurrent,hTargetPoint,_hSourceDom,_hSourceTest,_hSourceCurrent,_hSourcePoint,_hWhole,_hCos,_hHeads⟩ :=
    prepared_current_companion_smooth_diagram (k := k+2) hn M hM T hc C hC π hπ
      (fun x hx _ => hCuts x hx) h z hz hPos
  let o := nmOrd (geoTransformAlong M P) (g z)
  have ho : 0<o := hPos
  let r := regimeRun (OrdRegime M o) P (g z)
  let U := ordMask (geoTransformAlong M (head P r)) o
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q r)) o
  let J := compAt M o (head P r)
  let J' := compAt (markedPullback (m := m) f M) o (head Q r)
  let R := restrict U (tail P r)
  let R' := restrict V (tail Q r)
  let z' : openPreimage (tail Q r) V := ⟨z,hp'⟩
  change markedPullback (m := m) p J=J' at hRecord
  change IsActualTowerPullback p R' R q at hCart
  have hTarget : q z'∈(geoTransformAlong J R).cosupp := by
    rw [hPoint]
    exact hTargetPoint
  have hValues := current_companion_stepone_values
    ih hBound hn hm M hM T hc C hC π hπ hCuts (g z) hz hPos
  have hv := hValues.2.2.2 hCart z' hTarget d
  rw [hRecord,hPoint] at hv
  change genInv (fun {A} K {B} S w => Seq.StepOneValueMasked.stepOneInvM (X := A)
      (invFamily hm ((m-n)+(d+(k+2)))) K (Y := B) S w) (markedPullback (m := m) f M) Q z=
    generalDimensionMap (m-n) (stepDimensionMap (familyDimensionMap (m-n) (d+(k+2))))
      (genInv (fun {A} K {B} S w => Seq.StepOneValueMasked.stepOneInvM (X := A)
        (invFamily hn (d+(k+2))) K (Y := B) S w) M P (g z))
  unfold generalDimensionMap genInv genSecond
  rw [hOrd,show nmOrd (geoTransformAlong M P) (g z)=o from rfl,
    if_neg (ne_of_gt ho),hRun,genLowerValue_eq_of_mem _ _ hp',genLowerValue_eq_of_mem _ _ hp]
  simp only [if_neg (ne_of_gt ho),ofLex_toLex,Sum.map_inr,WithTop.map_coe]
  exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy ((m-n)+(d+(k+2)))) =>
    toLex (o,toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy ((m-n)+(d+(k+2))))))))) hv

/-- Genuine strong induction on SOURCE bound: every recursive lower use
strictly decreases j+(m-n), including the independently chosen OWN source. -/
private theorem prepared_full_at_source_bound (b : ℕ) : PreparedFullAt.{u} b := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro n m X D Z A B hn hm j hj hBound M hM T hc C hC π hπ hCuts f g Q h z hz d
    by_cases hTwo : j=2
    · subst j
      exact prepared_original_general_smooth_values hn hm M hM T hc C hC π hπ
        (fun x hx _ => hCuts x hx) h z hz d
    obtain ⟨k,rfl⟩ : ∃ k,j=k+3 := ⟨j-3,by omega⟩
    exact prepared_full_values_from_smaller_bound ih (by omega) hn hm M hM T hc C hC π hπ hCuts h z hz d

/-- Original inputs alone give ALL prepared FULL values; the strong
induction assertion is proved internally and is not a caller certificate. -/
theorem prepared_full_smooth_values (hn : 0<n) (hm : 0<m) (j : ℕ) (hj : 2≤j)
    (M : MarkedIdeal n X) (hM : IsInvDomain j M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((invFamily hn j).inv M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x∈(geoTransformAlong M T).cosupp,∀ c∈C,
      (invFamily hn j).inv M T x≤(invFamily hn j).inv M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q (.step T C π hπ) g)
    (z : B) (hz : g z∈(geoTransformAlong M (.step T C π hπ)).cosupp) (d : ℕ) :
    (invFamily hm ((m-n)+(d+j))).inv (markedPullback (m := m) f M) Q z=
      familyDimensionMap (m-n) (d+j) ((invFamily hn (d+j)).inv M (.step T C π hπ) (g z)) := by
  exact prepared_full_at_source_bound (j+(m-n)) hn hm j hj rfl M hM T hc C hC π hπ hCuts h z hz d

/-- Every prepared ORIGINAL StepOne branch uses the proved smaller-bound
FULL family, with no supplied lower value or lower TEST. -/
theorem prepared_step_one_smooth_values (hn : 0<n) (hm : 0<m) (j : ℕ) (hj : 2≤j)
    (M : MarkedIdeal n X) (hM : IsInvDomain (j+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hc : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn j) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x∈(geoTransformAlong M T).cosupp,∀ c∈C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn j) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn j) M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q (.step T C π hπ) g) :
    IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      ∀ z : B,g z∈(geoTransformAlong M (.step T C π hπ)).cosupp → ∀ d : ℕ,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+(d+j))) (markedPullback (m := m) f M) Q z=
        stepDimensionMap (familyDimensionMap (m-n) (d+j))
          (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+j)) M (.step T C π hπ) (g z)) := by
  obtain ⟨k,rfl⟩ : ∃ k,j=k+2 := ⟨j-2,by omega⟩
  exact all_stepone_values_of_smaller_source_bound
    (b := k+3+(m-n)) (fun a _ => prepared_full_at_source_bound a) (le_refl _) hn hm M hM hmax
      T hc C hC π hπ hCuts h

/-- Literal open Cartesian restriction supplies exact prepared FULL locality. -/
theorem prepared_full_value_restrict_open (hn : 0<n) (j : ℕ) (hj : 2≤j)
    (M : MarkedIdeal n X) (hM : IsInvDomain j M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((invFamily hn j).inv M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x∈(geoTransformAlong M T).cosupp,∀ c∈C,
      (invFamily hn j).inv M T x≤(invFamily hn j).inv M T c)
    (U : Opens X) (z : openPreimage (.step T C π hπ) U)
    (hz : z.val∈(geoTransformAlong M (.step T C π hπ)).cosupp) (d : ℕ) :
    (invFamily hn (d+j)).inv (markedPullback (m := n) (Subtype.val : U → X) M)
      (restrict U (.step T C π hπ)) z=
        (invFamily hn (d+j)).inv M (.step T C π hπ) z.val := by
  have hv := prepared_full_smooth_values hn hn j hj M hM T hc C hC π hπ hCuts
    (open_inclusion_actual_tower U (.step T C π hπ)) z hz d
  exact actual_full_zero_map_elim hn _ _ _ _ _ hv

/-- True nested restrictions compare through the SAME original full value. -/
theorem prepared_full_value_nested_open (hn : 0<n) (j : ℕ) (hj : 2≤j)
    (M : MarkedIdeal n X) (hM : IsInvDomain j M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((invFamily hn j).inv M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x∈(geoTransformAlong M T).cosupp,∀ c∈C,
      (invFamily hn j).inv M T x≤(invFamily hn j).inv M T c)
    (U V : Opens X) (hVU : V≤U) (z : openPreimage (.step T C π hπ) V)
    (hz : z.val∈(geoTransformAlong M (.step T C π hπ)).cosupp) (d : ℕ) :
    (invFamily hn (d+j)).inv (markedPullback (m := n) (Subtype.val : V → X) M)
      (restrict V (.step T C π hπ)) z=
    (invFamily hn (d+j)).inv (markedPullback (m := n) (Subtype.val : U → X) M)
      (restrict U (.step T C π hπ)) ⟨z.val,hVU z.property⟩ := by
  exact (prepared_full_value_restrict_open hn j hj M hM T hc C hC π hπ hCuts V z hz d).trans
    (prepared_full_value_restrict_open hn j hj M hM T hc C hC π hπ hCuts U
      ⟨z.val,hVU z.property⟩ hz d).symm


theorem prepared_current_lower_full_smooth_values
    (hn : 0<n) (hm : 0<m) (j : ℕ) (hj : 2≤j) (M : MarkedIdeal n X) (hM : IsInvDomain (j+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn j) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn j) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn j) M T c)
    (y : Z) (hy : y ∈ (geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) y) :
    let P := .step T C π hπ
    let J := lowerAt M P y
    let R := lowerTailAt M P y
    IsInvDomain j J ∧ IsGeoTestTower J R ∧
      ∀ {f : A → maskAt M P y} {g : B → patchAt M P y} {Q : BlowupTower A B},
        IsActualTowerPullback f Q R g → ∀ z : B,
          g z ∈ (geoTransformAlong J R).cosupp → ∀ d : ℕ,
            (invFamily hm ((m-n)+(d+j))).inv (markedPullback (m := m) f J) Q z=
              familyDimensionMap (m-n) (d+j) ((invFamily hn (d+j)).inv J R (g z)) := by
  obtain ⟨k,rfl⟩ : ∃ k,j=k+2 := ⟨j-2,by omega⟩
  exact current_lower_values_of_smaller_source_bound
    (b := k+3+(m-n)) (fun a _ => prepared_full_at_source_bound a) (le_refl _) hn hm M hM hmax
      T hcan C hC π hπ hCuts y hy hns

theorem prepared_zero_own_large_smooth_values
    (hn : 0<n) (hm : 0<m) (j : ℕ) (hj : 2≤j) (M : MarkedIdeal n X) (hM : IsInvDomain (j+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn j) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn j) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn j) M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (hCart : IsActualTowerPullback f Q (.step T C π hπ) g) :
    IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      ∀ z : B,g z∈(geoTransformAlong M (.step T C π hπ)).cosupp →
        ¬IsSpecial M (.step T C π hπ) (g z) → level M (.step T C π hπ) (g z)=0 →
        let P := .step T C π hπ
        let K := markedPullback (m := m) f M
        let r := regimeRun (stepRegime M 0) P (g z)
        let U := lowerMask M 0 (head P r) ((tail P r).proj (g z))
        let J := lowerMarkedM M 0 (head P r) ((tail P r).proj (g z))
        let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
        let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
        ∃ (hp : (tail P r).proj (g z)∈U) (hpOwn : (tail Q r).proj z∈W),
          ∀ d : ℕ,(invFamily hm ((m-n)+(d+j))).inv JOwn (restrict W (tail Q r)) ⟨z,hpOwn⟩=
            familyDimensionMap (m-n) (d+j) ((invFamily hn (d+j)).inv J (restrict U (tail P r)) ⟨g z,hp⟩) := by
  obtain ⟨k,rfl⟩ : ∃ k,j=k+2 := ⟨j-2,by omega⟩
  exact zero_own_large_values_of_smaller_source_bound
    (b := k+3+(m-n)) (fun a _ => prepared_full_at_source_bound a) (le_refl _) hn hm M hM hmax
      T hcan C hC π hπ hCuts hCart


end
end Hironaka.HironakaOriginalPreparedJointSourceBoundValues
