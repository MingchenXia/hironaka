/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedZeroOwnSmallValues
import Hironaka.Resolution.HironakaOriginalStepOneCutSourcePreparation
import Hironaka.Resolution.HironakaOriginalPreparedBoundFourCurrentLowerValues
/-! Real source DOMAIN4/current-lower FULL3 locality compares independent
OWN-small/OWN-large records in relative dimension ONE. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedZeroOwnLargeRelativeOneValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  BlowupTowerIsomorphism MaxLocusLocal HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneValueMasked
  StepOneRegime CanonicalCentres HironakaOriginalFrozenRecursiveLower
  HironakaOriginalPreparedCurrentLower HironakaOriginalPreparedBoundFourCurrentLowerValues
  HironakaOriginalPreparedZeroOwnSmallValues HironakaOriginalStepOneCutSourcePreparation
  HironakaOriginalSourceChoiceCartesian HironakaOriginalUntestedCurveSmoothValues
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionAllBranchHistory
  HironakaSmoothSubmersionPositiveMemberHistory
  HironakaSmoothSubmersionCanonicalValueDimensionShift
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m : ℕ} {X Y Z : CMfd.{u} n} {A B : CMfd.{u} m}

private theorem actual_nested_small_cartesian {D E : CMfd.{u} n}
    (S : BlowupTower D E) (W V : Opens D) (hVW : V≤W) :
    IsActualTowerPullback (fun p : V => (⟨p.val,hVW p.property⟩ : W))
      (restrict V S) (restrict W S)
      (fun z : openPreimage S V => (⟨z.val,hVW z.property⟩ : openPreimage S W)) := by
  have hNested := open_inclusion_actual_tower (nestedOpens W V) (restrict W S)
  have hIso := isTowerIso_restrict_nestedOpens (n := n) hVW S
  have hFlat := HironakaOriginalSourceChoiceCartesian.IsActualTowerPullback.source_isomorphism hNested hIso.symm
  exact hFlat

private theorem source_zero_current_model (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 4 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hc : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 3) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 3) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 3) M T c)
    (y : Z) (hy : y∈(geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) y)
    (hl : level M (.step T C π hπ) y=0) (r : ℕ)
    (hr : regimeRun (stepRegime M 0) (.step T C π hπ) y=r) :
    let P := .step T C π hπ
    let W := lowerMask M 0 (head P r) ((tail P r).proj y)
    let J := lowerMarkedM M 0 (head P r) ((tail P r).proj y)
    let R := restrict W (tail P r)
    ∃ hp : (tail P r).proj y∈W,
      IsInvDomain 3 J ∧ IsGeoTestTower J R ∧
      (⟨y,hp⟩ : openPreimage (tail P r) W)∈(geoTransformAlong J R).cosupp ∧
      ∀ {D E : CMfd.{u} n} {f : D → W} {g : E → openPreimage (tail P r) W}
        {Q : BlowupTower D E},IsActualTowerPullback f Q R g →
        ∀ z : E,g z∈(geoTransformAlong J R).cosupp → ∀ d : ℕ,
          (invFamily hn (d+3)).inv (markedPullback (m := n) f J) Q z=
            (invFamily hn (d+3)).inv J R (g z) := by
  let P : BlowupTower X Z := .step T C π hπ
  let F : ℕ → ℕ → Prop := fun ℓ j =>
    let W := lowerMask M ℓ (head P j) ((tail P j).proj y)
    let J := lowerMarkedM M ℓ (head P j) ((tail P j).proj y)
    let R := restrict W (tail P j)
    ∃ hp : (tail P j).proj y∈W,
      IsInvDomain 3 J ∧ IsGeoTestTower J R ∧
      (⟨y,hp⟩ : openPreimage (tail P j) W)∈(geoTransformAlong J R).cosupp ∧
      ∀ {D E : CMfd.{u} n} {f : D → W} {g : E → openPreimage (tail P j) W}
        {Q : BlowupTower D E},IsActualTowerPullback f Q R g →
        ∀ z : E,g z∈(geoTransformAlong J R).cosupp → ∀ d : ℕ,
          (invFamily hn (d+3)).inv (markedPullback (m := n) f J) Q z=
            (invFamily hn (d+3)).inv J R (g z)
  have hData := current_lower_data_after_cut (k := 3) hn M hM hmax T hc C hC π hπ hCuts y hy hns
  obtain ⟨hp,hPoint,_hDict⟩ := hData.2.2.2
  have hCurrent : F (level M P y) (runAt M P y) := by
    refine ⟨hp,hData.1,hData.2.1,hPoint,?_⟩
    intro D E f g Q h z hz d
    exact (current_lower_full_etale_values_after_bound_four_stepone_cut
      (A := D) (B := E) hn M hM hmax T hc C hC π hπ hCuts y hy hns).2.2 h z hz d
  have hIndex : runAt M P y=r := by
    unfold runAt
    rw [hl]
    exact hr
  have hZero : F 0 (runAt M P y) := (congrArg (fun ℓ => F ℓ (runAt M P y)) hl).mp hCurrent
  change F 0 r
  exact (congrArg (F 0) hIndex).mp hZero

private theorem relative_one_source_preparation (hn : 0<n) (hm : 0<m) (hrel : m-n=1)
    (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hc : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M) T)
    {f : A → X} {g : B → Y} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q T g)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T c) :
    let K := markedPullback (m := m) f M
    IsInvDomain 4 K ∧ IsMaximalOrderAlong K.N K.ideal K.d ∧ IsGeoTestTower K Q ∧
      IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hm 3) K) Q ∧
      (geoTransformAlong K Q).IsAdmissibleCentre (g ⁻¹' C) ∧
      ∀ x ∈ (geoTransformAlong K Q).cosupp,∀ c ∈ g ⁻¹' C,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hm 3) K Q x≤
          Seq.StepOneValueMasked.stepOneInvM (invFamily hm 3) K Q c := by
  let K := markedPullback (m := m) f M
  let F : ℕ → Prop := fun t =>
    IsInvDomain (t+1+2) K ∧ IsMaximalOrderAlong K.N K.ideal K.d ∧ IsGeoTestTower K Q ∧
      IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hm (t+1+1)) K) Q ∧
      (geoTransformAlong K Q).IsAdmissibleCentre (g ⁻¹' C) ∧
      ∀ x ∈ (geoTransformAlong K Q).cosupp,∀ c ∈ g ⁻¹' C,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hm (t+1+1)) K Q x≤
          Seq.StepOneValueMasked.stepOneInvM (invFamily hm (t+1+1)) K Q c
  have hActual : F (m-n) := original_stepone_cut_source_data (k := 1) hn hm M hM hmax hc h C hC hCuts
  have hZero : F 1 := (congrArg F hrel).mp hActual
  exact hZero

private theorem full_values_eq_of_depth (hn : 0<n) {a b : ℕ} (hab : a=b)
    {U V D E : CMfd.{u} n} (K : MarkedIdeal n U) (L : MarkedIdeal n V)
    (R : BlowupTower U D) (S : BlowupTower V E) (x : D) (y : E)
    (h : (invFamily hn b).inv K R x=(invFamily hn b).inv L S y) :
    (invFamily hn a).inv K R x=(invFamily hn a).inv L S y := by
  cases hab
  exact h

/-- Genuine small/large reflection on the SAME independent source OWN record;
the actual relative-dimension-one equality gives the genuine source bound. -/
theorem original_prepared_zero_own_large_relative_one_values
    (hn : 0<n) (hm : 0<m) (hrel : m-n=1) (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T c)
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
          ∀ d : ℕ,(invFamily hm ((m-n)+d+2)).inv JOwn (restrict W (tail Q r)) ⟨z,hpOwn⟩=
            familyDimensionMap (m-n) (d+2) ((invFamily hn (d+2)).inv J (restrict U (tail P r)) ⟨g z,hp⟩) := by
  cases hCart with
  | @step D' D Z' Z Q₀ T₀ g₀ h hg C₀ π₀ hπ₀ ρ hρ =>
    let P : BlowupTower X Z := .step T C π hπ
    let QS : BlowupTower A B := .step Q₀ (g₀ ⁻¹' C) ρ hρ
    let gS := HironakaSmoothSubmersionBlowupLift.actualLift hg hπ hρ
    have hPost : IsActualTowerPullback f QS P gS := .step h hg hπ hρ
    let K := markedPullback (m := m) f M
    have hSource := relative_one_source_preparation hn hm hrel M hM hmax T hcan h C hC hCuts
    have hKD : IsInvDomain 4 K := hSource.1
    have hKM : IsMaximalOrderAlong K.N K.ideal K.d := hSource.2.1
    have hKC : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hm 3) K) Q₀ := hSource.2.2.2.1
    have hCC : (geoTransformAlong K Q₀).IsAdmissibleCentre (g₀ ⁻¹' C) := hSource.2.2.2.2.1
    have hKCuts := hSource.2.2.2.2.2
    have hP : IsGeoTestTower M P := ⟨(Seq.StepOneBridge.isGeoTestTower_of_isCanonical
      (invFamily hn 2) M hM hmax hn T hcan).2.1,hC⟩
    have hCoeff := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.one_le_d
    have hBar : IsGeoTestTower (barMarked M) P := (hCoeff.2 P).1.mpr hP
    have hSmall := original_prepared_zero_own_small_values hn hm M hM hmax T hcan C hC π hπ hCuts hPost
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
      source_zero_current_model hm K hKD hKM Q₀ hKC (g₀ ⁻¹' C) hCC ρ hρ hKCuts z hyK hnsK hlK r hrK
    obtain ⟨hp,Vv,hVW,hzv,φ,η,_hCartSmall,_hRecordSmall,_hEndpointSmall,_hTestSmall,_hPointSmall,hSmallValues⟩ :=
      hSmall.2 z hy hns hl
    refine ⟨hp,hpOwn,?_⟩
    intro d
    have hOpen := actual_nested_small_cartesian (tail QS r)
      (lowerMask K 0 (head QS r) ((tail QS r).proj z)) Vv hVW
    have hSmallLarge := hValues hOpen (⟨z,hzv⟩ : openPreimage (tail QS r) Vv) hOwnPoint d
    have hDepth : (m-n)+d+2=d+3 := by omega
    have hSmallLarge' := full_values_eq_of_depth hm hDepth _ _ _ _ _ _ hSmallLarge
    exact hSmallLarge'.symm.trans (hSmallValues d)

end
end Hironaka.HironakaOriginalPreparedZeroOwnLargeRelativeOneValues
