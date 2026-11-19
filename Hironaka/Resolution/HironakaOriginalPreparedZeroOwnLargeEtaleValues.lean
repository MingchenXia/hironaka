/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedZeroOwnSmallValues
import Hironaka.Resolution.HironakaOriginalStepOneCutSourcePreparation
/-! True source-bound-three locality reflects genuine OWN-small values to
SAME independent OWN-large records in equal ambient dimension. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedZeroOwnLargeEtaleValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  BlowupTowerIsomorphism MaxLocusLocal HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneValueMasked
  StepOneRegime CanonicalCentres HironakaOriginalFrozenRecursiveLower
  HironakaOriginalPreparedCurrentLower HironakaOriginalPreparedCurrentLowerFullValues
  HironakaOriginalPreparedZeroOwnSmallValues HironakaOriginalStepOneCutSourcePreparation
  HironakaOriginalSourceChoiceCartesian HironakaOriginalUntestedCurveSmoothValues
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionAllBranchHistory
  HironakaSmoothSubmersionPositiveMemberHistory
  HironakaSmoothSubmersionCanonicalValueDimensionShift
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y Z A B : CMfd.{u} n}

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
    (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hc : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T c)
    (y : Z) (hy : y∈(geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) y)
    (hl : level M (.step T C π hπ) y=0) (r : ℕ)
    (hr : regimeRun (stepRegime M 0) (.step T C π hπ) y=r) :
    let P := .step T C π hπ
    let W := lowerMask M 0 (head P r) ((tail P r).proj y)
    let J := lowerMarkedM M 0 (head P r) ((tail P r).proj y)
    let R := restrict W (tail P r)
    ∃ hp : (tail P r).proj y∈W,
      IsInvDomain 2 J ∧ IsGeoTestTower J R ∧
      (⟨y,hp⟩ : openPreimage (tail P r) W)∈(geoTransformAlong J R).cosupp ∧
      ∀ {D E : CMfd.{u} n} {f : D → W} {g : E → openPreimage (tail P r) W}
        {Q : BlowupTower D E},IsActualTowerPullback f Q R g →
        ∀ z : E,g z∈(geoTransformAlong J R).cosupp → ∀ d : ℕ,
          (invFamily hn ((n-n)+d+2)).inv (markedPullback (m := n) f J) Q z=
            familyDimensionMap (n-n) (d+2) ((invFamily hn (d+2)).inv J R (g z)) := by
  let P : BlowupTower X Z := .step T C π hπ
  let F : ℕ → ℕ → Prop := fun ℓ j =>
    let W := lowerMask M ℓ (head P j) ((tail P j).proj y)
    let J := lowerMarkedM M ℓ (head P j) ((tail P j).proj y)
    let R := restrict W (tail P j)
    ∃ hp : (tail P j).proj y∈W,
      IsInvDomain 2 J ∧ IsGeoTestTower J R ∧
      (⟨y,hp⟩ : openPreimage (tail P j) W)∈(geoTransformAlong J R).cosupp ∧
      ∀ {D E : CMfd.{u} n} {f : D → W} {g : E → openPreimage (tail P j) W}
        {Q : BlowupTower D E},IsActualTowerPullback f Q R g →
        ∀ z : E,g z∈(geoTransformAlong J R).cosupp → ∀ d : ℕ,
          (invFamily hn ((n-n)+d+2)).inv (markedPullback (m := n) f J) Q z=
            familyDimensionMap (n-n) (d+2) ((invFamily hn (d+2)).inv J R (g z))
  have hData := current_lower_data_after_cut (k := 2) hn M hM hmax T hc C hC π hπ hCuts y hy hns
  obtain ⟨hp,hPoint,_hDict⟩ := hData.2.2.2
  have hCurrent : F (level M P y) (runAt M P y) := by
    refine ⟨hp,hData.1,hData.2.1,hPoint,?_⟩
    intro D E f g Q h z hz d
    exact (current_lower_full_smooth_values_after_stepone_cut
      (A := D) (B := E) hn hn M hM hmax T hc C hC π hπ hCuts y hy hns).2.2 h z hz d
  have hIndex : runAt M P y=r := by
    unfold runAt
    rw [hl]
    exact hr
  have hZero : F 0 (runAt M P y) := (congrArg (fun ℓ => F ℓ (runAt M P y)) hl).mp hCurrent
  change F 0 r
  exact (congrArg (F 0) hIndex).mp hZero

private theorem equal_ambient_source_preparation (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hc : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M) T)
    {f : A → X} {g : B → Y} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q T g)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T c) :
    let K := markedPullback (m := n) f M
    IsInvDomain 3 K ∧ IsMaximalOrderAlong K.N K.ideal K.d ∧ IsGeoTestTower K Q ∧
      IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) Q ∧
      (geoTransformAlong K Q).IsAdmissibleCentre (g ⁻¹' C) ∧
      ∀ x ∈ (geoTransformAlong K Q).cosupp,∀ c ∈ g ⁻¹' C,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K Q x≤
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K Q c := by
  let K := markedPullback (m := n) f M
  let F : ℕ → Prop := fun t =>
    IsInvDomain (t+1+2) K ∧ IsMaximalOrderAlong K.N K.ideal K.d ∧ IsGeoTestTower K Q ∧
      IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (t+1+1)) K) Q ∧
      (geoTransformAlong K Q).IsAdmissibleCentre (g ⁻¹' C) ∧
      ∀ x ∈ (geoTransformAlong K Q).cosupp,∀ c ∈ g ⁻¹' C,
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (t+1+1)) K Q x≤
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn (t+1+1)) K Q c
  have hActual : F (n-n) := original_stepone_cut_source_data (k := 1) hn hn M hM hmax hc h C hC hCuts
  have hZero : F 0 := (congrArg F (Nat.sub_self n)).mp hActual
  exact hZero

/-- Genuine small/large reflection on the SAME independent source OWN record;
only the equality of actual ambient dimensions is used for the source bound. -/
theorem original_prepared_zero_own_large_etale_values
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (hCart : IsActualTowerPullback f Q (.step T C π hπ) g) :
    IsGeoTestTower (markedPullback (m := n) f M) Q ∧
      ∀ z : B,g z∈(geoTransformAlong M (.step T C π hπ)).cosupp →
        ¬IsSpecial M (.step T C π hπ) (g z) → level M (.step T C π hπ) (g z)=0 →
        let P := .step T C π hπ
        let K := markedPullback (m := n) f M
        let r := regimeRun (stepRegime M 0) P (g z)
        let U := lowerMask M 0 (head P r) ((tail P r).proj (g z))
        let J := lowerMarkedM M 0 (head P r) ((tail P r).proj (g z))
        let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
        let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
        ∃ (hp : (tail P r).proj (g z)∈U) (hpOwn : (tail Q r).proj z∈W),
          ∀ d : ℕ,(invFamily hn (d+2)).inv JOwn (restrict W (tail Q r)) ⟨z,hpOwn⟩=
            (invFamily hn (d+2)).inv J (restrict U (tail P r)) ⟨g z,hp⟩ := by
  cases hCart with
  | @step D' D Z' Z Q₀ T₀ g₀ h hg C₀ π₀ hπ₀ ρ hρ =>
    let P : BlowupTower X Z := .step T C π hπ
    let QS : BlowupTower A B := .step Q₀ (g₀ ⁻¹' C) ρ hρ
    let gS := HironakaSmoothSubmersionBlowupLift.actualLift hg hπ hρ
    have hPost : IsActualTowerPullback f QS P gS := .step h hg hπ hρ
    let K := markedPullback (m := n) f M
    have hSource := equal_ambient_source_preparation hn M hM hmax T hcan h C hC hCuts
    have hKD : IsInvDomain 3 K := hSource.1
    have hKM : IsMaximalOrderAlong K.N K.ideal K.d := hSource.2.1
    have hKC : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) Q₀ := hSource.2.2.2.1
    have hCC : (geoTransformAlong K Q₀).IsAdmissibleCentre (g₀ ⁻¹' C) := hSource.2.2.2.2.1
    have hKCuts := hSource.2.2.2.2.2
    have hP : IsGeoTestTower M P := ⟨(Seq.StepOneBridge.isGeoTestTower_of_isCanonical
      (invFamily hn 2) M hM hmax hn T hcan).2.1,hC⟩
    have hCoeff := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.one_le_d
    have hBar : IsGeoTestTower (barMarked M) P := (hCoeff.2 P).1.mpr hP
    have hSmall := original_prepared_zero_own_small_values hn hn M hM hmax T hcan C hC π hπ hCuts hPost
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
      source_zero_current_model hn K hKD hKM Q₀ hKC (g₀ ⁻¹' C) hCC ρ hρ hKCuts z hyK hnsK hlK r hrK
    obtain ⟨hp,Vv,hVW,hzv,φ,η,_hCartSmall,_hRecordSmall,_hEndpointSmall,_hTestSmall,_hPointSmall,hSmallValues⟩ :=
      hSmall.2 z hy hns hl
    refine ⟨hp,hpOwn,?_⟩
    intro d
    have hOpen := actual_nested_small_cartesian (tail QS r)
      (lowerMask K 0 (head QS r) ((tail QS r).proj z)) Vv hVW
    have hSmallLarge := hValues hOpen (⟨z,hzv⟩ : openPreimage (tail QS r) Vv) hOwnPoint d
    exact (strictMono_familyDimensionMap (n-n) (d+2)).injective
      (hSmallLarge.symm.trans (hSmallValues d))

end
end Hironaka.HironakaOriginalPreparedZeroOwnLargeEtaleValues
