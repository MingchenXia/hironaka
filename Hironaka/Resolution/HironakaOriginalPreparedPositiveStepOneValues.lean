/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedCurrentLowerFullValues
import Hironaka.Resolution.HironakaOriginalPositiveStepOneSmoothValues
/-! Genuine higher positive lower FULL and unchanged StepOne numerical values
after actual preparation, on the SAME given upper smooth Cartesian history. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedPositiveStepOneValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres HomogenizedIdealAlong HomogenizedIdealAlongTower
  StepOneValue StepOneLowerDomain StepOneValueMasked StepOneRegime
  HironakaOriginalFrozenRecursiveLower HironakaOriginalPreparedCurrentLower
  HironakaOriginalPreparedCurrentLowerFullValues
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionPositiveLowerHistory HironakaSmoothSubmersionPositiveMemberHistory
  HironakaSmoothSubmersionAllBranchHistory HironakaSmoothSubmersionCanonicalValueDimensionShift
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m : ℕ} {X Y Z : CMfd.{u} n} {A B : CMfd.{u} m}

/-- Genuine current lower membership and actual ALL4 positive-record transport
precede EVERY numerical comparison of the independently computed source lower. -/
theorem prepared_positive_run_lower_full_values
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T c)
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
      (invFamily hm ((m-n)+d+2)).inv J' (restrict V (tail Q r)) ⟨z,hp'⟩=
        familyDimensionMap (m-n) (d+2)
          ((invFamily hn (d+2)).inv J (restrict U (tail P r)) ⟨g z,hp⟩) := by
  let P : BlowupTower X Z := .step T C π hπ
  let r := runAt M P (g z)
  let U := lowerMask M (s+1) (head P r) ((tail P r).proj (g z))
  let V := lowerMask (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  let J := lowerMarkedM M (s+1) (head P r) ((tail P r).proj (g z))
  let J' := lowerMarkedM (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (k := 3) (invFamily hn 2) M hM hmax hn T hcan
  have hP : IsGeoTestTower M P := ⟨hb.2.1,hC⟩
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) P := (he.2 P).1.mpr hP
  have hData := current_lower_data_after_cut (k := 2) hn M hM hmax T hcan C hC π hπ hCuts (g z) hy hns
  have hNum := current_lower_full_smooth_values_after_stepone_cut
    (A := CMfd.of (n := m) V) (B := CMfd.of (n := m) (openPreimage (tail Q r) V))
    hn hm M hM hmax T hcan C hC π hπ hCuts (g z) hy hns
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
            (invFamily hm ((m-n)+d+2)).inv (markedPullback (m := m) p K) S w=
              familyDimensionMap (m-n) (d+2) ((invFamily hn (d+2)).inv K R (q w))
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
theorem prepared_positive_step_one_smooth_values
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q (.step T C π hπ) g) (s : ℕ) (z : B)
    (hy : g z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) (g z)) (hl : level M (.step T C π hπ) (g z)=s+1) (d : ℕ) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+d+2)) (markedPullback (m := m) f M) Q z=
      stepDimensionMap (familyDimensionMap (m-n) (d+2))
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) M (.step T C π hπ) (g z)) := by
  let P : BlowupTower X Z := .step T C π hπ
  let r := runAt M P (g z)
  let U := lowerMask M (s+1) (head P r) ((tail P r).proj (g z))
  let V := lowerMask (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  let J := lowerMarkedM M (s+1) (head P r) ((tail P r).proj (g z))
  let J' := lowerMarkedM (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  obtain ⟨hp,hp',hValues⟩ := prepared_positive_run_lower_full_values hn hm M hM hmax T hcan C hC π hπ hCuts
    h s z hy hns hl
  let yU : openPreimage (tail P r) U := ⟨g z,hp⟩
  let zV : openPreimage (tail Q r) V := ⟨z,hp'⟩
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (k := 3) (invFamily hn 2) M hM hmax hn T hcan
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
  have hSource : Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+d+2))
      (markedPullback (m := m) f M) Q z=
      toLex (s+1,((invFamily hm ((m-n)+d+2)).inv J' (restrict V (tail Q r)) zV :
        WithTop (ValTy ((m-n)+d+2)))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hnsSource,hRun,hLevel,hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp']
  have hTarget : Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) M P (g z)=
      toLex (s+1,((invFamily hn (d+2)).inv J (restrict U (tail P r)) yU : WithTop (ValTy (d+2)))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hns]
    change toLex (level M P (g z),Seq.StepOneValueMasked.lowerValueL (invFamily hn (d+2)) M
      (lowerMarkedM M) (level M P (g z)) (head P r) (tail P r) (g z))=_
    rw [hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp]
  rw [hSource,hTarget]
  unfold stepDimensionMap
  simp only [ofLex_toLex,WithTop.map_coe]
  exact congrArg (fun v : ValTy ((m-n)+d+2) => toLex (s+1,(v : WithTop (ValTy ((m-n)+d+2))))) (hValues d)

end
end Hironaka.HironakaOriginalPreparedPositiveStepOneValues
