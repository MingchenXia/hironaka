/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPositiveStepOneCutLowerTest

/-! Original Step One whole cuts construct genuine FULL lower invariant cuts
on the SAME canonical lower history, before recursive preparation is invoked. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalStepOneInheritedLowerCut
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres HomogenizedIdealAlong StepOneValue StepOneValueMasked StepOneRegime
  StepOneCanonicalTail StepOneMaskTower HironakaOriginalFrozenRecursiveLower
  HironakaOriginalPositiveStepOneCutLowerTest
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
variable {n k : ℕ} {X Y Z : CMfd.{u} n}

theorem original_stepone_cut_inherited_lower_values (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T c) :
    ∀ c : patchAt M T y,c.val ∈ C →
      c ∈ (geoTransformAlong (lowerAt M T y) (lowerTailAt M T y)).cosupp ∧
      ∀ p : patchAt M T y,
        p ∈ (geoTransformAlong (lowerAt M T y) (lowerTailAt M T y)).cosupp →
          (invFamily hn k).inv (lowerAt M T y) (lowerTailAt M T y) p≤
            (invFamily hn k).inv (lowerAt M T y) (lowerTailAt M T y) c := by
  have hData := actual_lower_domain_and_cosupport_dictionary hn M hM hmax T hcan y hy hns
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (k := k+1) (invFamily hn k) M hM hmax hn T hcan
  have hyBar : y ∈ (geoTransformAlong (barMarked M) T).cosupp := by rwa [hb.2.2]
  obtain ⟨hReg,_⟩ := stepRegime_and_mem_cosupp_head M hM.isWellFormed T hb.1 hyBar hns
  intro c hc
  have hGe : level M T y≤level M T c := by
    have h := Prod.Lex.le_iff.mp (hCuts y hy c hc)
    rw [Seq.StepOneValueMasked.stepOneInvL_fst,Seq.StepOneValueMasked.stepOneInvL_fst] at h
    exact h.elim (fun h => h.le) (fun h => h.1.le)
  have hLe : level M T c≤level M T y := by
    have h := level_le_of_mem_lowerMask M (fun A hA => hM.isWellFormed.isSNCDivisor.1 A hA)
      (head T (runAt M T y)) (tail T (runAt M T y)) hReg.1 c.property
    rwa [head_append_tail] at h
  have hcCos : c ∈ (geoTransformAlong (lowerAt M T y) (lowerTailAt M T y)).cosupp :=
    (hData.2.2.2 c).mpr ⟨hC.2.1 hc,le_antisymm hLe hGe⟩
  refine ⟨hcCos,?_⟩
  intro p hp
  have hpCos := ((hData.2.2.2 p).mp hp).1
  have hpValue := stepOneInvM_eq_actual_fixed_lower hn M hM hmax T hcan y hy hns p hp
  have hcValue := stepOneInvM_eq_actual_fixed_lower hn M hM hmax T hcan y hy hns c hcCos
  have hBound := hCuts p hpCos c hc
  rw [hpValue,hcValue] at hBound
  rcases Prod.Lex.le_iff.mp hBound with hlt | ⟨_,hle⟩
  · exact False.elim ((lt_irrefl _) hlt)
  · exact WithTop.coe_le_coe.mp hle

theorem original_positive_stepone_cut_lower_maximum (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T y)
    (s : ℕ) (hlevel : level M T y=s+1)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T c) :
    let r := regimeRun (stepRegime M (s+1)) T y
    let H := head T r
    let S := tail T r
    let W := lowerMask M (s+1) H (S.proj y)
    let J := lowerMarkedM M (s+1) H (S.proj y)
    let R := restrict W S
    IsInvDomain k J ∧ IsCanonical J ((invFamily hn k).inv J) R ∧
      IsGeoTestTower J (restrict W (.step S C π hπ)) ∧
        (Subtype.val : openPreimage S W → Y) ⁻¹' C ⊆
          maxLocus ((invFamily hn k).inv J R) (geoTransformAlong J R).cosupp := by
  have hNext := original_positive_stepone_cut_lower_test hn M hM hmax T hcan y hy hns
    s hlevel C hC π hπ (hCuts y hy)
  have hData := actual_lower_domain_and_cosupport_dictionary hn M hM hmax T hcan y hy hns
  have hInherited := original_stepone_cut_inherited_lower_values hn M hM hmax T hcan y hy hns
    C hC hCuts
  let P : ℕ → Prop := fun ℓ =>
    let r := regimeRun (stepRegime M ℓ) T y
    let H := head T r
    let S := tail T r
    let W := lowerMask M ℓ H (S.proj y)
    let J := lowerMarkedM M ℓ H (S.proj y)
    let R := restrict W S
    IsInvDomain k J ∧ IsCanonical J ((invFamily hn k).inv J) R ∧
      (Subtype.val : openPreimage S W → Y) ⁻¹' C ⊆
        maxLocus ((invFamily hn k).inv J R) (geoTransformAlong J R).cosupp
  have hActual : P (level M T y) := ⟨hData.2.1,hData.2.2.1,hInherited⟩
  have hFixed : P (s+1) := (congrArg P hlevel).mp hActual
  exact ⟨hFixed.1,hFixed.2.1,hNext.2.1,hFixed.2.2⟩

end
end Hironaka.HironakaOriginalStepOneInheritedLowerCut
