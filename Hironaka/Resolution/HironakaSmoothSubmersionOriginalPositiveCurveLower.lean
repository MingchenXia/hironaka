/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalCurveFamily
/-! Actual original positive-member inner recursion through the complete
curve family, with no monomial-inner-order or source-canonical certificate.
Complete mathematics preceded proofs in Mathematics.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalPositiveCurveLower
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  StepOneRegime StepOneValue StepOneValueMasked HomogenizedIdealAlong
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail GeneralValue
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionNonmonomialHistory HironakaSmoothSubmersionAllBranchHistory
  HironakaSmoothSubmersionPositiveMemberHistory
  HironakaSmoothSubmersionOriginalPositiveFamilyLeaf HironakaSmoothSubmersionOriginalGeneralFamilyLeaves
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaSmoothSubmersionOriginalCurveFamily
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

theorem original_positive_curve_lower_step_value (hn : 0 < n) (hm : 0 < m)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M) T)
    (s : ℕ) (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp)
    (hns : ¬ IsSpecial M T (g z)) (hl : level M T (g z) = s+1) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+1)) (markedPullback (m := m) f M) Q z =
      stepDimensionMap (familyDimensionMap (m-n) 1)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M T (g z)) := by
  obtain ⟨hp,hp',p,q,_,hrecord,hrestr,hq,hdom,hcanJ,hcosJ,_,_,_⟩ :=
    original_positive_canonical_lower_diagram hn h M hM hmax hcan s z hy hns hl
  let r := regimeRun (stepRegime M (level M T (g z))) T (g z)
  let U := lowerMask M (s+1) (head T r) ((tail T r).proj (g z))
  let V := lowerMask (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  let J := lowerMarkedM M (s+1) (head T r) ((tail T r).proj (g z))
  let J' := lowerMarkedM (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  let L := restrict U (tail T r)
  let L' := restrict V (tail Q r)
  let z' : openPreimage (tail Q r) V := ⟨z,hp'⟩
  let y' : openPreimage (tail T r) U := ⟨g z,hp⟩
  have hcosq : q z' ∈ (geoTransformAlong J L).cosupp := by rw [hq];exact hcosJ
  have hv := IsActualTowerPullback.actual_curve_family_value hn hm hrestr J hdom hcanJ z' hcosq
  rw [hrecord,hq] at hv
  have ht := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn 1) M hM hmax hn T hcan).1
  have hlevel := IsActualTowerPullback.bar_level_dictionary h M hM.isWellFormed ht z
  have hrun : regimeRun
      (stepRegime (markedPullback (m := m) f M) (level (markedPullback (m := m) f M) Q z)) Q z = r := by
    rw [hlevel]
    exact IsActualTowerPullback.all_stepRegime_run h M hM.isWellFormed ht _ z
  have hns' : ¬ IsSpecial (markedPullback (m := m) f M) Q z :=
    fun hsp => hns ((IsActualTowerPullback.all_isSpecial_dictionary h M hM.isWellFormed ht z).mp hsp)
  have hs : Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+1)) (markedPullback (m := m) f M) Q z =
      toLex (s+1,((invFamily hm ((m-n)+1)).inv J' L' z' : WithTop (ValTy ((m-n)+1)))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hns',hrun,hlevel,hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp']
  have htval : Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) M T (g z) =
      toLex (s+1,((invFamily hn 1).inv J L y' : WithTop (ValTy 1))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hns]
    change toLex (level M T (g z), Seq.StepOneValueMasked.lowerValueL
      (invFamily hn 1) M (lowerMarkedM M) (level M T (g z)) (head T r) (tail T r) (g z)) = _
    rw [hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp]
  rw [hs,htval]
  unfold stepDimensionMap
  simp only [ofLex_toLex,WithTop.map_coe]
  exact congrArg (fun v : ValTy ((m-n)+1) => toLex (s+1,(v : WithTop (ValTy ((m-n)+1))))) hv

theorem original_positive_curve_general_value (hn : 0 < n) (hm : 0 < m)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hcan : IsCanonical M ((invFamily hn 2).inv M) T)
    (o : ℕ) (ho : 0 < o) (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp)
    (hord : nmOrd (geoTransformAlong M T) (g z) = o) :
    let r := regimeRun (OrdRegime M o) T (g z)
    let U := ordMask (geoTransformAlong M (head T r)) o
    let P := compAt M o (head T r)
    let L := restrict U (tail T r)
    ∃ hp : (tail T r).proj (g z) ∈ U,
      (IsInvDomain 2 P ∧ IsMaximalOrderAlong P.N P.ideal P.d ∧
        IsCanonical P (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) P) L ∧
        (⟨g z,hp⟩ : openPreimage (tail T r) U) ∈ (geoTransformAlong P L).cosupp) ∧
      ∀ s : ℕ, ¬ IsSpecial P L (⟨g z,hp⟩ : openPreimage (tail T r) U) →
        level P L (⟨g z,hp⟩ : openPreimage (tail T r) U) = s+1 →
        (invFamily hm ((m-n)+2)).inv (markedPullback (m := m) f M) Q z =
          familyDimensionMap (m-n) 2 ((invFamily hn 2).inv M T (g z)) := by
  dsimp only
  obtain ⟨hp,hp',p,q,hrecord,hrestr,hq,hdom,hmax,hcanP,hcosP,_,_,_⟩ :=
    original_general_canonical_companion_diagram hn h M hM hcan o ho z hy hord
  refine ⟨hp,⟨hdom,hmax,hcanP,hcosP⟩,?_⟩
  intro s hns hl
  let r := regimeRun (OrdRegime M o) T (g z)
  let U := ordMask (geoTransformAlong M (head T r)) o
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q r)) o
  let P := compAt M o (head T r)
  let P' := compAt (markedPullback (m := m) f M) o (head Q r)
  let L := restrict U (tail T r)
  let L' := restrict V (tail Q r)
  let z' : openPreimage (tail Q r) V := ⟨z,hp'⟩
  have hcos' : q z' ∈ (geoTransformAlong P L).cosupp := by rw [hq];exact hcosP
  have hns' : ¬ IsSpecial P L (q z') := by rw [hq];exact hns
  have hl' : level P L (q z') = s+1 := by rw [hq];exact hl
  have hv := original_positive_curve_lower_step_value hn hm hrestr P hdom hmax hcanP s z' hcos' hns' hl'
  rw [hrecord,hq] at hv
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical (invFamily hn 2).isInvValue hM T hcan
  have hord' : nmOrd (geoTransformAlong (markedPullback (m := m) f M) Q) z = o :=
    (IsActualTowerPullback.orderAt_dictionary hn h M hM ht z).trans hord
  have hrun : regimeRun (OrdRegime (markedPullback (m := m) f M) o) Q z = r :=
    IsActualTowerPullback.fixed_order_regime_run hn h M hM ht o z
  change genInv (fun {A} J {B} S y => Seq.StepOneValueMasked.stepOneInvM (X := A)
      (invFamily hm ((m-n)+1)) J (Y := B) S y) (markedPullback (m := m) f M) Q z =
    generalDimensionMap (m-n) (stepDimensionMap (familyDimensionMap (m-n) 1))
      (genInv (fun {A} J {B} S y => Seq.StepOneValueMasked.stepOneInvM (X := A)
        (invFamily hn 1) J (Y := B) S y) M T (g z))
  unfold generalDimensionMap genInv genSecond
  rw [hord',hord,if_neg (ne_of_gt ho),hrun,genLowerValue_eq_of_mem _ _ hp',genLowerValue_eq_of_mem _ _ hp]
  simp only [if_neg (ne_of_gt ho),ofLex_toLex,Sum.map_inr,WithTop.map_coe]
  exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy ((m-n)+1)) =>
    toLex (o,toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy ((m-n)+1))))))) hv
end
end Hironaka.HironakaSmoothSubmersionOriginalPositiveCurveLower
