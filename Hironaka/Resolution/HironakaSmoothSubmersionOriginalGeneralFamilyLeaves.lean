/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalPositiveFamilyLeaf
import Hironaka.Invariant.GeneralCanonicalTail
/-! Original general companion data and actual full smooth family branches.
Complete mathematics preceded Lean in `Mathematics.tex`. No supplied source
canonical/value certificate; positive inner/zero-contact recursion stays open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalGeneralFamilyLeaves
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  StepOneRegime StepOneValue StepOneValueMasked HomogenizedIdealAlong
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail GeneralValue MaxOrderValue
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionPositiveMemberHistory HironakaSmoothSubmersionAllBranchHistory
  HironakaSmoothSubmersionNonmonomialHistory HironakaSmoothSubmersionHistoricalCompanionMasks
  HironakaSmoothSubmersionHistoricalControlledTail
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaSmoothSubmersionOriginalPositiveFamilyLeaf
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m k : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

private theorem base_submersion (h : IsActualTowerPullback f Q T g) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f := by
  induction h with
  | refl hf => exact hf
  | step _ _ _ _ ih => exact ih

theorem original_special_step_one_value (hn : 0 < n) (hm : 0 < m)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain (k+1) M) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) T)
    (z : D') (hsp : IsSpecial M T (g z)) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k)) (markedPullback (m := m) f M) Q z =
      stepDimensionMap (familyDimensionMap (m-n) k)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M T (g z)) := by
  have ht := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (invFamily hn k) M hM hmax hn T hcan).1
  have hsp' := (IsActualTowerPullback.all_isSpecial_dictionary h M hM.isWellFormed ht z).mpr hsp
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_pos hsp',if_pos hsp,IsActualTowerPullback.bar_level_dictionary h M hM.isWellFormed ht z]
  unfold stepDimensionMap
  simp only [ofLex_toLex,WithTop.map_top]

theorem original_general_canonical_companion_diagram (hn : 0 < n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain (k+2) M) (hcan : IsCanonical M ((invFamily hn (k+2)).inv M) T)
    (o : ℕ) (ho : 0 < o) (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp)
    (hord : nmOrd (geoTransformAlong M T) (g z) = o) :
    let r := regimeRun (OrdRegime M o) T (g z)
    let U := ordMask (geoTransformAlong M (head T r)) o
    let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q r)) o
    let P := compAt M o (head T r)
    let P' := compAt (markedPullback (m := m) f M) o (head Q r)
    let L := restrict U (tail T r)
    let L' := restrict V (tail Q r)
    ∃ (hp : (tail T r).proj (g z) ∈ U) (hp' : (tail Q r).proj z ∈ V)
      (p : V → U) (q : openPreimage (tail Q r) V → openPreimage (tail T r) U),
      markedPullback (m := m) p P = P' ∧ IsActualTowerPullback p L' L q ∧
      q (⟨z,hp'⟩ : openPreimage (tail Q r) V) = ⟨g z,hp⟩ ∧
      IsInvDomain (k+2) P ∧ IsMaximalOrderAlong P.N P.ideal P.d ∧
      IsCanonical P (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) P) L ∧
      (⟨g z,hp⟩ : openPreimage (tail T r) U) ∈ (geoTransformAlong P L).cosupp ∧
      IsInvDomain ((m-n)+k+2) P' ∧ IsGeoTestTower P' L' ∧
      (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong P' L').cosupp := by
  dsimp only
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn (k+2)).isInvValue hM T hcan
  let F := fun {A : CMfd.{u} n} (J : MarkedIdeal n A) {B : CMfd.{u} n}
    (S : BlowupTower A B) (y : B) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J S y
  have hF : IsMaxOrderValue n (k+2) F := StepOneSeq.isMaxOrderValue_stepOneInvM (k := k+2) (invFamily hn (k+1)) hn
  have hc : IsCanonical M (genInv F M) T := hcan
  have hd := GeneralCanonicalTail.hasGenLowerData_of_isCanonical F hF hn hM T ht hc (g z) hy o hord ho
  obtain ⟨hp,hdom,hmax,hcanP,hcosP⟩ := hd
  let r := regimeRun (OrdRegime M o) T (g z)
  let U := ordMask (geoTransformAlong M (head T r)) o
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q r)) o
  let P := compAt M o (head T r)
  let P' := compAt (markedPullback (m := m) f M) o (head Q r)
  let L := restrict U (tail T r)
  let L' := restrict V (tail Q r)
  change IsInvDomain (k+2) P at hdom
  change IsMaximalOrderAlong P.N P.ideal P.d at hmax
  change IsCanonical P (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) P) L at hcanP
  obtain ⟨p,q,hrecord,hqcoord,hrestr⟩ := IsActualTowerPullback.exists_actual_historical_tail hn h M hM ht r o
  change markedPullback (m := m) p P = P' at hrecord
  change IsActualTowerPullback p L' L q at hrestr
  obtain ⟨a,hhead,htail⟩ := IsActualTowerPullback.simultaneous_split h r
  have hheadT := ((isGeoTestTower_iff_head_tail M T r).mp ht).1
  have hpre : (V : Set (split Q r).1) = a ⁻¹' (U : Set (split T r).1) :=
    IsActualTowerPullback.order_mask_dictionary hn hhead M hM hheadT o
  have hp' : (tail Q r).proj z ∈ V := by
    change (tail Q r).proj z ∈ (V : Set (split Q r).1)
    rw [hpre]
    change a ((tail Q r).proj z) ∈ U
    rw [← htail.proj_comm z]
    exact hp
  have hq : q (⟨z,hp'⟩ : openPreimage (tail Q r) V) = (⟨g z,hp⟩ : openPreimage (tail T r) U) :=
    Subtype.ext (hqcoord (⟨z,hp'⟩ : openPreimage (tail Q r) V))
  have htP : IsGeoTestTower P L :=
    (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (invFamily hn (k+1)) P hdom hmax hn L hcanP).2.1
  have hsourceDom : IsInvDomain ((m-n)+k+2) P' := by
    have hd := isInvDomain_markedPullback_submersion (base_submersion hrestr) P hdom
    have hd' : IsInvDomain ((k+2)+(m-n)) P' := hrecord ▸ hd
    convert hd' using 1
    omega
  have hsourceT : IsGeoTestTower P' L' :=
    hrecord ▸ (IsActualTowerPullback.relative_marked_dictionary hrestr P hdom.isWellFormed htP).1
  have hsourceCos : (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong P' L').cosupp := by
    have hc : (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈
        (geoTransformAlong (markedPullback (m := m) p P) L').cosupp := by
      rw [IsActualTowerPullback.relative_cosupport_dictionary hrestr P hdom.isWellFormed htP]
      change _ ∈ (geoTransformAlong P L).cosupp
      rw [hq]
      exact hcosP
    exact hrecord ▸ hc
  exact ⟨hp,hp',p,q,hrecord,hrestr,hq,hdom,hmax,hcanP,hcosP,hsourceDom,hsourceT,hsourceCos⟩

theorem original_general_special_companion_value (hn : 0 < n) (hm : 0 < m)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain (k+2) M) (hcan : IsCanonical M ((invFamily hn (k+2)).inv M) T)
    (o : ℕ) (ho : 0 < o) (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp)
    (hord : nmOrd (geoTransformAlong M T) (g z) = o) :
    let r := regimeRun (OrdRegime M o) T (g z)
    let U := ordMask (geoTransformAlong M (head T r)) o
    let P := compAt M o (head T r)
    let L := restrict U (tail T r)
    ∃ hp : (tail T r).proj (g z) ∈ U,
      (IsInvDomain (k+2) P ∧ IsMaximalOrderAlong P.N P.ideal P.d ∧
        IsCanonical P (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) P) L ∧
        (⟨g z,hp⟩ : openPreimage (tail T r) U) ∈ (geoTransformAlong P L).cosupp) ∧
      (IsSpecial P L (⟨g z,hp⟩ : openPreimage (tail T r) U) →
        (invFamily hm ((m-n)+k+2)).inv (markedPullback (m := m) f M) Q z =
          familyDimensionMap (m-n) (k+2) ((invFamily hn (k+2)).inv M T (g z))) := by
  dsimp only
  obtain ⟨hp,hp',p,q,hrecord,hrestr,hq,hdom,hmax,hcanP,hcosP,_,_,_⟩ :=
    original_general_canonical_companion_diagram hn h M hM hcan o ho z hy hord
  refine ⟨hp,⟨hdom,hmax,hcanP,hcosP⟩,?_⟩
  intro hsp
  let r := regimeRun (OrdRegime M o) T (g z)
  let U := ordMask (geoTransformAlong M (head T r)) o
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q r)) o
  let P := compAt M o (head T r)
  let P' := compAt (markedPullback (m := m) f M) o (head Q r)
  let L := restrict U (tail T r)
  let L' := restrict V (tail Q r)
  let z' : openPreimage (tail Q r) V := ⟨z,hp'⟩
  have hsp' : IsSpecial P L (q z') := by rw [hq];exact hsp
  have hv := original_special_step_one_value hn hm hrestr P hdom hmax hcanP z' hsp'
  rw [hrecord,hq] at hv
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn (k+2)).isInvValue hM T hcan
  have hord' : nmOrd (geoTransformAlong (markedPullback (m := m) f M) Q) z = o :=
    (IsActualTowerPullback.orderAt_dictionary hn h M hM ht z).trans hord
  have hrun : regimeRun (OrdRegime (markedPullback (m := m) f M) o) Q z = r :=
    IsActualTowerPullback.fixed_order_regime_run hn h M hM ht o z
  change genInv (fun {A} J {B} S y =>
      Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hm ((m-n)+k+1)) J (Y := B) S y)
      (markedPullback (m := m) f M) Q z =
    generalDimensionMap (m-n) (stepDimensionMap (familyDimensionMap (m-n) (k+1)))
      (genInv (fun {A} J {B} S y =>
        Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn (k+1)) J (Y := B) S y) M T (g z))
  unfold generalDimensionMap genInv genSecond
  rw [hord',hord,if_neg (ne_of_gt ho),hrun,
    genLowerValue_eq_of_mem _ _ hp',genLowerValue_eq_of_mem _ _ hp]
  simp only [if_neg (ne_of_gt ho),ofLex_toLex,Sum.map_inr,WithTop.map_coe]
  exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy ((m-n)+k+1)) =>
    toLex (o,toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy ((m-n)+k+1))))))) hv

theorem original_general_positive_companion_leaf (hn : 0 < n) (hm : 0 < m)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain (k+2) M) (hcan : IsCanonical M ((invFamily hn (k+2)).inv M) T)
    (o : ℕ) (ho : 0 < o) (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp)
    (hord : nmOrd (geoTransformAlong M T) (g z) = o) :
    let r := regimeRun (OrdRegime M o) T (g z)
    let U := ordMask (geoTransformAlong M (head T r)) o
    let P := compAt M o (head T r)
    let L := restrict U (tail T r)
    ∃ hp : (tail T r).proj (g z) ∈ U,
      let y' : openPreimage (tail T r) U := ⟨g z,hp⟩
      (IsInvDomain (k+2) P ∧ IsMaximalOrderAlong P.N P.ideal P.d ∧
        IsCanonical P (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) P) L ∧
        y' ∈ (geoTransformAlong P L).cosupp) ∧
      ∀ s : ℕ, ¬ IsSpecial P L y' → level P L y' = s+1 →
        let r₁ := regimeRun (stepRegime P (level P L y')) L y'
        let U₁ := lowerMask P (s+1) (head L r₁) ((tail L r₁).proj y')
        let J := lowerMarkedM P (s+1) (head L r₁) ((tail L r₁).proj y')
        let L₁ := restrict U₁ (tail L r₁)
        ∃ hp₁ : (tail L r₁).proj y' ∈ U₁,
          (IsInvDomain (k+1) J ∧ IsCanonical J ((invFamily hn (k+1)).inv J) L₁ ∧
            (⟨y',hp₁⟩ : openPreimage (tail L r₁) U₁) ∈ (geoTransformAlong J L₁).cosupp) ∧
          (nmOrd (geoTransformAlong J L₁) (⟨y',hp₁⟩ : openPreimage (tail L r₁) U₁) = 0 →
            (invFamily hm ((m-n)+k+2)).inv (markedPullback (m := m) f M) Q z =
              familyDimensionMap (m-n) (k+2) ((invFamily hn (k+2)).inv M T (g z))) := by
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
  let y' : openPreimage (tail T r) U := ⟨g z,hp⟩
  have hcos' : q z' ∈ (geoTransformAlong P L).cosupp := by rw [hq];exact hcosP
  have hns' : ¬ IsSpecial P L (q z') := by rw [hq];exact hns
  have hl' : level P L (q z') = s+1 := by rw [hq];exact hl
  have hd := original_positive_step_one_monomial_leaf hn hm hrestr P hdom hmax hcanP s z' hcos' hns' hl'
  rw [hq] at hd
  obtain ⟨hp₁,hdata,hvalue⟩ := hd
  refine ⟨hp₁,hdata,?_⟩
  intro h0
  have hv := hvalue h0
  rw [hrecord] at hv
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn (k+2)).isInvValue hM T hcan
  have hord' : nmOrd (geoTransformAlong (markedPullback (m := m) f M) Q) z = o :=
    (IsActualTowerPullback.orderAt_dictionary hn h M hM ht z).trans hord
  have hrun : regimeRun (OrdRegime (markedPullback (m := m) f M) o) Q z = r :=
    IsActualTowerPullback.fixed_order_regime_run hn h M hM ht o z
  change genInv (fun {A} J {B} S y =>
      Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hm ((m-n)+k+1)) J (Y := B) S y)
      (markedPullback (m := m) f M) Q z =
    generalDimensionMap (m-n) (stepDimensionMap (familyDimensionMap (m-n) (k+1)))
      (genInv (fun {A} J {B} S y =>
        Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn (k+1)) J (Y := B) S y) M T (g z))
  unfold generalDimensionMap genInv genSecond
  rw [hord',hord,if_neg (ne_of_gt ho),hrun,
    genLowerValue_eq_of_mem _ _ hp',genLowerValue_eq_of_mem _ _ hp]
  simp only [if_neg (ne_of_gt ho),ofLex_toLex,Sum.map_inr,WithTop.map_coe]
  exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy ((m-n)+k+1)) =>
    toLex (o,toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy ((m-n)+k+1))))))) hv

end
end Hironaka.HironakaSmoothSubmersionOriginalGeneralFamilyLeaves
