/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionActualFamilyMonomialLeaf
import Hironaka.Resolution.HironakaSmoothSubmersionPositiveLowerHistory
/-! Genuine original positive canonical lower diagrams and full Step One
comparison at their actual monomial leaves. Complete mathematics was written
first in `Mathematics.tex`; positive inner orders and zero contact remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalPositiveFamilyLeaf
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  StepOneRegime StepOneValue StepOneValueMasked HomogenizedIdealAlong
  NonmonomialOrderLocal HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionPositiveLowerHistory
  HironakaSmoothSubmersionPositiveMemberHistory HironakaSmoothSubmersionAllBranchHistory
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaSmoothSubmersionActualFamilyMonomialLeaf
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m k : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

theorem original_positive_canonical_lower_diagram
    (hn : 0 < n) (h : IsActualTowerPullback f Q T g)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+2) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M) T)
    (s : ℕ) (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp)
    (hns : ¬ IsSpecial M T (g z)) (hl : level M T (g z) = s+1) :
    let r := regimeRun (stepRegime M (level M T (g z))) T (g z)
    let U := lowerMask M (s+1) (head T r) ((tail T r).proj (g z))
    let V := lowerMask (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
    let J := lowerMarkedM M (s+1) (head T r) ((tail T r).proj (g z))
    let J' := lowerMarkedM (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
    let L := restrict U (tail T r)
    let L' := restrict V (tail Q r)
    ∃ (hp : (tail T r).proj (g z) ∈ U) (hp' : (tail Q r).proj z ∈ V)
      (p : V → U) (q : openPreimage (tail Q r) V → openPreimage (tail T r) U),
      Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ p ∧
      markedPullback (m := m) p J = J' ∧ IsActualTowerPullback p L' L q ∧
      q (⟨z,hp'⟩ : openPreimage (tail Q r) V) = ⟨g z,hp⟩ ∧
      IsInvDomain (k+1) J ∧ IsCanonical J ((invFamily hn (k+1)).inv J) L ∧
      (⟨g z,hp⟩ : openPreimage (tail T r) U) ∈ (geoTransformAlong J L).cosupp ∧
      IsInvDomain ((m-n)+k+1) J' ∧ IsGeoTestTower J' L' ∧
      (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong J' L').cosupp := by
  dsimp only
  obtain ⟨ht,_,hcos⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn (k+1)) M hM hmax hn T hcan
  have hc := (Seq.StepOneBridge.isCanonical_iff (invFamily hn (k+1)) M hM hmax hn T).mp hcan
  have hybar : g z ∈ (geoTransformAlong (barMarked M) T).cosupp := hcos.symm ▸ hy
  let r := regimeRun (stepRegime M (level M T (g z))) T (g z)
  have hd := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical M (k := k+2)
    (invFamily hn (k+1)) hM.isWellFormed hM.one_le_d hn hmax hM.dimLE T ht hc (g z) hybar hns
  have hd' : Seq.StepOneValueMasked.LowerDataL (invFamily hn (k+1)) M (lowerMarkedM M)
      (s+1) (head T r) (tail T r) (g z) := by simpa only [r,hl] using hd
  obtain ⟨hp,hdom,hcanJ,hcosJ⟩ := hd'
  obtain ⟨a,hhead,htail,p,q,hpSmooth,_,hqcoord,hrecord,hrestr⟩ :=
    IsActualTowerPullback.exists_split_actual_positive_lower_diagram h M hM.isWellFormed ht r s z
  let U := lowerMask M (s+1) (head T r) ((tail T r).proj (g z))
  let V := lowerMask (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  let J := lowerMarkedM M (s+1) (head T r) ((tail T r).proj (g z))
  let J' := lowerMarkedM (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  let L := restrict U (tail T r)
  let L' := restrict V (tail Q r)
  change markedPullback (m := m) p J = J' at hrecord
  change IsActualTowerPullback p L' L q at hrestr
  have hheadT := ((isGeoTestTower_iff_head_tail (barMarked M) T r).mp ht).1
  have hpre := IsActualTowerPullback.all_maskA_dictionary hhead M hM.isWellFormed hheadT ((tail Q r).proj z)
  rw [← htail.proj_comm z] at hpre
  have hpre' : (V : Set (split Q r).1) = a ⁻¹' (U : Set (split T r).1) := hpre
  have hp' : (tail Q r).proj z ∈ V := by
    change (tail Q r).proj z ∈ (V : Set (split Q r).1)
    rw [hpre']
    change a ((tail Q r).proj z) ∈ U
    rw [← htail.proj_comm z]
    exact hp
  have hq : _ = (⟨g z,hp⟩ : openPreimage (tail T r) U) :=
    Subtype.ext (hqcoord (⟨z,hp'⟩ : openPreimage (tail Q r) V))
  have htJ : IsGeoTestTower J L := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn (k+1)).isInvValue hdom L hcanJ
  have hsourceDom : IsInvDomain ((m-n)+k+1) J' := by
    have hd := isInvDomain_markedPullback_submersion hpSmooth J hdom
    have hd' : IsInvDomain ((k+1)+(m-n)) J' := hrecord ▸ hd
    convert hd' using 1
    omega
  have hsourceT : IsGeoTestTower J' L' := by
    exact hrecord ▸ (IsActualTowerPullback.relative_marked_dictionary hrestr J hdom.isWellFormed htJ).1
  have hsourceCos : (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong J' L').cosupp := by
    have hc : (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈
        (geoTransformAlong (markedPullback (m := m) p J) L').cosupp := by
      rw [IsActualTowerPullback.relative_cosupport_dictionary hrestr J hdom.isWellFormed htJ]
      change _ ∈ (geoTransformAlong J L).cosupp
      rw [hq]
      exact hcosJ
    exact hrecord ▸ hc
  exact ⟨hp,hp',p,q,hpSmooth,hrecord,hrestr,hq,hdom,hcanJ,hcosJ,hsourceDom,hsourceT,hsourceCos⟩

/-- Full original Step One values at positive level and actual lower
monomial order, with all lower data derived from original target canonicity. -/
theorem original_positive_step_one_monomial_leaf
    (hn : 0 < n) (hm : 0 < m) (h : IsActualTowerPullback f Q T g)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+2) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M) T)
    (s : ℕ) (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp)
    (hns : ¬ IsSpecial M T (g z)) (hl : level M T (g z) = s+1) :
    let r := regimeRun (stepRegime M (level M T (g z))) T (g z)
    let U := lowerMask M (s+1) (head T r) ((tail T r).proj (g z))
    let J := lowerMarkedM M (s+1) (head T r) ((tail T r).proj (g z))
    let L := restrict U (tail T r)
    ∃ hp : (tail T r).proj (g z) ∈ U,
      (IsInvDomain (k+1) J ∧ IsCanonical J ((invFamily hn (k+1)).inv J) L ∧
        (⟨g z,hp⟩ : openPreimage (tail T r) U) ∈ (geoTransformAlong J L).cosupp) ∧
      (nmOrd (geoTransformAlong J L) (⟨g z,hp⟩ : openPreimage (tail T r) U) = 0 →
        Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1))
          (markedPullback (m := m) f M) Q z =
        stepDimensionMap (familyDimensionMap (m-n) (k+1))
          (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z))) := by
  dsimp only
  obtain ⟨hp,hp',p,q,_,hrecord,hrestr,hq,hdom,hcanJ,hcosJ,_,_,_⟩ :=
    original_positive_canonical_lower_diagram hn h M hM hmax hcan s z hy hns hl
  refine ⟨hp,⟨hdom,hcanJ,hcosJ⟩,?_⟩
  intro h0
  let r := regimeRun (stepRegime M (level M T (g z))) T (g z)
  let U := lowerMask M (s+1) (head T r) ((tail T r).proj (g z))
  let V := lowerMask (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  let J := lowerMarkedM M (s+1) (head T r) ((tail T r).proj (g z))
  let J' := lowerMarkedM (markedPullback (m := m) f M) (s+1) (head Q r) ((tail Q r).proj z)
  let L := restrict U (tail T r)
  let L' := restrict V (tail Q r)
  let z' : openPreimage (tail Q r) V := ⟨z,hp'⟩
  let y' : openPreimage (tail T r) U := ⟨g z,hp⟩
  have htJ : IsGeoTestTower J L := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn (k+1)).isInvValue hdom L hcanJ
  have h0' : nmOrd (geoTransformAlong J L) (q z') = 0 := by rw [hq];exact h0
  have hv := (IsActualTowerPullback.actual_family_monomial_leaf hn hm hrestr J hdom htJ z' h0').2
  rw [hrecord,hq] at hv
  have ht := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn (k+1)) M hM hmax hn T hcan).1
  have hlevel := IsActualTowerPullback.bar_level_dictionary h M hM.isWellFormed ht z
  have hrun : regimeRun
      (stepRegime (markedPullback (m := m) f M) (level (markedPullback (m := m) f M) Q z)) Q z = r := by
    rw [hlevel]
    exact IsActualTowerPullback.all_stepRegime_run h M hM.isWellFormed ht _ z
  have hns' : ¬ IsSpecial (markedPullback (m := m) f M) Q z :=
    fun hsp => hns ((IsActualTowerPullback.all_isSpecial_dictionary h M hM.isWellFormed ht z).mp hsp)
  have hs : Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1))
      (markedPullback (m := m) f M) Q z =
      toLex (s+1,((invFamily hm ((m-n)+k+1)).inv J' L' z' : WithTop (ValTy ((m-n)+k+1)))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hns',hrun,hlevel,hl,
      Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp']
  have htval : Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z) =
      toLex (s+1,((invFamily hn (k+1)).inv J L y' : WithTop (ValTy (k+1)))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hns]
    change toLex (level M T (g z), Seq.StepOneValueMasked.lowerValueL
      (invFamily hn (k+1)) M (lowerMarkedM M) (level M T (g z)) (head T r) (tail T r) (g z)) = _
    rw [hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp]
  rw [hs,htval]
  unfold stepDimensionMap
  simp only [ofLex_toLex,WithTop.map_coe]
  exact congrArg (fun v : ValTy ((m-n)+k+1) => toLex (s+1,(v : WithTop (ValTy ((m-n)+k+1))))) hv

end
end Hironaka.HironakaSmoothSubmersionOriginalPositiveFamilyLeaf
