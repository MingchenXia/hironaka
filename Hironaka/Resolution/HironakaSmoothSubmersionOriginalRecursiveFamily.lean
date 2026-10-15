/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalZeroContactLower
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalZeroFamilyHistory
/-! Entire original depth-parametric smooth family and canonical history transfer.
Complete mathematics preceded proofs in Mathematics.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalRecursiveFamily
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  StepOneRegime StepOneValue StepOneValueMasked HomogenizedIdealAlong
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail GeneralValue
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionNonmonomialHistory HironakaSmoothSubmersionAllBranchHistory
  HironakaSmoothSubmersionPositiveMemberHistory
  ContactStageKept TangentDirectionAlong HironakaSmoothSubmersionOriginalZeroContactLower
  HironakaSmoothSubmersionOriginalPositiveCurveLower
  HironakaSmoothSubmersionOriginalPositiveFamilyLeaf HironakaSmoothSubmersionOriginalGeneralFamilyLeaves
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaSmoothSubmersionOriginalCurveFamily
  HironakaSmoothSubmersionActualFamilyMonomialLeaf HironakaSmoothSubmersionOriginalZeroFamilyHistory
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m k : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

private def FamilyTransport (hn : 0 < n) (hm : 0 < m) (d : ℕ) : Prop :=
  ∀ {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
    {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D},
    IsActualTowerPullback f Q T g → ∀ (M : MarkedIdeal n X), IsInvDomain d M →
    IsCanonical M ((invFamily hn d).inv M) T →
    IsCanonical (markedPullback (m := m) f M)
      ((invFamily hm ((m-n)+d)).inv (markedPullback (m := m) f M)) Q ∧
    ∀ z : D', g z ∈ (geoTransformAlong M T).cosupp →
      (invFamily hm ((m-n)+d)).inv (markedPullback (m := m) f M) Q z =
        familyDimensionMap (m-n) d ((invFamily hn d).inv M T (g z))

private theorem actual_base_submersion (h : IsActualTowerPullback f Q T g) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f := by
  induction h with
  | refl hf => exact hf
  | step _ _ _ _ ih => exact ih

private theorem positive_step_value_of_lower_family (hn : 0 < n) (hm : 0 < m)
    (hLower : FamilyTransport.{u} hn hm (k+1))
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain (k+2) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M) T)
    (s : ℕ) (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp)
    (hns : ¬ IsSpecial M T (g z)) (hl : level M T (g z) = s+1) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M) Q z =
      stepDimensionMap (familyDimensionMap (m-n) (k+1))
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z)) := by
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
  have hv := (hLower hrestr J hdom hcanJ).2 z' hcosq
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
  have hs : Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M) Q z =
      toLex (s+1,((invFamily hm ((m-n)+k+1)).inv J' L' z' : WithTop (ValTy ((m-n)+k+1)))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hns',hrun,hlevel,hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp']
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

private theorem zero_step_value_of_current_source_canonical
    (hn : 0 < n) (hm : 0 < m)
    (hLower : FamilyTransport.{u} hn hm (k+1)) (h : IsActualTowerPullback f Q T g)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+2) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M) T)
    (hsource : IsCanonical (markedPullback (m := m) f M)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M)) Q)
    (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp)
    (hns : ¬ IsSpecial M T (g z)) (hl : level M T (g z) = 0) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M) Q z =
      stepDimensionMap (familyDimensionMap (m-n) (k+1))
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z)) := by
  obtain ⟨hp,a,V,hp',p,q,hu,_hh,_hV,_hpSmooth,hrecord,hrestr,hq,hWU,hWE,hdom,hcanJ,hcosJ,hd',_hqt,_hcos'⟩ :=
    original_zero_canonical_lower_diagram hn h M hM hmax hcan z hy hns hl
  let r := regimeRun (stepRegime M 0) T (g z)
  let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
  let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
  let w := (tangentChoice M (T.proj (g z))).2
  let J' := contactMarkedKept (markedPullback (m := m) f M) (w ∘ f) (head Q r) V
  let L := restrict U (tail T r)
  let L' := restrict V (tail Q r)
  let z' : openPreimage (tail Q r) V := ⟨z,hp'⟩
  let y' : openPreimage (tail T r) U := ⟨g z,hp⟩
  have hcommon : IsCanonical J' ((invFamily hm ((m-n)+k+1)).inv J') L' := by
    have hc := (hLower hrestr J hdom hcanJ).1
    rwa [hrecord] at hc
  have hcosq : q z' ∈ (geoTransformAlong J L).cosupp := by rw [hq];exact hcosJ
  have hv := (hLower hrestr J hdom hcanJ).2 z' hcosq
  rw [hrecord,hq] at hv
  have hf := actual_base_submersion h
  have hMs : IsInvDomain ((m-n)+k+2) (markedPullback (m := m) f M) := by
    have hd := isInvDomain_markedPullback_submersion hf M hM
    convert hd using 1
    omega
  have hmaxs : IsMaximalOrderAlong (markedPullback (m := m) f M).N
      (markedPullback (m := m) f M).ideal (markedPullback (m := m) f M).d :=
    HironakaSmoothSubmersionTangentContact.isMaximalOrderAlong_preimage hf hM.isWellFormed.isCoherent M.N M.d hmax
  obtain ⟨ht,_,_⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn (k+1)) M hM hmax hn T hcan
  have hlevel := IsActualTowerPullback.bar_level_dictionary h M hM.isWellFormed ht z
  have hrun : regimeRun
      (stepRegime (markedPullback (m := m) f M) (level (markedPullback (m := m) f M) Q z)) Q z = r := by
    rw [hlevel,hl]
    exact IsActualTowerPullback.all_stepRegime_run h M hM.isWellFormed ht 0 z
  have hns' : ¬ IsSpecial (markedPullback (m := m) f M) Q z :=
    fun hsp => hns ((IsActualTowerPullback.all_isSpecial_dictionary h M hM.isWellFormed ht z).mp hsp)
  obtain ⟨hts,_,hcoss⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M) hMs hmaxs hm Q hsource
  have hsrcCos : z ∈ (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp := by
    rw [IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed
      (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (invFamily hn (k+1)) M hM hmax hn T hcan).2.1]
    exact hy
  have hbarCos : z ∈ (geoTransformAlong (barMarked (markedPullback (m := m) f M)) Q).cosupp :=
    hcoss.symm ▸ hsrcCos
  have hsc := (Seq.StepOneBridge.isCanonical_iff (invFamily hm ((m-n)+k+1))
    (markedPullback (m := m) f M) hMs hmaxs hm Q).mp hsource
  have hD := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical
    (markedPullback (m := m) f M) (k := (m-n)+k+2) (invFamily hm ((m-n)+k+1))
    hMs.isWellFormed hMs.one_le_d hm hmaxs hMs.dimLE Q hts hsc z hbarCos hns'
  rw [hrun,hlevel,hl] at hD
  have hts' : IsGeoTestTower (barMarked (markedPullback (m := m) f M)) ((head Q r).append (tail Q r)) := by
    rwa [head_append_tail Q r]
  have hbarCos' : z ∈ (geoTransformAlong (barMarked (markedPullback (m := m) f M))
      ((head Q r).append (tail Q r))).cosupp := by rwa [head_append_tail Q r]
  have hanchor := Seq.ContactLowerValue.lowerValueL_zero_eq (invFamily hm ((m-n)+k+1))
    (markedPullback (m := m) f M) hMs.isWellFormed hMs.one_le_d (head Q r) (tail Q r)
    hts' hu V hWU hWE hd' hcommon hp' hbarCos' hD
  have hs : Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M) Q z =
      toLex (0,((invFamily hm ((m-n)+k+1)).inv J' L' z' : WithTop (ValTy ((m-n)+k+1)))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hns',hrun,hlevel,hl,hanchor]
  have htval : Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z) =
      toLex (0,((invFamily hn (k+1)).inv J L y' : WithTop (ValTy (k+1)))) := by
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hns,hl,Seq.StepOneValueMasked.lowerValueL_eq_of_mem _ _ _ hp]
  rw [hs,htval]
  unfold stepDimensionMap
  simp only [ofLex_toLex,WithTop.map_coe]
  exact congrArg (fun v : ValTy ((m-n)+k+1) => toLex (0,(v : WithTop (ValTy ((m-n)+k+1))))) hv
private theorem step_value_of_current_source_canonical
    (hn : 0 < n) (hm : 0 < m)
    (hLower : FamilyTransport.{u} hn hm (k+1)) (h : IsActualTowerPullback f Q T g)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+2) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M) T)
    (hsource : IsCanonical (markedPullback (m := m) f M)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M)) Q)
    (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M) Q z =
      stepDimensionMap (familyDimensionMap (m-n) (k+1))
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z)) := by
  by_cases hsp : IsSpecial M T (g z)
  · exact original_special_step_one_value hn hm h M hM hmax hcan z hsp
  by_cases hl : level M T (g z) = 0
  · exact zero_step_value_of_current_source_canonical hn hm hLower h M hM hmax hcan hsource z hy hsp hl
  obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero hl
  exact positive_step_value_of_lower_family hn hm hLower h M hM hmax hcan s z hy hsp hs

private theorem visible_maximum_of_whole_values
    {A B : Type*} {Λ Γ : Type*} [LinearOrder Λ] [LinearOrder Γ]
    (g : B → A) (S : Set A) (S' : Set B) (I : A → Λ) (I' : B → Γ)
    (δ : Λ → Γ) (hδ : StrictMono δ) (hS : S' = g ⁻¹' S)
    (hv : ∀ z, g z ∈ S → I' z = δ (I (g z)))
    (hvisible : (g ⁻¹' ResolutionDriver.maxLocus I S).Nonempty) :
    ResolutionDriver.maxLocus I' S' = g ⁻¹' ResolutionDriver.maxLocus I S := by
  obtain ⟨w,hw⟩ := hvisible
  change g w ∈ S ∧ ∀ x ∈ S, I x ≤ I (g w) at hw
  ext z
  change (z ∈ S' ∧ ∀ v ∈ S', I' v ≤ I' z) ↔
    (g z ∈ S ∧ ∀ x ∈ S, I x ≤ I (g z))
  rw [hS]
  constructor
  · rintro ⟨hz,hmax⟩
    refine ⟨hz,fun x hx => (hw.2 x hx).trans ?_⟩
    have hle := hmax w hw.1
    rw [hv w hw.1,hv z hz] at hle
    exact hδ.le_iff_le.mp hle
  · rintro ⟨hz,hmax⟩
    refine ⟨hz,?_⟩
    intro v hvS
    rw [hv v hvS,hv z hz]
    exact hδ.monotone (hmax (g v) hvS)

private theorem step_family_of_lower_family (hn : 0 < n) (hm : 0 < m)
    (hLower : FamilyTransport.{u} hn hm (k+1))
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain (k+2) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M) T) :
    IsCanonical (markedPullback (m := m) f M)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M)) Q ∧
    ∀ z : D', g z ∈ (geoTransformAlong M T).cosupp →
      Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M) Q z =
        stepDimensionMap (familyDimensionMap (m-n) (k+1))
          (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z)) := by
  induction h with
  | refl hf =>
    refine ⟨trivial,?_⟩
    intro z hz
    exact step_value_of_current_source_canonical hn hm hLower (.refl hf) M hM hmax hcan trivial z hz
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    obtain ⟨hc,hC⟩ := hcan
    obtain ⟨hcs,hv⟩ := ih hc
    have hcurrent : IsCanonical (markedPullback (m := m) f M)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M))
        (.step Q (g ⁻¹' C) ρ hρ) := by
      refine ⟨hcs,?_⟩
      rcases hC with hC | hC
      · left
        rw [hC,preimage_empty]
      · by_cases he : g ⁻¹' C = ∅
        · exact Or.inl he
        · have hvisible : (g ⁻¹' ResolutionDriver.maxLocus
              (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T)
              (geoTransformAlong M T).cosupp).Nonempty := by
            rw [← hC]
            exact nonempty_iff_ne_empty.mpr he
          have ht := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
            (invFamily hn (k+1)) M hM hmax hn T hc).2.1
          have hcsdict := IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed ht
          have heq := visible_maximum_of_whole_values g
            (geoTransformAlong M T).cosupp (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T)
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k+1)) (markedPullback (m := m) f M) Q)
            (stepDimensionMap (familyDimensionMap (m-n) (k+1)))
            (strictMono_stepDimensionMap (strictMono_familyDimensionMap (m-n) (k+1))) hcsdict hv hvisible
          exact Or.inr (by rw [hC,heq])
    refine ⟨hcurrent,?_⟩
    intro z hz
    exact step_value_of_current_source_canonical hn hm hLower (.step h hg hπ hρ)
      M hM hmax ⟨hc,hC⟩ hcurrent z hz
private theorem family_value_of_lower_family (hn : 0 < n) (hm : 0 < m)
    (hLower : FamilyTransport.{u} hn hm (k+1))
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain (k+2) M)
    (hcan : IsCanonical M ((invFamily hn (k+2)).inv M) T)
    (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp) :
    (invFamily hm ((m-n)+k+2)).inv (markedPullback (m := m) f M) Q z =
      familyDimensionMap (m-n) (k+2) ((invFamily hn (k+2)).inv M T (g z)) := by
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn (k+2)).isInvValue hM T hcan
  by_cases hzero : nmOrd (geoTransformAlong M T) (g z) = 0
  · exact (IsActualTowerPullback.actual_family_monomial_leaf hn hm h M hM ht z hzero).2
  let o := nmOrd (geoTransformAlong M T) (g z)
  have ho : 0 < o := Nat.pos_of_ne_zero hzero
  obtain ⟨hp,hp',p,q,hrecord,hrestr,hq,hdom,hmax,hcanP,hcosP,_,_,_⟩ :=
    original_general_canonical_companion_diagram hn h M hM hcan o ho z hy rfl
  let r := regimeRun (OrdRegime M o) T (g z)
  let U := ordMask (geoTransformAlong M (head T r)) o
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q r)) o
  let P := compAt M o (head T r)
  let P' := compAt (markedPullback (m := m) f M) o (head Q r)
  let L := restrict U (tail T r)
  let L' := restrict V (tail Q r)
  let z' : openPreimage (tail Q r) V := ⟨z,hp'⟩
  have hcos' : q z' ∈ (geoTransformAlong P L).cosupp := by rw [hq];exact hcosP
  have hv := (step_family_of_lower_family hn hm hLower hrestr P hdom hmax hcanP).2 z' hcos'
  rw [hrecord,hq] at hv
  have hord' : nmOrd (geoTransformAlong (markedPullback (m := m) f M) Q) z = o :=
    IsActualTowerPullback.orderAt_dictionary hn h M hM ht z
  have hrun : regimeRun (OrdRegime (markedPullback (m := m) f M) o) Q z = r :=
    IsActualTowerPullback.fixed_order_regime_run hn h M hM ht o z
  change genInv (fun {A} J {B} S y => Seq.StepOneValueMasked.stepOneInvM (X := A)
      (invFamily hm ((m-n)+k+1)) J (Y := B) S y) (markedPullback (m := m) f M) Q z =
    generalDimensionMap (m-n) (stepDimensionMap (familyDimensionMap (m-n) (k+1)))
      (genInv (fun {A} J {B} S y => Seq.StepOneValueMasked.stepOneInvM (X := A)
        (invFamily hn (k+1)) J (Y := B) S y) M T (g z))
  unfold generalDimensionMap genInv genSecond
  rw [hord',show nmOrd (geoTransformAlong M T) (g z) = o from rfl,
    if_neg (ne_of_gt ho),hrun,genLowerValue_eq_of_mem _ _ hp',genLowerValue_eq_of_mem _ _ hp]
  simp only [if_neg (ne_of_gt ho),ofLex_toLex,Sum.map_inr,WithTop.map_coe]
  exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy ((m-n)+k+1)) =>
    toLex (o,toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy ((m-n)+k+1))))))) hv

private theorem family_canonical_of_lower_family (hn : 0 < n) (hm : 0 < m)
    (hLower : FamilyTransport.{u} hn hm (k+1))
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain (k+2) M)
    (hcan : IsCanonical M ((invFamily hn (k+2)).inv M) T) :
    IsCanonical (markedPullback (m := m) f M)
      ((invFamily hm ((m-n)+k+2)).inv (markedPullback (m := m) f M)) Q := by
  induction h with
  | refl => trivial
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    obtain ⟨hc,hC⟩ := hcan
    refine ⟨ih hc,?_⟩
    rcases hC with hC | hC
    · left
      rw [hC,preimage_empty]
    · by_cases he : g ⁻¹' C = ∅
      · exact Or.inl he
      · have hvisible : (g ⁻¹' ResolutionDriver.maxLocus ((invFamily hn (k+2)).inv M T)
            (geoTransformAlong M T).cosupp).Nonempty := by
          rw [← hC]
          exact nonempty_iff_ne_empty.mpr he
        have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
          (invFamily hn (k+2)).isInvValue hM T hc
        have hcsdict := IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed ht
        have heq := visible_maximum_of_whole_values g
          (geoTransformAlong M T).cosupp (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp
          ((invFamily hn (k+2)).inv M T) ((invFamily hm ((m-n)+k+2)).inv (markedPullback (m := m) f M) Q)
          (familyDimensionMap (m-n) (k+2)) (strictMono_familyDimensionMap (m-n) (k+2)) hcsdict
          (fun z hz => family_value_of_lower_family hn hm hLower h M hM hc z hz) hvisible
        exact Or.inr (by rw [hC,heq])

private theorem family_transport_all_depths (hn : 0 < n) (hm : 0 < m) :
    ∀ d : ℕ, FamilyTransport.{u} hn hm d := by
  intro d
  induction d with
  | zero =>
    intro X D Y D' f g Q T h M hM hcan
    obtain ⟨_hd,_hte,_hqe,hsource,hzero,_hsourcezero,_hres,_hsourceres,_hvalue⟩ :=
      original_zero_actual_family_history hn hm h M hM hcan
    refine ⟨hsource,?_⟩
    intro z hz
    rw [hzero] at hz
    exact False.elim hz
  | succ d ih =>
    cases d with
    | zero =>
      intro X D Y D' f g Q T h M hM hcan
      exact ⟨IsActualTowerPullback.original_curve_family_canonical hn hm h M hM hcan,
        fun z hz => IsActualTowerPullback.actual_curve_family_value hn hm h M hM hcan z hz⟩
    | succ k =>
      intro X D Y D' f g Q T h M hM hcan
      exact ⟨family_canonical_of_lower_family hn hm ih h M hM hcan,
        fun z hz => family_value_of_lower_family hn hm ih h M hM hcan z hz⟩

theorem IsActualTowerPullback.original_recursive_family (hn : 0 < n) (hm : 0 < m)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hcan : IsCanonical M ((invFamily hn k).inv M) T) :
    IsCanonical (markedPullback (m := m) f M)
      ((invFamily hm ((m-n)+k)).inv (markedPullback (m := m) f M)) Q ∧
    ∀ z : D', g z ∈ (geoTransformAlong M T).cosupp →
      (invFamily hm ((m-n)+k)).inv (markedPullback (m := m) f M) Q z =
        familyDimensionMap (m-n) k ((invFamily hn k).inv M T (g z)) :=
  family_transport_all_depths hn hm k h M hM hcan

theorem exists_original_smooth_recursive_family_resolution [CompactSpace X]
    (hn : 0 < n) (hm : 0 < m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) :
    ∃ (D : CMfd.{u} n) (T : BlowupTower X D)
      (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsCanonical M ((invFamily hn k).inv M) T ∧ IsGeoResolution M T ∧
      IsActualTowerPullback f Q T g ∧ Q.length = T.length ∧
      IsInvDomain ((m-n)+k) (markedPullback (m := m) f M) ∧
      IsCanonical (markedPullback (m := m) f M)
        ((invFamily hm ((m-n)+k)).inv (markedPullback (m := m) f M)) Q ∧
      IsGeoResolution (markedPullback (m := m) f M) Q ∧
      geoTransformAlong (markedPullback (m := m) f M) Q = markedPullback (m := m) g (geoTransformAlong M T) ∧
      (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp = g ⁻¹' (geoTransformAlong M T).cosupp := by
  obtain ⟨D,T,hcan,hres⟩ := ResolutionInvariantSeq.exists_isGeoResolution_isCanonical (invFamily hn k) hM
  obtain ⟨D',Q,g,h⟩ := exists_actual_tower hf T
  have hd : IsInvDomain ((m-n)+k) (markedPullback (m := m) f M) := by
    simpa only [Nat.add_comm] using isInvDomain_markedPullback_submersion hf M hM
  obtain ⟨hqt,hrecord⟩ := IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hres.1
  have hcs := IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed hres.1
  have hqr : IsGeoResolution (markedPullback (m := m) f M) Q := by
    refine ⟨hqt,?_⟩
    rw [hcs,hres.2,preimage_empty]
  exact ⟨D,T,D',Q,g,hcan,hres,h,h.length_eq,hd,
    (IsActualTowerPullback.original_recursive_family hn hm h M hM hcan).1,hqr,hrecord,hcs⟩
end
end Hironaka.HironakaSmoothSubmersionOriginalRecursiveFamily
