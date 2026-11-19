/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalRunCompanionSpecialSmooth
/-! Original LARGE GENERAL values from genuine common-source curve models.
No companion TEST or canonical-only locality is inferred. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalZeroOwnLargeSmoothValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MaxLocusLocal CanonicalCentres
  HironakaOriginalRunCompanionSpecialSmooth HironakaOriginalZeroOwnSmallSmoothValues
  HironakaOriginalSourceChoiceCartesian HironakaOriginalUntestedCurveSmoothValues
  HironakaOriginalUntestedMemberCurveFullValues HironakaOriginalUntestedControlledSmoothPullback
  HironakaOriginalUntestedCompanionSmoothPullback HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionCanonicalValueDimensionShift
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionAllBranchHistory HironakaSmoothSubmersionPositiveMemberHistory
  HironakaOriginalActualSmoothZeroMaskHistories HironakaSmoothSubmersionTangentContact
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneLowerDomain StepOneRegime
  StepOneValueMasked
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  GeneralValue GeneralCompare GeneralCanonicalTail CompanionRebase CompanionReductionAlong
  InvDomainTowerAlong
open ResolutionInvariantSpec (IsInvDomain)
variable {n m b : ℕ} {X D : CMfd.{u} n} {Y D' A B : CMfd.{u} m}

theorem smaller_open_cartesian {U V : Opens Y} (hVU : V≤U) (Q : BlowupTower Y D') :
    IsActualTowerPullback (fun z : V => (⟨z.val,hVU z.property⟩ : U))
      (restrict V Q) (restrict U Q)
      (fun z : openPreimage Q V => (⟨z.val,hVU z.property⟩ : openPreimage Q U)) := by
  have hNested := open_inclusion_actual_tower (nestedOpens U V) (restrict U Q)
  have hIso := isTowerIso_restrict_nestedOpens (n := m) hVU Q
  exact HironakaOriginalSourceChoiceCartesian.IsActualTowerPullback.source_isomorphism hNested hIso.symm

private theorem dimensionValue_zero (v : WithBot MonomialInvariant.Val) : dimensionValue 0 v=v := by
  have hKey : dimensionKey 0=id := by funext w;simp [dimensionKey]
  simp [dimensionValue,hKey]

/-- Real common-source geometry, not a value certificate: the small actual
history is Cartesian over both genuine original TESTs. -/
theorem curve_model_full_value_via_same_ambient_cartesian (hn : 0<n) (hm : 0<m) (k : ℕ)
    {i : A → Y} {j : B → D'} {φ : A → X} {η : B → D}
    {S : BlowupTower A B} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (hLarge : IsActualTowerPullback i S Q j) (hCurve : IsActualTowerPullback φ S T η)
    (P : MarkedIdeal m Y) (hP : IsInvDomain b P) (hQ : IsGeoTestTower P Q)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M) (hT : IsGeoTestTower M T)
    (hInit : markedPullback (m := m) φ M=markedPullback (m := m) i P)
    (z : B) (hy : η z ∈ (geoTransformAlong M T).cosupp) :
    (invFamily hm ((m-n)+k+1)).inv P Q (j z)=
      familyDimensionMap (m-n) (k+1) ((invFamily hn (k+1)).inv M T (η z)) := by
  have hPM : ∀ {Z : CMfd.{u} m} (R : BlowupTower Y Z),IsGeoTestTower P R →
      IsInvDomain b (geoTransformAlong P R) := fun R hR => isInvDomain_geoTransformAlong hP R hR
  have hMM : ∀ {Z : CMfd.{u} n} (R : BlowupTower X Z),IsGeoTestTower M R →
      IsInvDomain 1 (geoTransformAlong M R) := fun R hR => isInvDomain_geoTransformAlong hM R hR
  have hWholeLarge := (IsActualTowerPullback.modeled_controlled_dictionary hLarge P P
    (fun R hR => (hPM R hR).isWellFormed) hQ).1
  have hWholeCurve := (IsActualTowerPullback.modeled_controlled_dictionary hCurve M M
    (fun R hR => (hMM R hR).isWellFormed) hT).1
  have hyLarge : j z ∈ (geoTransformAlong P Q).cosupp := by
    have hySmall := (IsActualTowerPullback.modeled_controlled_dictionary hCurve M M
      (fun R hR => (hMM R hR).isWellFormed) hT).2
    have hyS : z ∈ (geoTransformAlong (markedPullback (m := m) φ M) S).cosupp := by rw [hySmall];exact hy
    rw [hInit,(IsActualTowerPullback.modeled_controlled_dictionary hLarge P P
      (fun R hR => (hPM R hR).isWellFormed) hQ).2] at hyS
    exact hyS
  have hOrderCurve := IsActualTowerPullback.modeled_orderAt_dictionary hn hCurve M M hMM hT z
  have hOrderLarge := IsActualTowerPullback.modeled_orderAt_dictionary hm hLarge P P hPM hQ z
  change nmOrd (geoTransformAlong (markedPullback (m := m) φ M) S) z=nmOrd (geoTransformAlong M T) (η z) at hOrderCurve
  change nmOrd (geoTransformAlong (markedPullback (m := m) i P) S) z=nmOrd (geoTransformAlong P Q) (j z) at hOrderLarge
  rw [hInit] at hOrderCurve
  have hOrder := hOrderLarge.symm.trans hOrderCurve
  by_cases hz : nmOrd (geoTransformAlong M T) (η z)=0
  · have hPzero := hOrder.trans hz
    have hcP := hPM Q hQ
    have hcM := hMM T hT
    have hGammaLarge : MonomialCaseAlong.gammaAlong m (geoTransformAlong (markedPullback (m := m) i P) S).N
        (geoTransformAlong (markedPullback (m := m) i P) S).ideal
        (geoTransformAlong (markedPullback (m := m) i P) S).E
        (geoTransformAlong (markedPullback (m := m) i P) S).d z=
        MonomialCaseAlong.gammaAlong m (geoTransformAlong P Q).N (geoTransformAlong P Q).ideal
          (geoTransformAlong P Q).E (geoTransformAlong P Q).d (j z) := by
      rw [hWholeLarge]
      have hg := gammaAlong_preimage_dimension_shift hLarge.isSubmersion hcP.isWellFormed.isCoherent
        (geoTransformAlong P Q).N (geoTransformAlong P Q).E hcP.isWellFormed.isSNCDivisor
        (geoTransformAlong P Q).d z
      rw [Nat.sub_self,dimensionValue_zero] at hg
      exact hg
    have hGammaCurve : MonomialCaseAlong.gammaAlong m (geoTransformAlong (markedPullback (m := m) i P) S).N
        (geoTransformAlong (markedPullback (m := m) i P) S).ideal
        (geoTransformAlong (markedPullback (m := m) i P) S).E
        (geoTransformAlong (markedPullback (m := m) i P) S).d z=
        dimensionValue (m-n) (MonomialCaseAlong.gammaAlong n (geoTransformAlong M T).N
          (geoTransformAlong M T).ideal (geoTransformAlong M T).E (geoTransformAlong M T).d (η z)) := by
      rw [←hInit,hWholeCurve]
      exact gammaAlong_preimage_dimension_shift hCurve.isSubmersion hcM.isWellFormed.isCoherent
        _ _ hcM.isWellFormed.isSNCDivisor _ z
    have hGamma := hGammaLarge.symm.trans hGammaCurve
    change genInv (fun {A} J {B} R y =>
        Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hm ((m-n)+k)) J (Y := B) R y) P Q (j z)=
      familyDimensionMap (m-n) (k+1) (genInv (fun {A} J {B} R y =>
        Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn k) J (Y := B) R y) M T (η z))
    unfold familyDimensionMap generalDimensionMap genInv genSecond
    rw [hPzero,hz]
    simp only [ite_true,ofLex_toLex,Sum.map_inl]
    rw [hGamma]
  · have hpos : 0<nmOrd (geoTransformAlong M T) (η z) := Nat.pos_of_ne_zero hz
    let q := nmOrd (geoTransformAlong M T) (η z)
    let r := regimeRun (OrdRegime M q) T (η z)
    have hRunCurve := IsActualTowerPullback.modeled_fixed_order_run hn hCurve M M hMM hT q z
    rw [hInit] at hRunCurve
    have hRunLarge := IsActualTowerPullback.modeled_fixed_order_run hm hLarge P P hPM hQ q z
    have hRun : regimeRun (OrdRegime P q) Q (j z)=r := hRunLarge.symm.trans hRunCurve
    have hDictionary := original_run_companion_special_level hm hLarge P hP hQ z hyLarge
      (show 0<nmOrd (geoTransformAlong P Q) (j z) from hOrder ▸ hpos)
    dsimp only at hDictionary
    rw [hOrder,hRun] at hDictionary
    obtain ⟨hpLarge,_hpSmall,hSpecial,hLevel⟩ := hDictionary
    have hModelData := original_curve_smooth_run_special hn hm hCurve M hM hT z hy hpos
    dsimp only at hModelData
    rw [hInit] at hModelData
    obtain ⟨_hpModel,hsModel,hlModel,_hAllModelLeaves⟩ := hModelData
    have hs := hSpecial.mp hsModel
    have hl := hLevel.symm.trans hlModel
    have hLeaf : Seq.StepOneValueMasked.stepOneInvM (invFamily hm ((m-n)+k))
        (compAt P q (head Q r)) (restrict (ordMask (geoTransformAlong P (head Q r)) q) (tail Q r))
        (⟨j z,hpLarge⟩ : openPreimage (tail Q r) (ordMask (geoTransformAlong P (head Q r)) q))=toLex (0,⊤) := by
      unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
      rw [if_pos hs,hl]
    have hLargeValue : (invFamily hm ((m-n)+k+1)).inv P Q (j z)=
        toLex (q,toLex (Sum.inr ((toLex (0,(⊤ : WithTop (ValTy ((m-n)+k)))) :
          ℕ ×ₗ WithTop (ValTy ((m-n)+k))) : WithTop (ℕ ×ₗ WithTop (ValTy ((m-n)+k)))))) := by
      change genInv (fun {A} J {B} R y =>
        Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hm ((m-n)+k)) J (Y := B) R y) P Q (j z)=_
      rw [genInv_of_nmOrd_ne_zero _ _ Q hOrder hz,hRun,genLowerValue_eq_of_mem _ _ hpLarge,hLeaf]
    rw [hLargeValue,modeled_curve_full_value_formula hn k M M hMM T hT (η z) hy,if_neg hz]
    simp only [familyDimensionMap,generalDimensionMap,stepDimensionMap,ofLex_toLex,
      Sum.map_inr,WithTop.map_coe,WithTop.map_top]
    rfl


/-- ONLY original upper DOMAIN2 and actual smooth data supply the independent
OWN LARGE lower TEST, point and full values internally. -/
theorem exists_original_zero_own_large_smooth_values {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧ IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      ∀ (z : D'),g z ∈ (geoTransformAlong M T).cosupp → ¬IsSpecial M T (g z) → level M T (g z)=0 →
        let K := markedPullback (m := m) f M
        let r := regimeRun (stepRegime M 0) T (g z)
        let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
        let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
        let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
        let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
        ∃ (hp : (tail T r).proj (g z) ∈ U) (hpOwn : (tail Q r).proj z ∈ W),
          ∀ k : ℕ,(invFamily hm ((m-n)+k+1)).inv JOwn (restrict W (tail Q r)) ⟨z,hpOwn⟩=
            familyDimensionMap (m-n) (k+1) ((invFamily hn (k+1)).inv J
              (restrict U (tail T r)) ⟨g z,hp⟩) := by
  obtain ⟨D',Q,g,hCart,hQ,hSmall⟩ := exists_original_zero_own_small_smooth_values hf hn hm M hM hmax T hT
  refine ⟨D',Q,g,hCart,hQ,?_⟩
  intro z hy hns hl
  let K := markedPullback (m := m) f M
  let r := regimeRun (stepRegime M 0) T (g z)
  let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
  let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
  let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
  let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
  obtain ⟨hp,Vv,hVvW,hzv,p,q,hCurve,hRecord,hEndpoint,_hSmallTest,_hzSmall,_hSmallValues⟩ := hSmall z hy hns hl
  obtain ⟨_hpTarget,hJ,hJT,_hJWhole,hJP,_hJCurrent⟩ :=
    actual_original_test_zero_mask_history hn M hM hmax T hT (g z) hy hns hl
  have hK : IsInvDomain ((m-n)+2) K := by
    convert isInvDomain_markedPullback_submersion hf M hM using 1
    omega
  have hMaxK : IsMaximalOrderAlong K.N K.ideal K.d :=
    isMaximalOrderAlong_preimage hf hM.isWellFormed.isCoherent M.N M.d hmax
  have heM := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (heM.2 T).1.mpr hT
  have hzK : z ∈ (geoTransformAlong K Q).cosupp := by
    rw [IsActualTowerPullback.relative_cosupport_dictionary hCart M hM.isWellFormed hT]
    exact hy
  have hlK : level K Q z=0 :=
    (IsActualTowerPullback.bar_level_dictionary hCart M hM.isWellFormed hBar z).trans hl
  have hnsK : ¬IsSpecial K Q z := fun hs =>
    hns ((IsActualTowerPullback.all_isSpecial_dictionary hCart M hM.isWellFormed hBar z).mp hs)
  have hRun : regimeRun (stepRegime K 0) Q z=r :=
    IsActualTowerPullback.all_stepRegime_run hCart M hM.isWellFormed hBar 0 z
  have hOwn := actual_original_test_zero_mask_history hm K hK hMaxK Q hQ z hzK hnsK hlK
  rw [hRun] at hOwn
  obtain ⟨hpOwn,hOwnD,hOwnT,_hOwnWhole,_hzOwn,_hOwnCurrent⟩ := hOwn
  have hSmallLarge := smaller_open_cartesian (Y := (split Q r).1) hVvW (tail Q r)
  refine ⟨hp,hpOwn,fun k => ?_⟩
  have hyCurve : q (⟨z,hzv⟩ : openPreimage (tail Q r) Vv) ∈
      (geoTransformAlong J (restrict U (tail T r))).cosupp := by
    rw [hEndpoint]
    exact hJP
  have hValue := curve_model_full_value_via_same_ambient_cartesian
    (X := CMfd.of (n := n) U) (Y := CMfd.of (n := m) W)
    hn hm k hSmallLarge hCurve JOwn hOwnD hOwnT J hJ hJT hRecord ⟨z,hzv⟩ hyCurve
  rw [hEndpoint] at hValue
  exact hValue

end
end Hironaka.HironakaOriginalZeroOwnLargeSmoothValues
