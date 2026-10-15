/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalZeroCommonCurveValues
import Hironaka.Resolution.HironakaOriginalComputedZeroMaskCurveValues
import Hironaka.Resolution.HironakaOriginalZeroContactCurveFullValues
/-! Genuine computed OWN source zero-mask full values from original ANYTEST
and actual equal-dimensional smooth basechange. COMMON is compared, not renamed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalZeroOwnCurveValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen RelativePrincipalizationSpan
  CoefficientIdealRestriction CanonicalCentres HomogenizedIdealAlong HomogenizedIdealAlongTower
  HomogenizedGlueingTower ContactStageKept StepOneValue StepOneLowerDomain StepOneValueMasked StepOneRegime
  TangentDirectionAlong HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionRelativeOrder HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionAllBranchHistory
  HironakaSmoothSubmersionPositiveMemberHistory HironakaSmoothSubmersionTangentContact
  HironakaOriginalActualSmoothZeroMaskHistories HironakaOriginalIndependentSmoothContactChoices
  HironakaOriginalZeroContactCurveFullValues HironakaOriginalComputedZeroMaskCurveValues
  HironakaOriginalZeroCommonCurveValues
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y D D' : CMfd.{u} n}

/-- Actual intersection geometry supplies BOTH cosupport and full values
on two real presentation opens; no canonicality or comparison window input. -/
theorem original_curve_any_test_full_values_two_opens (hn : 0<n)
    (P : MarkedIdeal n X) (hP : P.ideal.IsCoherent) (U V : Opens X)
    (hU : IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : U → X) P))
    (hV : IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : V → X) P))
    (T : BlowupTower X D)
    (hTU : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) P) (restrict U T))
    (hTV : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → X) P) (restrict V T))
    (z : D) (hzU : T.proj z ∈ U) (hzV : T.proj z ∈ V)
    (hz : (⟨z,hzU⟩ : openPreimage T U) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) P) (restrict U T)).cosupp) :
    (⟨z,hzV⟩ : openPreimage T V) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) P) (restrict V T)).cosupp ∧
    ∀ k : ℕ,(invFamily hn (k+1)).inv (MarkedIdeal.pullback (Subtype.val : U → X) P) (restrict U T) ⟨z,hzU⟩=
      (invFamily hn (k+1)).inv (MarkedIdeal.pullback (Subtype.val : V → X) P) (restrict V T) ⟨z,hzV⟩ := by
  have hA := original_curve_any_test_full_value_nested_opens hn P hP (show U⊓V≤U from inf_le_left) hU T hTU
  have hB := original_curve_any_test_full_value_nested_opens hn P hP (show U⊓V≤V from inf_le_right) hV T hTV
  let p : openPreimage T (U⊓V) := ⟨z,⟨hzU,hzV⟩⟩
  have hp := (hA.2.2 p).1.mpr hz
  refine ⟨(hB.2.2 p).1.mp hp,fun k => ?_⟩
  exact ((hA.2.2 p).2 hp k).symm.trans ((hB.2.2 p).2 hp k)

private theorem actual_zero_own_values {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    {Q : BlowupTower Y D'} {T : BlowupTower X D} {g : D' → D}
    (hCart : IsActualTowerPullback f Q T g) (hT : IsGeoTestTower M T)
    (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp)
    (hns : ¬IsSpecial M T (g z)) (hl : level M T (g z)=0) :
    let K := markedPullback (m := n) f M
    let r := regimeRun (stepRegime M 0) T (g z)
    let r' := regimeRun (stepRegime K 0) Q z
    let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
    let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
    let W := lowerMask K 0 (head Q r') ((tail Q r').proj z)
    let JOwn := lowerMarkedM K 0 (head Q r') ((tail Q r').proj z)
    ∃ (hp : (tail T r).proj (g z) ∈ U) (hpOwn : (tail Q r').proj z ∈ W),
      IsInvDomain 1 J ∧ IsGeoTestTower J (restrict U (tail T r)) ∧
      IsInvDomain 1 JOwn ∧ IsGeoTestTower JOwn (restrict W (tail Q r')) ∧
      (⟨z,hpOwn⟩ : openPreimage (tail Q r') W) ∈ (geoTransformAlong JOwn (restrict W (tail Q r'))).cosupp ∧
      ∀ k : ℕ,(invFamily hn (k+1)).inv JOwn (restrict W (tail Q r')) ⟨z,hpOwn⟩=
        (invFamily hn (k+1)).inv J (restrict U (tail T r)) ⟨g z,hp⟩ := by
  let K := markedPullback (m := n) f M
  let r := regimeRun (stepRegime M 0) T (g z)
  let H := head Q r
  let S := tail Q r
  let W := lowerMask K 0 H (S.proj z)
  let JOwn := lowerMarkedM K 0 H (S.proj z)
  let u := (tangentChoice M (T.proj (g z))).2 ∘ f
  let v := (tangentChoice K (Q.proj z)).2
  have hK : IsInvDomain 2 K := by
    simpa only [Nat.sub_self,Nat.add_zero] using isInvDomain_markedPullback_submersion hf M hM
  have hMaxK : IsMaximalOrderAlong K.N K.ideal K.d :=
    isMaximalOrderAlong_preimage hf hM.isWellFormed.isCoherent M.N M.d hmax
  obtain ⟨hQ,_hCurrent⟩ := IsActualTowerPullback.relative_marked_dictionary hCart M hM.isWellFormed hT
  have hzK : z ∈ (geoTransformAlong K Q).cosupp := by
    rw [IsActualTowerPullback.relative_cosupport_dictionary hCart M hM.isWellFormed hT]
    exact hy
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 T).1.mpr hT
  have hlK : level K Q z=0 := (IsActualTowerPullback.bar_level_dictionary hCart M hM.isWellFormed hBar z).trans hl
  have hnsK : ¬IsSpecial K Q z := fun hs =>
    hns ((IsActualTowerPullback.all_isSpecial_dictionary hCart M hM.isWellFormed hBar z).mp hs)
  have hRun : regimeRun (stepRegime K 0) Q z=r :=
    IsActualTowerPullback.all_stepRegime_run hCart M hM.isWellFormed hBar 0 z
  dsimp only
  rw [hRun]
  have hOwnData := actual_original_test_zero_mask_history (k := 0) hn K hK hMaxK Q hQ z hzK hnsK hlK
  rw [hRun] at hOwnData
  obtain ⟨hpOwn,hOwnD,hOwnT,_hOwnCos,hOwnPoint,_hOwnNext⟩ := hOwnData
  obtain ⟨hp,_a,V,hpV,_p,_q,_hh,_hV,_hpSmooth,_hRecord,_hR,_hPoint,hJ,hJT,_hyJ,hCommonD,hCommonT,_hCommonCos,hCommonPoint,hCommonValue⟩ :=
    actual_original_zero_common_curve_full_values hn hCart M hM hmax hT z hy hns hl
  let JCommon := contactMarkedKept K u H V
  change IsInvDomain 1 JCommon at hCommonD
  change IsGeoTestTower JCommon (restrict V S) at hCommonT
  change (⟨z,hpV⟩ : openPreimage S V) ∈ (geoTransformAlong JCommon (restrict V S)).cosupp at hCommonPoint
  have hBase : T.proj (g z)=f (Q.proj z) := hCart.proj_comm z
  have hBaseQ : H.proj (S.proj z)=Q.proj z := (congrFun (proj_eq_comp Q r) z).symm
  have hfx : f (Q.proj z) ∈ M.cosupp := hBase ▸
    proj_mem_cosupp_of_mem_cosupp hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hT hy
  have hxK : Q.proj z ∈ K.cosupp :=
    proj_mem_cosupp_of_mem_cosupp hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent Q hQ hzK
  obtain ⟨U₀,_hU₀,hfxU₀,V₀,_hV₀,hxV₀,_hu₀,hPull,hv₀,_hGlue⟩ :=
    exists_original_smooth_independent_contact_glueing hf M hM hmax (Q.proj z) hfx
  let W₀ : Opens Y := ⟨f ⁻¹' (U₀ : Set X),U₀.isOpen.preimage hf.contMDiff.continuous⟩
  have hPullU : IsTangentDirectionAlong K.N K.ideal K.d W₀ u := by
    dsimp only [u]
    rw [hBase]
    exact hPull
  obtain ⟨O,hxO,hCompare⟩ := exists_original_zero_contact_curve_full_values hn K hK hMaxK
    (Q.proj z) hxK W₀ V₀ hPullU hfxU₀ hv₀ hxV₀
  have heK := coeff_homAlong_wEquiv K hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d
  have hBarQ : IsGeoTestTower (barMarked K) Q := (heK.2 Q).1.mpr hQ
  have hzBar : z ∈ (geoTransformAlong (barMarked K) Q).cosupp := by rw [(heK.2 Q).2 hBarQ];exact hzK
  obtain ⟨hReg,_hHeadCos⟩ := stepRegime_and_mem_cosupp_head K hK.isWellFormed Q hBarQ hzBar hnsK
  rw [hlK,hRun] at hReg
  have hFull : IsGeoTestTower K (H.append S) := by rw [head_append_tail];exact hQ
  have hzFull : z ∈ (geoTransformAlong K (H.append S)).cosupp := by rw [head_append_tail];exact hzK
  have hzO : H.proj (S.proj z) ∈ O := by rw [hBaseQ];exact hxO
  obtain ⟨Vu,Vv,hzu,hzv,_ψ,_ξ,_hVuMask,hVvMask,_hIso,_hFix,hAD,_hBD,_hParents,hAT,_hBT,hLocalValue⟩ :=
    hCompare H S hFull z hzFull hReg.2 hReg.1 hzO
  let A := contactMarkedKept K u H Vu
  let B := contactMarkedKept K v H Vv
  have hHead := ((isGeoTestTower_iff_head_tail (barMarked K) Q r).mp hBarQ).1
  let Pu := withN (coeffMarkedAlong (geoTransformAlong (barMarked K) H)) (strictAlong H (K.N ∩ {x | u x=0}))
  let Pv := withN (coeffMarkedAlong (geoTransformAlong (barMarked K) H)) (strictAlong H (K.N ∩ {x | v x=0}))
  have hPu : Pu.ideal.IsCoherent := isCoherent_restrictedCoeff K hK.isWellFormed.isCoherent hK.isWellFormed.isClosedSubmanifold_N u H hHead
  have hPv : Pv.ideal.IsCoherent := isCoherent_restrictedCoeff K hK.isWellFormed.isCoherent hK.isWellFormed.isClosedSubmanifold_N v H hHead
  have hOwnRecord : JOwn=contactMarkedKept K v H W := by
    change contactMarkedKept K (tangentChoice K (H.proj (S.proj z))).2 H W=_
    rw [hBaseQ]
  have hOwnD' := hOwnD
  have hOwnT' := hOwnT
  have hOwnPoint' := hOwnPoint
  change IsInvDomain 1 JOwn at hOwnD'
  change IsGeoTestTower JOwn (restrict W S) at hOwnT'
  change (⟨z,hpOwn⟩ : openPreimage S W) ∈ (geoTransformAlong JOwn (restrict W S)).cosupp at hOwnPoint'
  rw [hOwnRecord] at hOwnD' hOwnT' hOwnPoint'
  have hOwnSmall := original_curve_any_test_full_value_nested_opens hn Pv hPv hVvMask hOwnD' S hOwnT'
  have hOwnPoints := hOwnSmall.2.2 (⟨z,hzv⟩ : openPreimage S Vv)
  have hBPoint := hOwnPoints.1.mpr hOwnPoint'
  have hCommonLocal := original_curve_any_test_full_values_two_opens hn Pu hPu V Vu hCommonD hAD S hCommonT hAT
    z hpV hzu hCommonPoint
  refine ⟨hp,hpOwn,hJ,hJT,hOwnD,hOwnT,hOwnPoint,fun k => ?_⟩
  have hLocal : (invFamily hn (k+1)).inv B (restrict Vv S) ⟨z,hzv⟩=
      (invFamily hn (k+1)).inv A (restrict Vu S) ⟨z,hzu⟩ := hLocalValue k
  have hOwn := hOwnPoints.2 hBPoint k
  have hOwnLarge : (invFamily hn (k+1)).inv JOwn (restrict W S) ⟨z,hpOwn⟩=
      (invFamily hn (k+1)).inv B (restrict Vv S) ⟨z,hzv⟩ := by
    rw [hOwnRecord]
    exact hOwn.symm
  exact hOwnLarge.trans (hLocal.trans ((hCommonLocal.2 k).symm.trans (hCommonValue k)))

/-- ONLY original data construct ONE actual source history before the ACTUAL
independently computed OWN zero-mask full values at EVERY positive depth. -/
theorem exists_original_zero_own_curve_values {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    ∃ (D' : CMfd.{u} n) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧ IsGeoTestTower (markedPullback (m := n) f M) Q ∧
      ∀ z : D',g z ∈ (geoTransformAlong M T).cosupp → ¬IsSpecial M T (g z) → level M T (g z)=0 →
        let K := markedPullback (m := n) f M
        let r := regimeRun (stepRegime M 0) T (g z)
        let r' := regimeRun (stepRegime K 0) Q z
        let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
        let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
        let W := lowerMask K 0 (head Q r') ((tail Q r').proj z)
        let JOwn := lowerMarkedM K 0 (head Q r') ((tail Q r').proj z)
        ∃ (hp : (tail T r).proj (g z) ∈ U) (hpOwn : (tail Q r').proj z ∈ W),
          IsInvDomain 1 J ∧ IsGeoTestTower J (restrict U (tail T r)) ∧
          IsInvDomain 1 JOwn ∧ IsGeoTestTower JOwn (restrict W (tail Q r')) ∧
          (⟨z,hpOwn⟩ : openPreimage (tail Q r') W) ∈ (geoTransformAlong JOwn (restrict W (tail Q r'))).cosupp ∧
          ∀ k : ℕ,(invFamily hn (k+1)).inv JOwn (restrict W (tail Q r')) ⟨z,hpOwn⟩=
            (invFamily hn (k+1)).inv J (restrict U (tail T r)) ⟨g z,hp⟩ := by
  obtain ⟨D',Q,g,h,_hg,_hLen,_hSquare,hQ,_hCurrent,_hWF,_hCos,_hHeads⟩ :=
    exists_actual_relative_marked_tower hf M hM.isWellFormed T hT
  exact ⟨D',Q,g,h,hQ,fun z hy hns hl => actual_zero_own_values hf hn M hM hmax h hT z hy hns hl⟩

end
end Hironaka.HironakaOriginalZeroOwnCurveValues
