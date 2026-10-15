/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalZeroMaskChoiceTowers
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalZeroContactLower
/-! The actual original zero masked lower records on the actual regime-run
split, without canonicality or a desired lower test/domain certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalActualSmoothZeroMaskHistories
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ContactStageKept ContactStageInvDomain
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneLowerDomain TangentDirectionAlong
  HomogenizedGlueingTower HomogenizedGlueingAlongTower HomogenizedGlueingLiftAlong
  StepOneTangentChange BlowupTowerIsomorphism BlowupTowerSplitIso ContactEquivalenceAlong
  HironakaOriginalZeroMaskChoiceTowers HironakaOriginalIndependentSmoothContactChoices
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionAllBranchHistory HironakaSmoothSubmersionOriginalZeroContactLower
  HironakaSmoothSubmersionPositiveMemberHistory
  HironakaSmoothSubmersionTangentContact StepOneRegime StepOneValueMasked
open ResolutionInvariantSpec (IsInvDomain)
variable {n m k : ℕ} {X D : CMfd.{u} n} {Y : CMfd.{u} m}

/-- Original ANY-test zero/nonspecial data internally give the actual OWN
computed mask, genuine lower domain/TEST/BOTH whole cosupports/future domain. -/
theorem actual_original_test_zero_mask_history (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain (k+2) M) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) (y : D)
    (hy : y ∈ (geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T y) (hl : level M T y=0) :
    let r := regimeRun (stepRegime M 0) T y
    let U := lowerMask M 0 (head T r) ((tail T r).proj y)
    let J := lowerMarkedM M 0 (head T r) ((tail T r).proj y)
    let R := restrict U (tail T r)
    ∃ hp : (tail T r).proj y ∈ U,
      IsInvDomain (k+1) J ∧ IsGeoTestTower J R ∧
      (geoTransformAlong J R).cosupp=(Subtype.val : openPreimage (tail T r) U → D) ⁻¹'
        (geoTransformAlong M T).cosupp ∧
      (⟨y,hp⟩ : openPreimage (tail T r) U) ∈ (geoTransformAlong J R).cosupp ∧
      IsInvDomain (k+1) (geoTransformAlong J R) := by
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 T).1.mpr hT
  have hyBar : y ∈ (geoTransformAlong (barMarked M) T).cosupp := by
    rw [(he.2 T).2 hBar]
    exact hy
  obtain ⟨hReg,hHeadCos⟩ := StepOneValueMasked.stepRegime_and_mem_cosupp_head M
    hM.isWellFormed T hBar hyBar hns
  rw [hl] at hReg hHeadCos
  let r := regimeRun (stepRegime M 0) T y
  let U := lowerMask M 0 (head T r) ((tail T r).proj y)
  let J := lowerMarkedM M 0 (head T r) ((tail T r).proj y)
  let R := restrict U (tail T r)
  have hHeadTest := ((isGeoTestTower_iff_head_tail (barMarked M) T r).mp hBar).1
  have hMask := StepOneValueMasked.mem_lowerMask_and_isInvDomain_M M hM.isWellFormed hM.one_le_d
    hn hmax hM.dimLE (head T r) hHeadTest hHeadCos hReg
  have hJ : IsInvDomain (k+1) J := by
    simpa only [show k+2-1=k+1 by omega] using hMask.2
  have hAppend : IsGeoTestTower (barMarked M) ((head T r).append (tail T r)) := by
    rw [head_append_tail]
    exact hBar
  have hLower := StepOneCompare.isGeoTestTower_cosupp_lowerMarkedB M hM.isWellFormed hM.one_le_d
    hmax (head T r) (tail T r) hAppend hHeadCos
  rw [head_append_tail,(he.2 T).2 hBar] at hLower
  change IsGeoTestTower J R ∧ (geoTransformAlong J R).cosupp=_ at hLower
  have hyLower : (⟨y,hMask.1⟩ : openPreimage (tail T r) U) ∈ (geoTransformAlong J R).cosupp := by
    rw [hLower.2]
    exact hy
  exact ⟨hMask.1,hJ,hLower.1,hLower.2,hyLower,
    InvDomainTowerAlong.isInvDomain_geoTransformAlong hJ R hLower.1⟩

private theorem actual_nested_contact_parent_pullback (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (w : X → ℂ) (T : BlowupTower X D)
    (hT : IsGeoTestTower (barMarked M) T) (U V : Opens D) (hVU : V ≤ U) :
    MarkedIdeal.pullback (fun p : V => (⟨(p : D),hVU p.property⟩ : U))
      (contactMarkedKept M w T U)=contactMarkedKept M w T V := by
  have hc := isCoherent_restrictedCoeff M hM.isCoherent hM.isClosedSubmanifold_N w T hT
  have hi : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun p : V => (⟨(p : D),hVU p.property⟩ : U)) :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val (fun p => hVU p.property)
  exact pullback_pullback_of_comp hc contMDiff_subtype_val hi (fun _ => rfl)

/-- ONLY original smooth data produce real source history and actual computed
common/OWN zero masks before BOTH literal lower TESTS and every whole comparison. -/
theorem exists_original_smooth_actual_zero_mask_histories :
    ∀ {f : Y → X}
    (_hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (_hn : 0<n) (M : MarkedIdeal n X) (_hM : IsInvDomain (k+2) M)
    (_hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (_hT : IsGeoTestTower M T),
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧ IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      ∀ (z : D'),g z ∈ (geoTransformAlong M T).cosupp → ¬IsSpecial M T (g z) → level M T (g z)=0 →
        let K := markedPullback (m := m) f M
        let r := regimeRun (stepRegime M 0) T (g z)
        let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
        let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
        let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
        let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
        let u := (tangentChoice M (T.proj (g z))).2 ∘ f
        let v := (tangentChoice K (Q.proj z)).2
        IsInvDomain (k+1) J ∧
        ∃ (a : (split Q r).1 → (split T r).1) (V : Opens (split Q r).1)
          (p : V → U) (q : openPreimage (tail Q r) V → openPreimage (tail T r) U),
          IsActualTowerPullback f (head Q r) (head T r) a ∧
          (V : Set (split Q r).1)=a ⁻¹' (U : Set (split T r).1) ∧
          (tail Q r).proj z ∈ V ∧ (tail Q r).proj z ∈ W ∧
          Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ p ∧
          let JCommon := contactMarkedKept K u (head Q r) V
          markedPullback (m := m) p J=JCommon ∧
          IsActualTowerPullback p (restrict V (tail Q r)) (restrict U (tail T r)) q ∧
          IsInvDomain (k+1+(m-n)) JCommon ∧ IsInvDomain (k+1+(m-n)) JOwn ∧
          IsGeoTestTower JCommon (restrict V (tail Q r)) ∧ IsGeoTestTower JOwn (restrict W (tail Q r)) ∧
          ∃ (Vu Vv : Opens (split Q r).1)
            (hzu : (tail Q r).proj z ∈ Vu) (hzv : (tail Q r).proj z ∈ Vv)
            (ψ : CMfd.of (n := m) Vv ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ CMfd.of (n := m) Vu)
            (ξ : CMfd.of (n := m) (openPreimage (tail Q r) Vv) ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯
              CMfd.of (n := m) (openPreimage (tail Q r) Vu)),
            ∃ (hVuV : Vu ≤ V) (hVvW : Vv ≤ W),
              IsTowerIso ψ (restrict Vv (tail Q r)) (restrict Vu (tail Q r)) ξ ∧
              ξ ⟨z,hzv⟩=⟨z,hzu⟩ ∧
              let A := contactMarkedKept K u (head Q r) Vu
              let B := contactMarkedKept K v (head Q r) Vv
              MarkedIdeal.pullback (fun b : Vu => (⟨(b : (split Q r).1),hVuV b.property⟩ : V)) JCommon=A ∧
              MarkedIdeal.pullback (fun b : Vv => (⟨(b : (split Q r).1),hVvW b.property⟩ : W)) JOwn=B ∧
              MarkedIdeal.pullback ψ A=B ∧
              IsGeoTestTower A (restrict Vu (tail Q r)) ∧ IsGeoTestTower B (restrict Vv (tail Q r)) ∧
              geoTransformAlong B (restrict Vv (tail Q r))=
                MarkedIdeal.pullback ξ (geoTransformAlong A (restrict Vu (tail Q r))) ∧
              ∀ j : ℕ,∃ ξj,
                IsTowerIso ψ (head (restrict Vv (tail Q r)) j) (head (restrict Vu (tail Q r)) j) ξj ∧
                IsTowerIso ξj (tail (restrict Vv (tail Q r)) j) (tail (restrict Vu (tail Q r)) j) ξ ∧
                geoTransformAlong B (head (restrict Vv (tail Q r)) j)=
                  MarkedIdeal.pullback ξj (geoTransformAlong A (head (restrict Vu (tail Q r)) j)) := by
  intro f hf hn M hM hmax T hT
  obtain ⟨D',Q,g,hCart,_hg,_hLen,_hSquare,hQ,_hCurrent,_hWF,_hCos,_hHeads⟩ :=
    exists_actual_relative_marked_tower hf M hM.isWellFormed T hT
  refine ⟨D',Q,g,hCart,hQ,?_⟩
  intro z hy hns hl
  let K := markedPullback (m := m) f M
  let r := regimeRun (stepRegime M 0) T (g z)
  let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
  let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
  let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
  let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
  let u := (tangentChoice M (T.proj (g z))).2 ∘ f
  let v := (tangentChoice K (Q.proj z)).2
  have heM := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (heM.2 T).1.mpr hT
  have hyBar : g z ∈ (geoTransformAlong (barMarked M) T).cosupp := by
    rw [(heM.2 T).2 hBar]; exact hy
  have hK₀ := isInvDomain_markedPullback_submersion hf M hM
  have hK : IsInvDomain (k+(m-n)+2) K := by
    convert hK₀ using 1
    omega
  have hMaxK : IsMaximalOrderAlong K.N K.ideal K.d :=
    isMaximalOrderAlong_preimage hf hM.isWellFormed.isCoherent M.N M.d hmax
  have hzK : z ∈ (geoTransformAlong K Q).cosupp := by
    rw [IsActualTowerPullback.relative_cosupport_dictionary hCart M hM.isWellFormed hT]
    exact hy
  have hLevel := IsActualTowerPullback.bar_level_dictionary hCart M hM.isWellFormed hBar z
  have hlK : level K Q z=0 := hLevel.trans hl
  have hnsK : ¬IsSpecial K Q z :=
    fun hs => hns ((IsActualTowerPullback.all_isSpecial_dictionary hCart M hM.isWellFormed hBar z).mp hs)
  have hRun : regimeRun (stepRegime K 0) Q z=r :=
    IsActualTowerPullback.all_stepRegime_run hCart M hM.isWellFormed hBar 0 z
  have hm : 0<m := hn.trans_le
    (HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt (hf.isSubmersionAt (Q.proj z)))
  obtain ⟨_hpU,hJ,hJT,_hJCos,_hyJ,_hJNext⟩ :=
    actual_original_test_zero_mask_history hn M hM hmax T hT (g z) hy hns hl
  have hOwn := actual_original_test_zero_mask_history hm K hK hMaxK Q hQ z hzK hnsK hlK
  rw [hRun] at hOwn
  obtain ⟨hpW,hOwnD,hOwnT,_hOwnCos,_hzOwn,_hOwnNext⟩ := hOwn
  have hOwnDomain : IsInvDomain (k+1+(m-n)) JOwn := by
    convert hOwnD using 1
    omega
  obtain ⟨_hr,_hu,a,V,p,q,hHeadCart,_hTailCart,hV,hpV,hpSmooth,_hqcoord,hWU,hCommonE,hRecord,hR⟩ :=
    original_zero_common_contact_mask_geometry hCart M hM.isWellFormed hM.one_le_d hmax hBar z hyBar hl hns
  let JCommon := contactMarkedKept K u (head Q r) V
  change markedPullback (m := m) p J=JCommon at hRecord
  have hCommonDomain := isInvDomain_markedPullback_submersion hpSmooth J hJ
  rw [hRecord] at hCommonDomain
  have hCommonT := (IsActualTowerPullback.relative_marked_dictionary hR J hJ.isWellFormed hJT).1
  rw [hRecord] at hCommonT
  have hBase : T.proj (g z)=f (Q.proj z) := hCart.proj_comm z
  have hBaseQ : (head Q r).proj ((tail Q r).proj z)=Q.proj z :=
    (congrFun (proj_eq_comp Q r) z).symm
  have hfx : f (Q.proj z) ∈ M.cosupp := hBase ▸
    proj_mem_cosupp_of_mem_cosupp hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hT hy
  have hxK : Q.proj z ∈ K.cosupp :=
    proj_mem_cosupp_of_mem_cosupp hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent Q hQ hzK
  obtain ⟨U₀,hU₀,hfxU₀,V₀,hV₀,hxV₀,_hu₀,hPull,hv₀,_hCurrent⟩ :=
    exists_original_smooth_independent_contact_glueing hf M hM hmax (Q.proj z) hfx
  let W₀ : Opens Y := ⟨f ⁻¹' (U₀ : Set X),U₀.isOpen.preimage hf.contMDiff.continuous⟩
  have hPullU : IsTangentDirectionAlong K.N K.ideal K.d W₀ u := by
    dsimp only [u]
    rw [hBase]
    exact hPull
  have hVU₀ : (V : Set (split Q r).1) ⊆ (head Q r).proj ⁻¹' (W₀ : Set Y) := by
    intro b hb
    change f ((head Q r).proj b) ∈ U₀
    apply (Set.ext_iff.mp hU₀ (f ((head Q r).proj b))).mpr
    rw [←hBase]
    exact hWU hb
  have hWV₀ : (W : Set (split Q r).1) ⊆ (head Q r).proj ⁻¹' (V₀ : Set Y) := by
    intro b hb
    change (head Q r).proj b ∈ V₀
    apply (Set.ext_iff.mp hV₀ ((head Q r).proj b)).mpr
    have hh := (interior_subset hb).1
    rwa [hBaseQ] at hh
  have hOwnE : ∀ H ∈ origMembers K (head Q r),Disjoint (W : Set (split Q r).1) H := by
    intro H hH
    exact Set.disjoint_left.mpr (fun b hb hbH => (interior_subset hb).2.1 H hH hbH)
  obtain ⟨O,hxO,hCompare⟩ := exists_original_zero_mask_choice_towers K hK.isWellFormed
    hK.one_le_d (Q.proj z) hxK W₀ V₀ hPullU hfxU₀ hv₀ hxV₀
  have hFullQ : IsGeoTestTower K ((head Q r).append (tail Q r)) := by
    rw [head_append_tail]; exact hQ
  have hzFullQ : z ∈ (geoTransformAlong K ((head Q r).append (tail Q r))).cosupp := by
    rw [head_append_tail]; exact hzK
  have hzO : (head Q r).proj ((tail Q r).proj z) ∈ O := by rw [hBaseQ]; exact hxO
  obtain ⟨Vu,Vv,hzu,hzv,ψ,ξ,hVuV,hVvW,hIso,hξ,hParent,_hAN,_hAI,_hBN,_hBI,hAT,hBT,hEndpoint,hEveryHead⟩ :=
    hCompare (head Q r) (tail Q r) hFullQ V W hVU₀ hWV₀ hCommonE hOwnE z hpV hpW hzO hzFullQ
  have heK := coeff_homAlong_wEquiv K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d
  have hBarQ : IsGeoTestTower (barMarked K) Q := (heK.2 Q).1.mpr hQ
  have hBarHeadQ := ((isGeoTestTower_iff_head_tail (barMarked K) Q r).mp hBarQ).1
  have hNestedCommon := actual_nested_contact_parent_pullback K hK.isWellFormed u (head Q r) hBarHeadQ V Vu hVuV
  have hNestedOwn := actual_nested_contact_parent_pullback K hK.isWellFormed v (head Q r) hBarHeadQ W Vv hVvW
  have hOwnRecord : JOwn=contactMarkedKept K v (head Q r) W := by
    change contactMarkedKept K (tangentChoice K ((head Q r).proj ((tail Q r).proj z))).2 (head Q r) W=_
    rw [hBaseQ]
  rw [←hOwnRecord] at hNestedOwn
  exact ⟨hJ,a,V,p,q,hHeadCart,hV,hpV,hpW,hpSmooth,hRecord,hR,hCommonDomain,hOwnDomain,
    hCommonT,hOwnT,Vu,Vv,hzu,hzv,ψ,ξ,hVuV,hVvW,hIso,hξ,hNestedCommon,hNestedOwn,hParent,hAT,hBT,hEndpoint,hEveryHead⟩

end
end Hironaka.HironakaOriginalActualSmoothZeroMaskHistories
