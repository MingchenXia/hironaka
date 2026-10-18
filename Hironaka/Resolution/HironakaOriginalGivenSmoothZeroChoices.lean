/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalZeroOwnSmallSmoothValues
/-! Actual independent original zero choices and OWN SMALL values for ANY
given upper Cartesian history; no different upper source history is chosen. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalGivenSmoothZeroChoices
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
open HironakaOriginalZeroOwnSmallSmoothValues HironakaOriginalSourceChoiceCartesian HironakaOriginalUntestedCurveSmoothValues
  HironakaOriginalActualSmoothZeroMaskHistories
  MaxLocusLocal CanonicalCentres HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionCanonicalValueDimensionShift
open ResolutionInvariantSpec (IsInvDomain)
variable {n m k : ℕ} {X D : CMfd.{u} n} {Y E : CMfd.{u} m}

private theorem actual_base_submersion {f : Y → X} {D' : CMfd.{u} m}
    {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f := by
  induction h with
  | refl hf => exact hf
  | step _ _ _ _ ih => exact ih

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

/-- The GIVEN actual upper source history is retained before all independent
contact choices and exact endpoint/whole parent/head constructions. -/
theorem actual_zero_choices_with_endpoint
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain (k+2) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T)
    {f : Y → X} {D' : CMfd.{u} m} {Q : BlowupTower Y D'} {g : D' → D}
    (hCart : IsActualTowerPullback f Q T g) :
    IsGeoTestTower (markedPullback (m := m) f M) Q ∧
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
          (∀ b,(q b : D)=g (b : D')) ∧
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
  have hf := actual_base_submersion hCart
  have hQ := (IsActualTowerPullback.relative_marked_dictionary hCart M hM.isWellFormed hT).1
  refine ⟨hQ,?_⟩
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
  obtain ⟨_hr,_hu,a,V,p,q,hHeadCart,_hTailCart,hV,hpV,hpSmooth,hqcoord,hWU,hCommonE,hRecord,hR⟩ :=
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
  exact ⟨hJ,a,V,p,q,hHeadCart,hV,hpV,hpW,hpSmooth,hRecord,hR,hqcoord,hCommonDomain,hOwnDomain,
    hCommonT,hOwnT,Vu,Vv,hzu,hzv,ψ,ξ,hVuV,hVvW,hIso,hξ,hNestedCommon,hNestedOwn,hParent,hAT,hBT,hEndpoint,hEveryHead⟩

private theorem actual_small_curve_model (hn : 0<n) (hm : 0<m)
    (J : MarkedIdeal n X) (hJ : IsInvDomain 1 J) (R : BlowupTower X D) (hR : IsGeoTestTower J R)
    (S : BlowupTower Y E) (V W Vu Vv : Opens Y) (hVuV : Vu≤V) (hVvW : Vv≤W)
    (JOwn : MarkedIdeal m W) (p : V → X) (q : openPreimage S V → D)
    (hp : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ p)
    (hCart : IsActualTowerPullback p (restrict V S) R q)
    (ψ : CMfd.of (n := m) Vv ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ CMfd.of (n := m) Vu)
    (ξ : CMfd.of (n := m) (openPreimage S Vv) ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯
      CMfd.of (n := m) (openPreimage S Vu))
    (hIso : IsTowerIso ψ (restrict Vv S) (restrict Vu S) ξ)
    (hParent : MarkedIdeal.pullback ψ (MarkedIdeal.pullback
      (fun b : Vu => (⟨b.val,hVuV b.property⟩ : V)) (markedPullback (m := m) p J))=
        MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn)
    (z : E) (hzu : S.proj z ∈ Vu) (hzv : S.proj z ∈ Vv)
    (hFix : ξ ⟨z,hzv⟩=⟨z,hzu⟩) (y : D) (hy : y ∈ (geoTransformAlong J R).cosupp)
    (hPoint : q ⟨z,hVuV hzu⟩=y) :
    ∃ (φ : Vv → X) (η : openPreimage S Vv → D),
      let B := MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn
      IsActualTowerPullback φ (restrict Vv S) R η ∧ markedPullback (m := m) φ J=B ∧ η ⟨z,hzv⟩=y ∧
      IsGeoTestTower B (restrict Vv S) ∧ (⟨z,hzv⟩ : openPreimage S Vv) ∈ (geoTransformAlong B (restrict Vv S)).cosupp ∧
      ∀ d : ℕ,(invFamily hm ((m-n)+d+1)).inv B (restrict Vv S) ⟨z,hzv⟩=
        familyDimensionMap (m-n) (d+1) ((invFamily hn (d+1)).inv J R y) := by
  let iVu : Vu → V := fun b => ⟨b.val,hVuV b.property⟩
  let pFlat : Vu → X := p ∘ iVu
  let qFlat : openPreimage S Vu → D := fun b => q ⟨b.val,hVuV b.property⟩
  have hFlat := IsActualTowerPullback.restrict_source_inside_open hVuV hCart
  change IsActualTowerPullback pFlat (restrict Vu S) R qFlat at hFlat
  have hiVu : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ iVu :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val (fun b => hVuV b.property)
  have hpFlat : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ pFlat := hp.contMDiff.comp hiVu
  let φ := pFlat ∘ ψ
  let η := qFlat ∘ ξ
  let B := MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn
  have hOwn : markedPullback (m := m) φ J=B := by
    change markedPullback (m := m) (pFlat ∘ ψ) J=B
    rw [whole_markedPullback_comp (f := pFlat) hpFlat ψ.contMDiff J hJ.isWellFormed.isCoherent]
    have hInner : markedPullback (m := m) pFlat J=
        markedPullback (m := m) iVu (markedPullback (m := m) p J) :=
      whole_markedPullback_comp hp.contMDiff hiVu J hJ.isWellFormed.isCoherent
    rw [hInner]
    exact hParent
  have hChoice := HironakaOriginalSourceChoiceCartesian.IsActualTowerPullback.source_isomorphism hFlat hIso
  have hEndpoint : η (⟨z,hzv⟩ : openPreimage S Vv)=y := by
    change qFlat (ξ ⟨z,hzv⟩)=y
    rw [hFix]
    exact hPoint
  have hTest := (IsActualTowerPullback.relative_marked_dictionary hChoice J hJ.isWellFormed hR).1
  rw [hOwn] at hTest
  have hCos := IsActualTowerPullback.relative_cosupport_dictionary hChoice J hJ.isWellFormed hR
  rw [hOwn] at hCos
  have hBPoint : (⟨z,hzv⟩ : openPreimage S Vv) ∈ (geoTransformAlong B (restrict Vv S)).cosupp := by
    rw [hCos]
    change η ⟨z,hzv⟩ ∈ (geoTransformAlong J R).cosupp
    rw [hEndpoint]
    exact hy
  refine ⟨φ,η,hChoice,hOwn,hEndpoint,hTest,hBPoint,?_⟩
  intro d
  have hyModel : qFlat (ξ (⟨z,hzv⟩ : openPreimage S Vv)) ∈ (geoTransformAlong J R).cosupp := by
    change η ⟨z,hzv⟩ ∈ (geoTransformAlong J R).cosupp
    rw [hEndpoint]
    exact hy
  have hv := original_curve_full_value_source_isomorphism hn hm d hFlat J hJ hR hIso ⟨z,hzv⟩ hyModel
  change (invFamily hm ((m-n)+d+1)).inv (markedPullback (m := m) φ J) _ _=
    familyDimensionMap (m-n) (d+1) ((invFamily hn (d+1)).inv J R (η ⟨z,hzv⟩)) at hv
  rw [hOwn,hEndpoint] at hv
  exact hv

/-- Genuine OWN SMALL geometry and all-depth values use this SAME GIVEN
actual upper Cartesian history, without source-choice value certificates. -/
theorem original_given_zero_own_small_smooth_values
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T)
    {f : Y → X} {D' : CMfd.{u} m} {Q : BlowupTower Y D'} {g : D' → D}
    (hCart : IsActualTowerPullback f Q T g) :
    IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      ∀ (z : D'),g z ∈ (geoTransformAlong M T).cosupp → ¬IsSpecial M T (g z) → level M T (g z)=0 →
        let K := markedPullback (m := m) f M
        let r := regimeRun (stepRegime M 0) T (g z)
        let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
        let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
        let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
        let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
        ∃ (hp : (tail T r).proj (g z) ∈ U) (Vv : Opens (split Q r).1)
          (hVvW : Vv≤W) (hzv : (tail Q r).proj z ∈ Vv)
          (p : Vv → U) (q : openPreimage (tail Q r) Vv → openPreimage (tail T r) U),
          let B := MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn
          IsActualTowerPullback p (restrict Vv (tail Q r)) (restrict U (tail T r)) q ∧
          markedPullback (m := m) p J=B ∧ q ⟨z,hzv⟩=⟨g z,hp⟩ ∧
          IsGeoTestTower B (restrict Vv (tail Q r)) ∧
          (⟨z,hzv⟩ : openPreimage (tail Q r) Vv) ∈
            (geoTransformAlong B (restrict Vv (tail Q r))).cosupp ∧
          ∀ d : ℕ,(invFamily hm ((m-n)+d+1)).inv B (restrict Vv (tail Q r)) ⟨z,hzv⟩=
            familyDimensionMap (m-n) (d+1) ((invFamily hn (d+1)).inv J
              (restrict U (tail T r)) ⟨g z,hp⟩) := by
  obtain ⟨hQ,hData⟩ := actual_zero_choices_with_endpoint (k := 0) hn M hM hmax T hT hCart
  refine ⟨hQ,?_⟩
  intro z hy hns hl
  let K := markedPullback (m := m) f M
  let r := regimeRun (stepRegime M 0) T (g z)
  let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
  let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
  let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
  let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
  let u := (tangentChoice M (T.proj (g z))).2 ∘ f
  let v := (tangentChoice K (Q.proj z)).2
  obtain ⟨hp,hJD,hJT,_hJCos,hJP,_hJNext⟩ :=
    actual_original_test_zero_mask_history (k := 0) hn M hM hmax T hT (g z) hy hns hl
  obtain ⟨_hJ,a,V,p,q,_hHeadCart,_hV,_hpV,_hpW,hpSmooth,hRecord,hR,hqcoord,
    _hCommonD,_hOwnD,_hCommonT,_hOwnT,Vu,Vv,hzu,hzv,ψ,ξ,hVuV,hVvW,hIso,hξ,
    hNestedCommon,hNestedOwn,hParent,_hAT,_hBT,_hEndpoint,_hHeads⟩ := hData z hy hns hl
  have hParent' : MarkedIdeal.pullback ψ (MarkedIdeal.pullback
      (fun b : Vu => (⟨b.val,hVuV b.property⟩ : V)) (markedPullback (m := m) p J))=
      MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn := by
    rw [hRecord,hNestedCommon]
    exact hParent.trans hNestedOwn.symm
  have hPoint : q (⟨z,hVuV hzu⟩ : openPreimage (tail Q r) V)=(⟨g z,hp⟩ : openPreimage (tail T r) U) :=
    Subtype.ext (hqcoord ⟨z,hVuV hzu⟩)
  obtain ⟨φ,η,hChoice,hOwn,hEndpoint,hTest,hBPoint,hValues⟩ :=
    actual_small_curve_model (X := CMfd.of (n := n) U) (Y := (split Q r).1)
      hn hm J hJD (restrict U (tail T r)) hJT (tail Q r) V W Vu Vv hVuV hVvW JOwn p q
      hpSmooth hR ψ ξ hIso hParent' z hzu hzv hξ ⟨g z,hp⟩ hJP hPoint
  exact ⟨hp,Vv,hVvW,hzv,φ,η,hChoice,hOwn,hEndpoint,hTest,hBPoint,hValues⟩

end
end Hironaka.HironakaOriginalGivenSmoothZeroChoices
