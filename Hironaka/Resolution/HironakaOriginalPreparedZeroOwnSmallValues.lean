/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedCurrentLowerFullValues
import Hironaka.Resolution.HironakaOriginalGivenSmoothZeroChoices
/-! Independent genuine contact choices construct the actual OWN-small model
before higher prepared CURRENT lower FULL values; no OWN-large extension. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedZeroOwnSmallValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ContactStageKept ContactStageInvDomain
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneLowerDomain
  StepOneRegime StepOneValueMasked CanonicalCentres BlowupTowerIsomorphism
  HironakaOriginalGivenSmoothZeroChoices HironakaOriginalSourceChoiceCartesian HironakaOriginalZeroOwnSmallSmoothValues
  HironakaOriginalActualSmoothZeroMaskHistories HironakaOriginalPreparedCurrentLowerFullValues
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionAllBranchHistory HironakaSmoothSubmersionPositiveMemberHistory
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaOriginalUntestedCurveSmoothValues
  HironakaSmoothSubmersionOrderedChoiceImageTrace
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m : ℕ} {X Y Z : CMfd.{u} n} {A B : CMfd.{u} m}

private theorem zero_current_lower_values
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T c)
    (y : Z) (hy : y ∈ (geoTransformAlong M (.step T C π hπ)).cosupp)
    (hns : ¬IsSpecial M (.step T C π hπ) y) (hl : level M (.step T C π hπ) y=0) :
    let P := .step T C π hπ
    let r := regimeRun (stepRegime M 0) P y
    let U := lowerMask M 0 (head P r) ((tail P r).proj y)
    let J := lowerMarkedM M 0 (head P r) ((tail P r).proj y)
    ∀ {f : A → U} {g : B → openPreimage (tail P r) U} {Q : BlowupTower A B},
      IsActualTowerPullback f Q (restrict U (tail P r)) g → ∀ z : B,
        g z ∈ (geoTransformAlong J (restrict U (tail P r))).cosupp → ∀ d : ℕ,
          (invFamily hm ((m-n)+d+2)).inv (markedPullback (m := m) f J) Q z=
            familyDimensionMap (m-n) (d+2)
              ((invFamily hn (d+2)).inv J (restrict U (tail P r)) (g z)) := by
  let P : BlowupTower X Z := .step T C π hπ
  let F : ℕ → Prop := fun a =>
    let r := regimeRun (stepRegime M a) P y
    let U := lowerMask M a (head P r) ((tail P r).proj y)
    let J := lowerMarkedM M a (head P r) ((tail P r).proj y)
    ∀ {f : A → U} {g : B → openPreimage (tail P r) U} {Q : BlowupTower A B},
      IsActualTowerPullback f Q (restrict U (tail P r)) g → ∀ z : B,
        g z ∈ (geoTransformAlong J (restrict U (tail P r))).cosupp → ∀ d : ℕ,
          (invFamily hm ((m-n)+d+2)).inv (markedPullback (m := m) f J) Q z=
            familyDimensionMap (m-n) (d+2)
              ((invFamily hn (d+2)).inv J (restrict U (tail P r)) (g z))
  have hNum := current_lower_full_smooth_values_after_stepone_cut
    (A := A) (B := B) hn hm M hM hmax T hcan C hC π hπ hCuts y hy hns
  have hCurrent : F (level M P y) := by
    intro f g Q h z hz d
    exact hNum.2.2 h z hz d
  have hZero : F 0 := (congrArg F hl).mp hCurrent
  change F 0
  exact hZero

private theorem own_small_cartesian_geometry {D₀ : CMfd.{u} n} {Y₀ E₀ : CMfd.{u} m}
    (J : MarkedIdeal n X) (hJ : IsInvDomain 2 J) (R : BlowupTower X D₀) (hR : IsGeoTestTower J R)
    (S : BlowupTower Y₀ E₀) (V W Vu Vv : Opens Y₀) (hVuV : Vu≤V) (hVvW : Vv≤W)
    (JOwn : MarkedIdeal m W) (p : V → X) (q : openPreimage S V → D₀)
    (hp : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ p)
    (hCart : IsActualTowerPullback p (restrict V S) R q)
    (ψ : CMfd.of (n := m) Vv ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ CMfd.of (n := m) Vu)
    (ξ : CMfd.of (n := m) (openPreimage S Vv) ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯
      CMfd.of (n := m) (openPreimage S Vu))
    (hIso : IsTowerIso ψ (restrict Vv S) (restrict Vu S) ξ)
    (hParent : MarkedIdeal.pullback ψ (MarkedIdeal.pullback
      (fun b : Vu => (⟨b.val,hVuV b.property⟩ : V)) (markedPullback (m := m) p J))=
        MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn)
    (z : E₀) (hzu : S.proj z ∈ Vu) (hzv : S.proj z ∈ Vv)
    (hFix : ξ ⟨z,hzv⟩=⟨z,hzu⟩) (y : D₀) (hy : y ∈ (geoTransformAlong J R).cosupp)
    (hPoint : q ⟨z,hVuV hzu⟩=y) :
    ∃ (φ : Vv → X) (η : openPreimage S Vv → D₀),
      let K := MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn
      IsActualTowerPullback φ (restrict Vv S) R η ∧ markedPullback (m := m) φ J=K ∧ η ⟨z,hzv⟩=y ∧
      IsGeoTestTower K (restrict Vv S) ∧
        (⟨z,hzv⟩ : openPreimage S Vv) ∈ (geoTransformAlong K (restrict Vv S)).cosupp := by
  let iVu : Vu → V := fun b => ⟨b.val,hVuV b.property⟩
  let pFlat : Vu → X := p ∘ iVu
  let qFlat : openPreimage S Vu → D₀ := fun b => q ⟨b.val,hVuV b.property⟩
  have hFlat := IsActualTowerPullback.restrict_source_inside_open hVuV hCart
  change IsActualTowerPullback pFlat (restrict Vu S) R qFlat at hFlat
  have hiVu : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ iVu :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val (fun b => hVuV b.property)
  have hpFlat : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ pFlat := hp.contMDiff.comp hiVu
  let φ := pFlat ∘ ψ
  let η := qFlat ∘ ξ
  let K := MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn
  have hOwn : markedPullback (m := m) φ J=K := by
    change markedPullback (m := m) (pFlat ∘ ψ) J=K
    rw [whole_markedPullback_comp (f := pFlat) hpFlat ψ.contMDiff J hJ.isWellFormed.isCoherent]
    have hInner : markedPullback (m := m) pFlat J=
        markedPullback (m := m) iVu (markedPullback (m := m) p J) :=
      whole_markedPullback_comp (f := p) (g := iVu) hp.contMDiff hiVu J hJ.isWellFormed.isCoherent
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
  have hKPoint : (⟨z,hzv⟩ : openPreimage S Vv) ∈ (geoTransformAlong K (restrict Vv S)).cosupp := by
    rw [hCos]
    change η ⟨z,hzv⟩ ∈ (geoTransformAlong J R).cosupp
    rw [hEndpoint]
    exact hy
  exact ⟨φ,η,hChoice,hOwn,hEndpoint,hTest,hKPoint⟩

/-- The independent source OWN tangent and true small history are retained;
actual Cartesian geometry and point membership precede all FULL values. -/
theorem original_prepared_zero_own_small_values
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) M T c)
    {f : A → X} {g : B → Z} {Q : BlowupTower A B}
    (hCart : IsActualTowerPullback f Q (.step T C π hπ) g) :
    IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      ∀ z : B,g z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp →
        ¬IsSpecial M (.step T C π hπ) (g z) → level M (.step T C π hπ) (g z)=0 →
        let P := .step T C π hπ
        let K := markedPullback (m := m) f M
        let r := regimeRun (stepRegime M 0) P (g z)
        let U := lowerMask M 0 (head P r) ((tail P r).proj (g z))
        let J := lowerMarkedM M 0 (head P r) ((tail P r).proj (g z))
        let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
        let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
        ∃ (hp : (tail P r).proj (g z) ∈ U) (Vv : Opens (split Q r).1)
          (hVvW : Vv≤W) (hzv : (tail Q r).proj z ∈ Vv)
          (φ : Vv → U) (η : openPreimage (tail Q r) Vv → openPreimage (tail P r) U),
          let JSmall := MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn
          IsActualTowerPullback φ (restrict Vv (tail Q r)) (restrict U (tail P r)) η ∧
          markedPullback (m := m) φ J=JSmall ∧ η ⟨z,hzv⟩=⟨g z,hp⟩ ∧
          IsGeoTestTower JSmall (restrict Vv (tail Q r)) ∧
          (⟨z,hzv⟩ : openPreimage (tail Q r) Vv) ∈
            (geoTransformAlong JSmall (restrict Vv (tail Q r))).cosupp ∧
          ∀ d : ℕ,(invFamily hm ((m-n)+d+2)).inv JSmall (restrict Vv (tail Q r)) ⟨z,hzv⟩=
            familyDimensionMap (m-n) (d+2) ((invFamily hn (d+2)).inv J
              (restrict U (tail P r)) ⟨g z,hp⟩) := by
  let P : BlowupTower X Z := .step T C π hπ
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (k := 3) (invFamily hn 2) M hM hmax hn T hcan
  have hP : IsGeoTestTower M P := ⟨hb.2.1,hC⟩
  obtain ⟨hQ,hData⟩ := actual_zero_choices_with_endpoint (k := 1) hn M hM hmax P hP hCart
  refine ⟨hQ,?_⟩
  intro z hy hns hl
  let K := markedPullback (m := m) f M
  let r := regimeRun (stepRegime M 0) P (g z)
  let U := lowerMask M 0 (head P r) ((tail P r).proj (g z))
  let J := lowerMarkedM M 0 (head P r) ((tail P r).proj (g z))
  let W := lowerMask K 0 (head Q r) ((tail Q r).proj z)
  let JOwn := lowerMarkedM K 0 (head Q r) ((tail Q r).proj z)
  obtain ⟨hp,hJD,hJT,_hDict,hJP,_hJCurrent⟩ :=
    actual_original_test_zero_mask_history (k := 1) hn M hM hmax P hP (g z) hy hns hl
  obtain ⟨_hJ,a,V,p,q,_hHead,_hV,_hpV,_hpW,hpSmooth,hRecord,hR,hqcoord,
    _hCommonD,_hOwnD,_hCommonT,_hOwnT,Vu,Vv,hzu,hzv,ψ,ξ,hVuV,hVvW,hIso,hFix,
    hNestedCommon,hNestedOwn,hParent,_hAT,_hBT,_hCurrent,_hHeads⟩ := hData z hy hns hl
  have hParent' : MarkedIdeal.pullback ψ (MarkedIdeal.pullback
      (fun b : Vu => (⟨b.val,hVuV b.property⟩ : V)) (markedPullback (m := m) p J))=
      MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn := by
    rw [hRecord,hNestedCommon]
    exact hParent.trans hNestedOwn.symm
  have hPoint : q (⟨z,hVuV hzu⟩ : openPreimage (tail Q r) V)=
      (⟨g z,hp⟩ : openPreimage (tail P r) U) := Subtype.ext (hqcoord ⟨z,hVuV hzu⟩)
  obtain ⟨φ,η,hChoice,hOwn,hEndpoint,hTest,hBPoint⟩ :=
    own_small_cartesian_geometry (X := CMfd.of (n := n) U) (Y₀ := (split Q r).1)
      J hJD (restrict U (tail P r)) hJT (tail Q r) V W Vu Vv hVuV hVvW JOwn p q
      hpSmooth hR ψ ξ hIso hParent' z hzu hzv hFix ⟨g z,hp⟩ hJP hPoint
  let JSmall := MarkedIdeal.pullback (fun b : Vv => (⟨b.val,hVvW b.property⟩ : W)) JOwn
  refine ⟨hp,Vv,hVvW,hzv,φ,η,hChoice,hOwn,hEndpoint,hTest,hBPoint,?_⟩
  intro d
  have hyModel : η (⟨z,hzv⟩ : openPreimage (tail Q r) Vv) ∈
      (geoTransformAlong J (restrict U (tail P r))).cosupp := by
    rw [hEndpoint]
    exact hJP
  have hv := zero_current_lower_values
    (A := CMfd.of (n := m) Vv) (B := CMfd.of (n := m) (openPreimage (tail Q r) Vv))
    hn hm M hM hmax T hcan C hC π hπ hCuts
    (g z) hy hns hl hChoice ⟨z,hzv⟩ hyModel d
  rw [hOwn,hEndpoint] at hv
  exact hv

end
end Hironaka.HironakaOriginalPreparedZeroOwnSmallValues
