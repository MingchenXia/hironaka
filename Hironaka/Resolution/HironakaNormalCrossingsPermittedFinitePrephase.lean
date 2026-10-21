/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsPermittedCountDrop
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Resolution.HironakaCompactCosupportOpenTowerExtension

/-!
# Finite old-branch simplification near the whole permitted cosupport

This module retains the SAME original ideal, marking and entire retained/born
boundary. Global old selfcrossings outside the permitted neighbourhood are not
repaired. The finite iteration is developed from the actual one-phase drop and
the genuine reverse open-history producer, with no supplied phase certificate.
Blueprint: `hironaka-normal-crossings-permitted-finite-prephase-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsPermittedFinitePrephase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower GermIdealOrder
  MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HironakaBaseChange
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaNormalCrossingsBoundarySeparation
  HironakaNormalCrossingsPermittedCountDrop
  BlowupTowerIsomorphism
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Whole compact cosupport persists along every actual test history; neither
nonzero ideals nor an invariant-domain certificate are needed. -/
theorem current_cosupport_compact_of_wellFormed (M : MarkedIdeal n X)
    (hw : M.IsWellFormed) (hK : IsCompact M.cosupp)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    IsCompact (geoTransformAlong M T).cosupp ∧
      (geoTransformAlong M T).cosupp ⊆ T.proj ⁻¹' M.cosupp := by
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT
  have hc := GiraudAlong.isClosed_cosupport_along hwT.isCoherent hwT.isClosedSubmanifold_N
    (geoTransformAlong M T).d
  have hs : (geoTransformAlong M T).cosupp ⊆ T.proj ⁻¹' M.cosupp :=
    fun _ hy => StepOneLowerDomain.proj_mem_cosupp_of_mem_cosupp hw.isClosedSubmanifold_N
      hw.isCoherent T hT hy
  exact ⟨((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
    hc hs,hs⟩

/-- Restricting to an actual open containing the ENTIRE cosupport retains
compactness, without a compact-intersection premise on that open. -/
theorem restricted_cosupport_compact (M : MarkedIdeal n X)
    (hI : M.ideal.IsCoherent) (hK : IsCompact M.cosupp)
    (U : Opens X) (hU : M.cosupp ⊆ U) :
    IsCompact (MarkedIdeal.pullback (Subtype.val : U → X) M).cosupp := by
  rw [cosupp_pullback_val M
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
  rw [Subtype.isCompact_iff,image_preimage_eq_inter_range,Subtype.range_coe,
    inter_eq_left.mpr hU]
  exact hK

/-- A genuine actual upper open embedding transports an entire local open
neighbourhood to a literal ambient open with its real holomorphic inverse. -/
theorem exists_open_image_equiv {g : Z → Y} (hg : IsOpenHoloEmbedding n g)
    (V : Opens Z) :
    ∃ (W : Opens Y) (χ : V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ W),
      (W : Set Y)=g '' (V : Set Z) ∧ ∀ v : V,(χ v : Y)=g v := by
  have hg' := hg.contMDiff
  obtain ⟨O,Φ,hΦ⟩ := hg
  have ho : IsOpenMap g := by
    have he : g=Subtype.val ∘ Φ := funext hΦ
    rw [he]
    exact O.isOpen.isOpenMap_subtype_val.comp Φ.toHomeomorph.isOpenMap
  let W : Opens Y := ⟨g '' (V : Set Z),ho _ V.isOpen⟩
  have hWO (w : W) : (w:Y)∈O := by
    obtain ⟨z,_hz,hz⟩ := w.property
    rw [←hz,hΦ z]
    exact (Φ z).property
  let q : W → O := fun w => ⟨w.val,hWO w⟩
  have hq : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ q :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val hWO
  have hInv (w : W) : Φ.symm (q w)∈V := by
    obtain ⟨z,hz,hzw⟩ := w.property
    have he : q w=Φ z := Subtype.ext (hzw.symm.trans (hΦ z))
    rw [he,Φ.symm_apply_apply]
    exact hz
  let f : V → W := fun v => ⟨g v,⟨v,v.property,rfl⟩⟩
  let fi : W → V := fun w => ⟨Φ.symm (q w),hInv w⟩
  have hleft (v : V) : fi (f v)=v := by
    apply Subtype.ext
    change Φ.symm (q (f v))=v.val
    have he : q (f v)=Φ v.val := Subtype.ext (hΦ v.val)
    rw [he,Φ.symm_apply_apply]
  have hright (w : W) : f (fi w)=w := by
    apply Subtype.ext
    change g (Φ.symm (q w))=w.val
    rw [hΦ,Φ.apply_symm_apply]
  have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f :=
    BlowupRestrictOpen.contMDiff_opens_mk
      (hg'.comp contMDiff_subtype_val) (fun v : V => (show g v∈W from ⟨v,v.property,rfl⟩))
  let χ : V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ W :=
    { toEquiv := ⟨f,fi,hleft,hright⟩
      contMDiff_toFun := hf
      contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk
        (Φ.symm.contMDiff.comp hq) hInv }
  exact ⟨W,χ,rfl,fun _ => rfl⟩

private theorem count_congr {A : Type u} [TopologicalSpace A]
    [ChartedSpace (ComplexModel n) A] {H K : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H)
    (hK : IsNormalCrossingsCarrier (n := n) K) (heq : H=K) (x : A) :
    branchMultiplicity hH x=branchMultiplicity hK x := by
  subst K
  rfl

private theorem transport_open_bound (A : MarkedIdeal n Y) (B : MarkedIdeal n Z)
    {g : Z → Y} (hg : IsOpenHoloEmbedding n g)
    (hcover : A.cosupp ⊆ Set.range g)
    (hcos : B.cosupp=g ⁻¹' A.cosupp)
    (hE : B.E=A.E.map (g ⁻¹' ·)) (H : Set Y)
    (V : Opens Z) (hV : B.cosupp ⊆ V)
    (h : IsBoundaryAdaptedCarrier (n := n)
      ((Subtype.val : V → Z) ⁻¹' (g ⁻¹' H))
      (B.E.map (fun D => (Subtype.val : V → Z) ⁻¹' D)))
    {k : ℕ} (hb : ∀ v : V,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) v≤k) :
    ∃ (W : Opens Y),A.cosupp ⊆ W ∧
      ∃ hw : IsBoundaryAdaptedCarrier (n := n)
        ((Subtype.val : W → Y) ⁻¹' H)
        (A.E.map (fun D => (Subtype.val : W → Y) ⁻¹' D)),
        ∀ w : W,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hw) w≤k := by
  obtain ⟨W,χ,hW,hχ⟩ := exists_open_image_equiv hg V
  have hback (w : W) : g ((χ.symm w : V) : Z)=(w:Y) :=
    (hχ (χ.symm w)).symm.trans (congrArg Subtype.val (χ.apply_symm_apply w))
  have hOld : χ.symm ⁻¹' ((Subtype.val : V → Z) ⁻¹' (g ⁻¹' H))=
      (Subtype.val : W → Y) ⁻¹' H := by
    ext w
    change (g ((χ.symm w : V) : Z)∈H)↔((w:Y)∈H)
    rw [hback]
  have hList : (B.E.map (fun D => (Subtype.val : V → Z) ⁻¹' D)).map (χ.symm ⁻¹' ·)=
      A.E.map (fun D => (Subtype.val : W → Y) ⁻¹' D) := by
    rw [hE,List.map_map,List.map_map]
    apply List.map_congr_left
    intro D _hD
    ext w
    change (g ((χ.symm w : V) : Z)∈D)↔((w:Y)∈D)
    rw [hback]
  have hp := HironakaNormalCrossingsBiholomorphicMultiplicity.boundaryAdapted_preimage
    χ.symm.contMDiff (MarkedIdealTowerTransport.notMem_exceptionalLocus χ.symm) h
  have hw : IsBoundaryAdaptedCarrier (n := n)
      ((Subtype.val : W → Y) ⁻¹' H)
      (A.E.map (fun D => (Subtype.val : W → Y) ⁻¹' D)) := by
    simpa only [hOld,hList] using hp
  refine ⟨W,?_,hw,?_⟩
  · intro y hy
    obtain ⟨z,hzy⟩ := hcover hy
    have hz : z∈B.cosupp := by
      rw [hcos]
      change g z∈A.cosupp
      rw [hzy]
      exact hy
    rw [hW]
    exact ⟨z,hV hz,hzy⟩
  · intro w
    have heq : branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hw) w=
        branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) (χ.symm w) :=
      (count_congr _ (isNormalCrossingsCarrier_of_boundaryAdapted hp) hOld.symm w).trans
        (HironakaNormalCrossingsBiholomorphicMultiplicity.branchMultiplicity_preimage
          χ.symm.contMDiff (MarkedIdealTowerTransport.notMem_exceptionalLocus χ.symm)
          (isNormalCrossingsCarrier_of_boundaryAdapted h)
          (isNormalCrossingsCarrier_of_boundaryAdapted hp) w)
    rw [heq]
    exact hb (χ.symm w)

private def OpenExtension (n : ℕ) : Prop :=
  ∀ {A : CMfd.{u} n} (M : MarkedIdeal n A)
    (_hN : IsClosedSubmanifold n M.N) (_hI : M.ideal.IsCoherent)
    (_hK : IsCompact M.cosupp) (U : Opens A) (_hU : M.cosupp ⊆ U)
    {B : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) U) B),
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → A) M) T →
    ∃ (D : CMfd.{u} n) (Q : BlowupTower A D)
      (e : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U),
      IsGeoTestTower M Q ∧
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) T (restrict U Q) e

private theorem finite_prephase_of_open_extension (extend : OpenExtension.{u} n) (r : ℕ) :
    ∀ {A : CMfd.{u} n} (I : GermIdeal n A) (_hI : I.IsCoherent)
      (d : ℕ) (_hd : 1≤d) (_hK : IsCompact (cosupport n univ I d))
      {H : Set A} {E : List (Set A)} (h : IsBoundaryAdaptedCarrier (n := n) H E),
      (∀ x : A,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x≤r) →
      ∃ (B : CMfd.{u} n) (T : BlowupTower A B),
        IsGeoTestTower (⟨univ,E,I,d⟩ : MarkedIdeal n A) T ∧
        ∃ (V : Opens B),(geoTransformAlong (⟨univ,E,I,d⟩ : MarkedIdeal n A) T).cosupp ⊆ V ∧
          ∃ hp : IsBoundaryAdaptedCarrier (n := n)
            ((Subtype.val : V → B) ⁻¹' strictAlong T H)
            ((geoTransformAlong (⟨univ,E,I,d⟩ : MarkedIdeal n A) T).E.map
              (fun D => (Subtype.val : V → B) ⁻¹' D)),
            ∀ v : V,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hp) v≤1 := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro A I hI d hd hK H E h hbound
      let M : MarkedIdeal n A := ⟨univ,E,I,d⟩
      by_cases hr : r≤1
      · let V : Opens A := ⊤
        have hp := boundaryAdapted_open V h
        refine ⟨A,.refl,trivial,V,subset_univ _,hp,?_⟩
        change ∀ v : V,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hp) v≤1
        intro v
        exact (HironakaNormalCrossingsOpenRestrictionSeparation.branchMultiplicity_open V
          (isNormalCrossingsCarrier_of_boundaryAdapted h)
          (isNormalCrossingsCarrier_of_boundaryAdapted hp) v).le.trans ((hbound v.val).trans hr)
      · obtain ⟨B,P,_hres,hP,_hZ,hPair,U,_hUeq,hU,hcount⟩ :=
          exists_original_phase_permitted_count_drop I hI d hd hK h (by omega) hbound
        let MP := geoTransformAlong M P
        have hw : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,hI,
          isSNCDivisor_of_boundaryAdapted h,
          SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor
            (isSNCDivisor_of_boundaryAdapted h)⟩
        have hwP := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw P hP
        obtain ⟨hNP,hIP,_⟩ := pullback_eq_mul_geoTransformAlong (𝔪:=M) rfl hI P hP
        have hKP : IsCompact MP.cosupp := (current_cosupport_compact_of_wellFormed M hw hK P hP).1
        let HU := (Subtype.val : U → B) ⁻¹' strictAlong P H
        let EU := MP.E.map (fun D => (Subtype.val : U → B) ⁻¹' D)
        let IU := GermIdeal.pullback (m := n) (Subtype.val : U → B) MP.ideal
        let MU : MarkedIdeal n U := ⟨univ,EU,IU,d⟩
        have hIU : IU.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback
          contMDiff_subtype_val hIP
        have hMU : MU=MarkedIdeal.pullback (Subtype.val : U → B) MP := by
          apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
          · change univ=(Subtype.val : U → B) ⁻¹' MP.N
            rw [hNP,preimage_univ]
          · rfl
          · rfl
          · exact (d_geoTransformAlong M P).symm
        have hKU : IsCompact MU.cosupp := by
          rw [hMU]
          exact restricted_cosupport_compact MP hIP hKP U hU
        have hLocal : IsBoundaryAdaptedCarrier (n := n) HU EU := boundaryAdapted_open U hPair
        obtain ⟨C,S,hS,V,hV,hSV,hOne⟩ :=
          ih (r-1) (by omega) (A:=CMfd.of (n:=n) U) IU hIU d hd
            (show IsCompact (cosupport n univ IU d) from hKU) (H:=HU) (E:=EU) hLocal hcount
        have hS' : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → B) MP) S := by
          simpa only [←hMU] using hS
        obtain ⟨D,Q,e,hQ,hiso⟩ := extend MP hwP.isClosedSubmanifold_N hIP hKP U hU S hS'
        let AQ := geoTransformAlong MP Q
        let BS := geoTransformAlong MU S
        let g : C → D := fun z => (e z).val
        have hg : IsOpenHoloEmbedding n g := ⟨openPreimage Q U,e,fun _ => rfl⟩
        have hQU := isGeoTestTower_restrict U hwP.isClosedSubmanifold_N hIP Q hQ
        have hN_U : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : U → B) MP).N := by
          change IsClosedSubmanifold n ((Subtype.val : U → B) ⁻¹' MP.N)
          rw [hNP,preimage_univ]
          exact HomogenizedGlueingTower.isClosedSubmanifold_univ
        have hI_U : (MarkedIdeal.pullback (Subtype.val : U → B) MP).ideal.IsCoherent := hIU
        have hBS : BS=MarkedIdeal.pullback e
            (MarkedIdeal.pullback (Subtype.val : openPreimage Q U → D) AQ) := by
          have heq := IsTowerIso.geoTransformAlong_eq
            (X:=CMfd.of (n:=n) U) (X':=CMfd.of (n:=n) U)
            (𝔪:=MarkedIdeal.pullback (Subtype.val : U → B) MP) (T':=S) (T:=restrict U Q) (χ:=e)
            (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) hN_U hI_U hiso hQU
          change geoTransformAlong (MarkedIdeal.pullback (id : U → U)
            (MarkedIdeal.pullback (Subtype.val : U → B) MP)) S = _ at heq
          rw [ContactCanonicalAlong.pullback_id _ hI_U,
            geoTransformAlong_restrict U hwP.isClosedSubmanifold_N hIP Q hQ] at heq
          simpa only [←hMU] using heq
        have hAQI : AQ.ideal.IsCoherent :=
          (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwP.isClosedSubmanifold_N hIP Q hQ).2
        have hcos : BS.cosupp=g ⁻¹' AQ.cosupp := by
          rw [hBS,MarkedIdealTowerTransport.cosupp_pullback_eq
            (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hAQI),
            cosupp_pullback_val AQ (fun _ _ hf =>
              RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hAQI hf)]
          rfl
        have hBE : BS.E=AQ.E.map (g ⁻¹' ·) := by
          rw [hBS]
          change (AQ.E.map (fun L => (Subtype.val : openPreimage Q U → D) ⁻¹' L)).map
            (e ⁻¹' ·)=AQ.E.map (g ⁻¹' ·)
          rw [List.map_map]
          rfl
        have hcover : AQ.cosupp ⊆ Set.range g := by
          intro y hy
          have hyU : Q.proj y∈U := hU
            ((current_cosupport_compact_of_wellFormed MP hwP hKP Q hQ).2 hy)
          exact ⟨e.symm ⟨y,hyU⟩,by simp only [g,e.apply_symm_apply]⟩
        have hStrict : strictAlong S HU=g ⁻¹' strictAlong Q (strictAlong P H) := by
          have heq := hiso.strictAlong_eq HU
          change strictAlong S HU=e ⁻¹' strictAlong (restrict U Q) HU at heq
          rw [strictAlong_restrict] at heq
          exact heq
        have hSV' : IsBoundaryAdaptedCarrier (n := n)
            ((Subtype.val : V → C) ⁻¹' (g ⁻¹' strictAlong Q (strictAlong P H)))
            (BS.E.map (fun L => (Subtype.val : V → C) ⁻¹' L)) := by
          simpa only [hStrict] using hSV
        have hOne' : ∀ v : V,
            branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hSV') v≤1 := by
          intro v
          have heq := count_congr (isNormalCrossingsCarrier_of_boundaryAdapted hSV)
            (isNormalCrossingsCarrier_of_boundaryAdapted hSV')
            (congrArg (fun L => (Subtype.val : V → C) ⁻¹' L) hStrict) v
          rw [←heq]
          exact hOne v
        obtain ⟨W,hW,hFinal,hFinalCount⟩ := transport_open_bound AQ BS hg hcover hcos hBE
          (strictAlong Q (strictAlong P H)) V hV hSV' hOne'
        refine ⟨D,P.append Q,(isGeoTestTower_append_iff M P Q).mpr ⟨hP,hQ⟩,?_⟩
        simpa only [geoTransformAlong_append,MemberInterLocusAlong.strictAlong_append] using
          (show ∃ (W : Opens D),AQ.cosupp⊆W ∧
            ∃ hp : IsBoundaryAdaptedCarrier (n := n)
              ((Subtype.val : W → D) ⁻¹' strictAlong Q (strictAlong P H))
              (AQ.E.map (fun L => (Subtype.val : W → D) ⁻¹' L)),
              ∀ w : W,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hp) w≤1 from
            ⟨W,hW,hFinal,hFinalCount⟩)

/-- Original natural data internally supply a finite permitted prephase and a
literal whole-cosupport neighbourhood where the old trace is smooth and
transverse to the ENTIRE retained/born boundary. -/
theorem exists_original_finite_permitted_prephase
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1≤d)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E) :
    let M : MarkedIdeal n X := ⟨univ,E,I,d⟩
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),IsGeoTestTower M T ∧
      ∃ (V : Opens Y),(geoTransformAlong M T).cosupp⊆V ∧
        ∃ hp : IsBoundaryAdaptedCarrier (n := n)
          ((Subtype.val : V → Y) ⁻¹' strictAlong T H)
          ((geoTransformAlong M T).E.map (fun D => (Subtype.val : V → Y) ⁻¹' D)),
          (∀ v : V,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hp) v≤1) ∧
          IsClosedSubmanifold n ((Subtype.val : V → Y) ⁻¹' strictAlong T H) ∧
          NormalCrossings.IsTransverse n ((Subtype.val : V → Y) ⁻¹' strictAlong T H)
            ((geoTransformAlong M T).E.map (fun D => (Subtype.val : V → Y) ⁻¹' D)) ∧
          NormalCrossings.IsSNCDivisor n
            (((geoTransformAlong M T).E.map (fun D => (Subtype.val : V → Y) ⁻¹' D)) ++
              [(Subtype.val : V → Y) ⁻¹' strictAlong T H]) := by
  dsimp only
  have extend : OpenExtension.{u} n := by
    intro A M hN hcoh hcompact U hcover B S hS
    obtain ⟨D,Q,hQ,e,he⟩ := HironakaCompactCosupportOpenTowerExtension.exists_extension
      M hN hcoh hcompact U hcover S hS
    exact ⟨D,Q,e,hQ,he⟩
  obtain ⟨Y,T,hT,V,hV,hp,hcount⟩ := finite_prephase_of_open_extension extend n (A:=X) I hI d hd hK h
    (fun x => branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted h) x)
  exact ⟨Y,T,hT,V,hV,hp,hcount,
    isClosedSubmanifold_of_branchMultiplicity_le_one (isNormalCrossingsCarrier_of_boundaryAdapted hp) hcount,
    isTransverse_of_boundaryAdapted_count_le_one hp hcount,
    isSNCDivisor_append_original_of_count_le_one hp hcount⟩

/-- The original NC carrier itself supplies the empty retained-boundary input;
every literal born slot remains in the actual current record. -/
theorem exists_original_nc_finite_permitted_prephase
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1≤d)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) :
    let M : MarkedIdeal n X := ⟨univ,[],I,d⟩
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),IsGeoTestTower M T ∧
      ∃ (V : Opens Y),(geoTransformAlong M T).cosupp⊆V ∧
        ∃ hp : IsBoundaryAdaptedCarrier (n := n)
          ((Subtype.val : V → Y) ⁻¹' strictAlong T H)
          ((geoTransformAlong M T).E.map (fun D => (Subtype.val : V → Y) ⁻¹' D)),
          (∀ v : V,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hp) v≤1) ∧
          IsClosedSubmanifold n ((Subtype.val : V → Y) ⁻¹' strictAlong T H) ∧
          NormalCrossings.IsTransverse n ((Subtype.val : V → Y) ⁻¹' strictAlong T H)
            ((geoTransformAlong M T).E.map (fun D => (Subtype.val : V → Y) ⁻¹' D)) ∧
          NormalCrossings.IsSNCDivisor n
            (((geoTransformAlong M T).E.map (fun D => (Subtype.val : V → Y) ⁻¹' D)) ++
              [(Subtype.val : V → Y) ⁻¹' strictAlong T H]) :=
  exists_original_finite_permitted_prephase I hI d hd hK (boundaryAdapted_nil hH)

end
end Hironaka.HironakaNormalCrossingsPermittedFinitePrephase
