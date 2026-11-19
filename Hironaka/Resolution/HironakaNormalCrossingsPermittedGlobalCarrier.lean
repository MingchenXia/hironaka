/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsPermittedFinitePrephase

/-!
# Global old/born NC geometry through the actual finite permitted prephase

Two actual opens retain the complete global old carrier and current boundary.
The original-input finite induction constructs every phase and every genuine
ambient extension. Old simplicity is asserted only on the actual open containing
the whole current controlled cosupport. Intermediate old-branch centre
admissibility and general-NC canonical naturality remain separate obligations.
Blueprint: `hironaka-normal-crossings-permitted-global-carrier-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsPermittedGlobalCarrier
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MemberInterTowerAlong GermIdealOrder
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HironakaBaseChange HironakaNormalCrossingsLocalBranches
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaNormalCrossingsBoundarySeparation
  HironakaNormalCrossingsPermittedCountDrop HironakaNormalCrossingsPermittedFinitePrephase
  HironakaNormalCrossingsGlobalPhaseCarrier HironakaNormalCrossingsBiholomorphicMultiplicity
  BlowupTowerIsomorphism RestrictEmptyTower
variable {n : ℕ} {X Y Z : CMfd.{u} n}

private theorem record_eq_of_extension (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent) (U : Opens X)
    (S : BlowupTower (CMfd.of (n:=n) U) Z) (Q : BlowupTower X Y)
    (hQ : IsGeoTestTower M Q)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) S (restrict U Q) e) :
    geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) S=
      MarkedIdeal.pullback e
        (MarkedIdeal.pullback (Subtype.val : openPreimage Q U → Y) (geoTransformAlong M Q)) := by
  have hNU : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : U → X) M).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hIU : (MarkedIdeal.pullback (Subtype.val : U → X) M).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI
  have hr := IsTowerIso.geoTransformAlong_eq
    (X:=CMfd.of (n:=n) U) (X':=CMfd.of (n:=n) U)
    (𝔪:=MarkedIdeal.pullback (Subtype.val : U → X) M) (T':=S) (T:=restrict U Q) (χ:=e)
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) hNU hIU he
    (isGeoTestTower_restrict U hN hI Q hQ)
  change geoTransformAlong (MarkedIdeal.pullback (id : U → U)
    (MarkedIdeal.pullback (Subtype.val : U → X) M)) S = _ at hr
  rw [ContactCanonicalAlong.pullback_id _ hIU,geoTransformAlong_restrict U hN hI Q hQ] at hr
  exact hr

private theorem boundaryAdapted_of_actual_extension (M : MarkedIdeal n X)
    (hw : M.IsWellFormed) {H : Set X}
    (h : IsBoundaryAdaptedCarrier (n:=n) H M.E) (U : Opens X) (hU : M.cosupp⊆U)
    (S : BlowupTower (CMfd.of (n:=n) U) Z) (Q : BlowupTower X Y)
    (hQ : IsGeoTestTower M Q)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) S (restrict U Q) e)
    (hS : IsBoundaryAdaptedCarrier (n:=n)
      (strictAlong S ((Subtype.val : U → X) ⁻¹' H))
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) S).E) :
    IsBoundaryAdaptedCarrier (n:=n) (strictAlong Q H) (geoTransformAlong M Q).E := by
  have hwQ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw Q hQ
  have hr := record_eq_of_extension M hw.isClosedSubmanifold_N hw.isCoherent U S Q hQ e he
  have hs := he.strictAlong_eq ((Subtype.val : U → X) ⁻¹' H)
  change strictAlong S ((Subtype.val : U → X) ⁻¹' H)=
    e ⁻¹' strictAlong (restrict U Q) ((Subtype.val : U → X) ⁻¹' H) at hs
  rw [strictAlong_restrict] at hs
  have hbackH : e.symm ⁻¹' strictAlong S ((Subtype.val : U → X) ⁻¹' H)=
      (Subtype.val : openPreimage Q U → Y) ⁻¹' strictAlong Q H := by
    rw [hs]
    ext p
    simp only [mem_preimage,e.apply_symm_apply]
  have hbackE : (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) S).E.map
      (e.symm ⁻¹' ·)=(geoTransformAlong M Q).E.map
        (fun D => (Subtype.val : openPreimage Q U → Y) ⁻¹' D) := by
    rw [hr]
    change (((geoTransformAlong M Q).E.map
      (fun D => (Subtype.val : openPreimage Q U → Y) ⁻¹' D)).map (e ⁻¹' ·)).map
        (e.symm ⁻¹' ·)=_
    rw [List.map_map,List.map_map]
    apply List.map_congr_left
    intro D _hD
    ext p
    change (e (e.symm p)).val∈D ↔ p.val∈D
    rw [e.apply_symm_apply]
  have hInside := boundaryAdapted_preimage e.symm.contMDiff
    (MarkedIdealTowerTransport.notMem_exceptionalLocus e.symm) hS
  rw [hbackH,hbackE] at hInside
  let Uout : Opens X := ⟨M.cosuppᶜ,(GiraudAlong.isClosed_cosupport_along hw.isCoherent
    hw.isClosedSubmanifold_N M.d).isOpen_compl⟩
  have hEmpty := isEmptyTower_restrict_of_centresOver Uout
    (show Disjoint (Uout : Set X) M.cosupp from disjoint_compl_left) Q
    (HironakaAdmissibleSequence.centresOver_cosupp M hw.isClosedSubmanifold_N hw.isCoherent Q hQ)
  have hOutside := boundaryAdapted_empty_tower
    (MarkedIdeal.pullback (Subtype.val : Uout → X) M) (boundaryAdapted_open Uout h)
    (restrict Uout Q) hEmpty
  rw [strictAlong_restrict,geoTransformAlong_restrict Uout hw.isClosedSubmanifold_N
    hw.isCoherent Q hQ] at hOutside
  apply boundaryAdapted_of_open_traces (isClosed_strictAlong Q h.1) hwQ.isSNCDivisor.1
  intro y
  by_cases hy : Q.proj y∈U
  · exact ⟨openPreimage Q U,hy,hInside⟩
  · have hyout : Q.proj y∈Uout := fun hyc => hy (hU hyc)
    exact ⟨openPreimage Q Uout,hyout,hOutside⟩

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

private theorem finite_global_prephase (r : ℕ) :
    ∀ {A : CMfd.{u} n} (I : GermIdeal n A) (_hI : I.IsCoherent)
      (d : ℕ) (_hd : 1≤d) (_hK : IsCompact (cosupport n univ I d))
      {H : Set A} {E : List (Set A)} (h : IsBoundaryAdaptedCarrier (n := n) H E),
      (∀ x : A,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x≤r) →
      ∃ (B : CMfd.{u} n) (T : BlowupTower A B),
        IsGeoTestTower (⟨univ,E,I,d⟩ : MarkedIdeal n A) T ∧
        IsBoundaryAdaptedCarrier (n:=n) (strictAlong T H)
          (geoTransformAlong (⟨univ,E,I,d⟩ : MarkedIdeal n A) T).E ∧
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
        refine ⟨A,.refl,trivial,h,V,subset_univ _,hp,?_⟩
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
        obtain ⟨C,S,hS,hGlobalS,V,hV,hSV,hOne⟩ :=
          ih (r-1) (by omega) (A:=CMfd.of (n:=n) U) IU hIU d hd
            (show IsCompact (cosupport n univ IU d) from hKU) (H:=HU) (E:=EU) hLocal hcount
        have hS' : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → B) MP) S := by
          simpa only [←hMU] using hS
        obtain ⟨D,Q,hQ,e,hiso⟩ := HironakaCompactCosupportOpenTowerExtension.exists_extension
          MP hwP.isClosedSubmanifold_N hIP hKP U hU S hS'
        have hGlobalS' : IsBoundaryAdaptedCarrier (n:=n)
            (strictAlong S ((Subtype.val : U → B) ⁻¹' strictAlong P H))
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → B) MP) S).E := by
          simpa only [←hMU] using hGlobalS
        have hGlobalQ := boundaryAdapted_of_actual_extension MP hwP hPair U hU S Q hQ e hiso hGlobalS'
        let AQ := geoTransformAlong MP Q
        let BS := geoTransformAlong MU S
        let g : C → D := fun z => (e z).val
        have hg : IsOpenHoloEmbedding n g := ⟨openPreimage Q U,e,fun _ => rfl⟩
        have hBS : BS=MarkedIdeal.pullback e
            (MarkedIdeal.pullback (Subtype.val : openPreimage Q U → D) AQ) := by
          simpa only [←hMU] using record_eq_of_extension MP hwP.isClosedSubmanifold_N hIP U S Q hQ e hiso
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
        have hGlobal : IsBoundaryAdaptedCarrier (n:=n) (strictAlong (P.append Q) H)
            (geoTransformAlong M (P.append Q)).E := by
          simpa only [geoTransformAlong_append,MemberInterLocusAlong.strictAlong_append] using hGlobalQ
        refine ⟨D,P.append Q,(isGeoTestTower_append_iff M P Q).mpr ⟨hP,hQ⟩,hGlobal,?_⟩
        simpa only [geoTransformAlong_append,MemberInterLocusAlong.strictAlong_append] using
          (show ∃ (W : Opens D),AQ.cosupp⊆W ∧
            ∃ hp : IsBoundaryAdaptedCarrier (n := n)
              ((Subtype.val : W → D) ⁻¹' strictAlong Q (strictAlong P H))
              (AQ.E.map (fun L => (Subtype.val : W → D) ⁻¹' L)),
              ∀ w : W,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hp) w≤1 from
            ⟨W,hW,hFinal,hFinalCount⟩)

/-- Original natural data internally supply a finite permitted prephase and a
GLOBAL adapted current pair and a literal whole-cosupport neighbourhood where the old trace is smooth and
transverse to the ENTIRE retained/born boundary. -/
theorem exists_original_global_finite_permitted_prephase
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1≤d)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E) :
    let M : MarkedIdeal n X := ⟨univ,E,I,d⟩
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),IsGeoTestTower M T ∧
      IsBoundaryAdaptedCarrier (n:=n) (strictAlong T H) (geoTransformAlong M T).E ∧
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
  obtain ⟨Y,T,hT,hGlobal,V,hV,hp,hcount⟩ := finite_global_prephase n (A:=X) I hI d hd hK h
    (fun x => branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted h) x)
  exact ⟨Y,T,hT,hGlobal,V,hV,hp,hcount,
    isClosedSubmanifold_of_branchMultiplicity_le_one (isNormalCrossingsCarrier_of_boundaryAdapted hp) hcount,
    isTransverse_of_boundaryAdapted_count_le_one hp hcount,
    isSNCDivisor_append_original_of_count_le_one hp hcount⟩

/-- The original NC carrier itself supplies the empty retained-boundary input;
every literal born slot remains in the actual current record. -/
theorem exists_original_nc_global_finite_permitted_prephase
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1≤d)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) :
    let M : MarkedIdeal n X := ⟨univ,[],I,d⟩
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),IsGeoTestTower M T ∧
      IsBoundaryAdaptedCarrier (n:=n) (strictAlong T H) (geoTransformAlong M T).E ∧
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
  exists_original_global_finite_permitted_prephase I hI d hd hK (boundaryAdapted_nil hH)


end
end Hironaka.HironakaNormalCrossingsPermittedGlobalCarrier
