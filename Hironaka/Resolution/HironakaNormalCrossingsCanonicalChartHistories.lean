/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaHomogeneousCanonicalNeighbourhoods

/-! # Actual general-NC canonical prefixes in whole coordinate models

Original charts and actual whole-history comparisons are constructed internally.
An empty original centre trace selects a real empty model step; otherwise whole
values over every origin neighbourhood identify the genuine ENTIRE model maximum.
No present-incidence surrogate or desired history certificate is assumed.
Blueprint: `hironaka-normal-crossings-canonical-chart-histories-extension.tex`.
-/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaNormalCrossingsCanonicalChartHistories

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionInvariantSeq ResolutionDriver
  HironakaHomogeneousCanonicalTowerMaxima HironakaHomogeneousCanonicalNeighbourhoods
  HironakaNormalCrossingsMarkedAdmissibility HironakaNormalCrossingsTotalIdeal
  HironakaNormalCrossingsInitialFullMaximum HironakaNormalCrossingsLocalBranches
  HironakaNormalCrossingsBiholomorphicMultiplicity HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsFirstStepChartHistory BlowupFlatCoordinates
  BlowupTowerIsomorphism MarkedIdealBiholomorphism

noncomputable section
variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ] {A B D : CMfd.{u} n}

private theorem original_pullback_open {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (U : TopologicalSpace.Opens A) :
    MarkedIdeal.pullback (Subtype.val : U → A) (originalMarkedIdeal H) =
      originalMarkedIdeal (A := CMfd.of (n := n) U) ((Subtype.val : U → A) ⁻¹' H) := by
  have hp := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open U (boundaryAdapted_nil hH))
  have hc : (vanishingIdeal (n := n) ((Subtype.val : U → A) ⁻¹' H)).IsCoherent :=
    (isInvDomain_originalMarkedIdeal (A := CMfd.of (n := n) U) hp).isWellFormed.isCoherent
  have hi := BlowupRestrictOpen.pullback_vanishingIdeal_opens (n := n) (m := n) U (id : U → U) H
  rw [BlowupControlledTransform.pullback_id hc] at hi
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    (𝔪 := MarkedIdeal.pullback (Subtype.val : U → A) (originalMarkedIdeal H))
    (𝔫 := originalMarkedIdeal (A := CMfd.of (n := n) U) ((Subtype.val : U → A) ⁻¹' H)) rfl rfl ?_ rfl
  change GermIdeal.pullback (m := n) (Subtype.val : U → A) (vanishingIdeal (n := n) H) =
    vanishingIdeal (n := n) ((Subtype.val : U → A) ⁻¹' H)
  simpa only [Function.comp_id] using hi.symm

private theorem original_pullback_diffeomorph
    (χ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    MarkedIdeal.pullback χ (originalMarkedIdeal H) = originalMarkedIdeal (χ ⁻¹' H) := by
  have hp := isNormalCrossingsCarrier_preimage χ.contMDiff
    (notMem_exceptionalLocus_of_inverse χ.contMDiff χ.symm.contMDiff
      χ.apply_symm_apply χ.symm_apply_apply) hH
  have hc : (vanishingIdeal (n := n) (χ ⁻¹' H)).IsCoherent :=
    (isInvDomain_originalMarkedIdeal hp).isWellFormed.isCoherent
  have hi := pullback_vanishingIdeal_preimage χ.contMDiff χ.symm.contMDiff
    χ.apply_symm_apply χ.symm_apply_apply (g := (id : B → B)) contMDiff_id H
  rw [BlowupControlledTransform.pullback_id hc] at hi
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    (𝔪 := MarkedIdeal.pullback χ (originalMarkedIdeal H))
    (𝔫 := originalMarkedIdeal (χ ⁻¹' H)) rfl rfl ?_ rfl
  change GermIdeal.pullback (m := n) χ (vanishingIdeal (n := n) H) = vanishingIdeal (n := n) (χ ⁻¹' H)
  simpa only [Function.comp_id] using hi.symm

/-- A genuine initial original NC chart, including the WHOLE marked record.
No higher-history data is part of this geometric chart. -/
structure OriginalCoordinateChart (H : Set A) (x : A) where
  S : Finset (Fin n)
  U : TopologicalSpace.Opens A
  hx : x ∈ U
  V : TopologicalSpace.Opens (CoordinateBase.{u} n)
  h0 : coordinateOrigin ∈ V
  map : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V
  pullback_record : MarkedIdeal.pullback map
      (MarkedIdeal.pullback (Subtype.val : V → CoordinateBase n) (coordinateMarked S)) =
    MarkedIdeal.pullback (Subtype.val : U → A) (originalMarkedIdeal H)

/-- Genuine NC coordinates internally produce an origin chart and WHOLE
original-record comparison at every original point. -/
theorem exists_original_coordinate_chart {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (x : A) :
    Nonempty (OriginalCoordinateChart H x) := by
  obtain ⟨Φ,hsrc,hzero,S,hflat⟩ := hH.2 x
  let U := chartOpen Φ
  let V : TopologicalSpace.Opens (CoordinateBase.{u} n) := coordinateOpen Φ
  let e := flatDomainDiffeomorph Φ hsrc
  have h0 : coordinateOrigin ∈ V := by
    have ht := Φ.mapsTo_toFun Φ.center_mem_source
    rw [hzero] at ht
    exact ht
  have hpre : e ⁻¹' ((Subtype.val : V → CoordinateBase n) ⁻¹' coordinateCarrier S) =
      (Subtype.val : U → A) ⁻¹' H := by
    ext p
    exact (hflat p p.2).symm
  have hmodel := coordinateCarrier_isNormalCrossings.{u} S
  have htrace := isNormalCrossingsCarrier_of_boundaryAdapted
    (boundaryAdapted_open V (boundaryAdapted_nil hmodel))
  have hrecord : MarkedIdeal.pullback e
      (MarkedIdeal.pullback (Subtype.val : V → CoordinateBase n) (coordinateMarked S)) =
      MarkedIdeal.pullback (Subtype.val : U → A) (originalMarkedIdeal H) := by
    change MarkedIdeal.pullback e
      (MarkedIdeal.pullback (Subtype.val : V → CoordinateBase n)
        (originalMarkedIdeal (A := CoordinateBase.{u} n) (coordinateCarrier S))) = _
    rw [original_pullback_open hmodel V]
    have hi := original_pullback_diffeomorph
      (A := CMfd.of (n := n) V) (B := CMfd.of (n := n) U) e htrace
    rw [hpre] at hi
    exact hi.trans (original_pullback_open hH U).symm
  exact ⟨⟨S,U,mem_flatDomain_self Φ,V,h0,e,hrecord⟩⟩

private theorem original_domain {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hnk : n ≤ k) :
    IsInvDomain k (originalMarkedIdeal H) := by
  have h := isInvDomain_originalMarkedIdeal hH
  refine ⟨h.isWellFormed,?_,h.one_le_d,h.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨d,hd,hreg⟩ := h.dimLE x hx
  exact ⟨d,hd.trans hnk,hreg⟩

private theorem model_domain (S : Finset (Fin n)) (hnk : n ≤ k) :
    IsInvDomain k (coordinateMarked.{u} S) :=
  original_domain (A := CoordinateBase.{u} n) (coordinateCarrier_isNormalCrossings.{u} S) hnk

private theorem OriginalCoordinateChart.model_domain {H : Set A} {x : A}
    (Q : OriginalCoordinateChart H x) (hnk : n ≤ k) :
    IsInvDomain k (MarkedIdeal.pullback (Subtype.val : Q.V → CoordinateBase n) (coordinateMarked Q.S)) := by
  change IsInvDomain k (MarkedIdeal.pullback (Subtype.val : Q.V → CoordinateBase n)
    (originalMarkedIdeal (A := CoordinateBase.{u} n) (coordinateCarrier Q.S)))
  rw [original_pullback_open (coordinateCarrier_isNormalCrossings.{u} Q.S) Q.V]
  exact original_domain (isNormalCrossingsCarrier_of_boundaryAdapted
    (boundaryAdapted_open Q.V (boundaryAdapted_nil (coordinateCarrier_isNormalCrossings.{u} Q.S)))) hnk

/-- Actual whole-history naturality compares the actual original and model
cosupports and ENTIRE values at their actual corresponding chart points. -/
theorem chart_history_cosupp_value
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n ≤ k)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) {x : A}
    (Q : OriginalCoordinateChart H x) (T : BlowupTower A D)
    (hcan : IsCanonical (originalMarkedIdeal H) (R.inv (originalMarkedIdeal H)) T)
    {Z : CMfd.{u} n} (W : BlowupTower (CoordinateBase.{u} n) Z)
    (hmodel : IsCanonical (coordinateMarked Q.S) (R.inv (coordinateMarked Q.S)) W)
    (e : CMfd.of (n := n) (openPreimage T Q.U)
      ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage W Q.V))
    (hiso : IsTowerIso Q.map (restrict Q.U T) (restrict Q.V W) e)
    (p : openPreimage T Q.U) :
    ((p : D) ∈ (geoTransformAlong (originalMarkedIdeal H) T).cosupp ↔
      ((e p : openPreimage W Q.V) : Z) ∈ (geoTransformAlong (coordinateMarked Q.S) W).cosupp) ∧
    ((p : D) ∈ (geoTransformAlong (originalMarkedIdeal H) T).cosupp →
      R.inv (originalMarkedIdeal H) T p = R.inv (coordinateMarked Q.S) W (e p)) := by
  have hdom := original_domain hH hnk
  have hdomM := model_domain.{u} Q.S hnk
  have hdomV := Q.model_domain hnk
  have htest := R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan
  have htestM := R.isInvValue.isGeoTestTower_of_isCanonical hdomM W hmodel
  have hcanV := HironakaHomogeneousCanonicalNeighbourhoods.isCanonical_restrict R hnk Q.S W hmodel Q.V Q.h0
  have htestV := R.isInvValue.isGeoTestTower_of_isCanonical hdomV (restrict Q.V W) hcanV
  have hcosI := IsTowerIso.cosupp_geoTransformAlong Q.map hdomV.isWellFormed.isClosedSubmanifold_N
    hdomV.isWellFormed.isCoherent hiso htestV
  rw [Q.pullback_record] at hcosI
  have hcosO := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent Q.U T htest
  have hcosM := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hdomM.isWellFormed.isClosedSubmanifold_N hdomM.isWellFormed.isCoherent Q.V W htestM
  have hco : (p : D) ∈ (geoTransformAlong (originalMarkedIdeal H) T).cosupp ↔
      ((e p : openPreimage W Q.V) : Z) ∈ (geoTransformAlong (coordinateMarked Q.S) W).cosupp := by
    rw [hcosO,hcosM] at hcosI
    exact (congrArg (fun S => p ∈ S) hcosI).to_iff
  refine ⟨hco,fun hp => ?_⟩
  have hpM : e p ∈ (geoTransformAlong
      (MarkedIdeal.pullback (Subtype.val : Q.V → CoordinateBase n) (coordinateMarked Q.S))
      (restrict Q.V W)).cosupp := by
    rw [hcosM]
    exact hco.mp hp
  have hv := R.isInvValue.towerIso Q.map _ hdomV (restrict Q.U T) (restrict Q.V W) e hiso hcanV p hpM
  rw [Q.pullback_record] at hv
  have ho := R.isInvValue.restrictOpen (originalMarkedIdeal H) hdom Q.U T hcan p hp
  have hm := R.isInvValue.restrictOpen (coordinateMarked Q.S) hdomM Q.V W hmodel (e p) (hco.mp hp)
  exact ho.symm.trans (hv.trans hm)

private theorem centre_preimage_of_nonempty_trace
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n ≤ k)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) {x : A}
    (Q : OriginalCoordinateChart H x) (T : BlowupTower A D)
    {F : CMfd.{u} n} (C : Set D) (π : F → D) (hπ : IsBlowupAlong n C π)
    (hstep : IsCanonical (originalMarkedIdeal H) (R.inv (originalMarkedIdeal H)) (.step T C π hπ))
    {Z : CMfd.{u} n} (W : BlowupTower (CoordinateBase.{u} n) Z)
    (hmodel : IsCanonical (coordinateMarked Q.S) (R.inv (coordinateMarked Q.S)) W)
    (e : CMfd.of (n := n) (openPreimage T Q.U)
      ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage W Q.V))
    (hiso : IsTowerIso Q.map (restrict Q.U T) (restrict Q.V W) e)
    (hne : ((Subtype.val : openPreimage T Q.U → D) ⁻¹' C).Nonempty) :
    e ⁻¹' ((Subtype.val : openPreimage W Q.V → Z) ⁻¹'
      maxLocus (R.inv (coordinateMarked Q.S) W) (geoTransformAlong (coordinateMarked Q.S) W).cosupp) =
      (Subtype.val : openPreimage T Q.U → D) ⁻¹' C := by
  have hC : C = maxLocus (R.inv (originalMarkedIdeal H) T)
      (geoTransformAlong (originalMarkedIdeal H) T).cosupp := by
    rcases hstep.2 with hC | hC
    · obtain ⟨p,hp⟩ := hne
      simp only [hC,preimage_empty,notMem_empty] at hp
    · exact hC
  obtain ⟨p₀,hp₀⟩ := hne
  have hpmax : (p₀ : D) ∈ maxLocus (R.inv (originalMarkedIdeal H) T)
      (geoTransformAlong (originalMarkedIdeal H) T).cosupp := hC ▸ hp₀
  have hc₀ := chart_history_cosupp_value R hnk hH Q T hstep.1 W hmodel e hiso p₀
  have hm₀ : ((e p₀ : openPreimage W Q.V) : Z) ∈
      maxLocus (R.inv (coordinateMarked Q.S) W) (geoTransformAlong (coordinateMarked Q.S) W).cosupp := by
    refine ⟨hc₀.1.mp hpmax.1,fun z hz => ?_⟩
    obtain ⟨z',hzV,hzcos,hzval⟩ :=
      exists_value_representative_over_neighbourhood R hnk Q.S W hmodel Q.V Q.h0 z hz
    let q : openPreimage W Q.V := ⟨z',hzV⟩
    let p := e.symm q
    have hcp := chart_history_cosupp_value R hnk hH Q T hstep.1 W hmodel e hiso p
    have hpcos : (p : D) ∈ (geoTransformAlong (originalMarkedIdeal H) T).cosupp :=
      hcp.1.mpr (by simpa only [p,q,e.apply_symm_apply] using hzcos)
    have hpval : R.inv (originalMarkedIdeal H) T p = R.inv (coordinateMarked Q.S) W z' := by
      simpa only [p,q,e.apply_symm_apply] using hcp.2 hpcos
    calc
      R.inv (coordinateMarked Q.S) W z = R.inv (coordinateMarked Q.S) W z' := hzval.symm
      _ = R.inv (originalMarkedIdeal H) T p := hpval.symm
      _ ≤ R.inv (originalMarkedIdeal H) T p₀ := hpmax.2 p hpcos
      _ = R.inv (coordinateMarked Q.S) W (e p₀) := hc₀.2 hpmax.1
  ext p
  have hcp := chart_history_cosupp_value R hnk hH Q T hstep.1 W hmodel e hiso p
  constructor
  · intro hp
    have hpcos := hcp.1.mpr hp.1
    rw [hC]
    refine ⟨hpcos,fun z hz => ?_⟩
    calc
      R.inv (originalMarkedIdeal H) T z ≤ R.inv (originalMarkedIdeal H) T p₀ := hpmax.2 z hz
      _ = R.inv (coordinateMarked Q.S) W (e p₀) := hc₀.2 hpmax.1
      _ ≤ R.inv (coordinateMarked Q.S) W (e p) := hp.2 (e p₀) hm₀.1
      _ = R.inv (originalMarkedIdeal H) T p := (hcp.2 hpcos).symm
  · intro hp
    have hpmax' : (p : D) ∈ maxLocus (R.inv (originalMarkedIdeal H) T)
        (geoTransformAlong (originalMarkedIdeal H) T).cosupp := hC ▸ hp
    refine ⟨hcp.1.mp hpmax'.1,fun z hz => ?_⟩
    calc
      R.inv (coordinateMarked Q.S) W z ≤ R.inv (coordinateMarked Q.S) W (e p₀) := hm₀.2 z hz
      _ = R.inv (originalMarkedIdeal H) T p₀ := (hc₀.2 hpmax.1).symm
      _ ≤ R.inv (originalMarkedIdeal H) T p := hpmax'.2 p₀ hpmax.1
      _ = R.inv (coordinateMarked Q.S) W (e p) := hcp.2 hpmax'.1

/-- The actual original next step PRODUCES its real entire coordinate next step
and genuine whole chart-history lift. No next-centre/history certificate is input. -/
theorem exists_next_model_chart_history
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n ≤ k)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) {x : A}
    (Q : OriginalCoordinateChart H x) (T : BlowupTower A D)
    {F : CMfd.{u} n} (C : Set D) (π : F → D) (hπ : IsBlowupAlong n C π)
    (hstep : IsCanonical (originalMarkedIdeal H) (R.inv (originalMarkedIdeal H)) (.step T C π hπ))
    {Z : CMfd.{u} n} (W : BlowupTower (CoordinateBase.{u} n) Z)
    (hmodel : IsCanonical (coordinateMarked Q.S) (R.inv (coordinateMarked Q.S)) W)
    (e : CMfd.of (n := n) (openPreimage T Q.U)
      ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage W Q.V))
    (hiso : IsTowerIso Q.map (restrict Q.U T) (restrict Q.V W) e) :
    ∃ K : Set Z, ∃ Z' : CMfd.{u} n, ∃ σ : Z' → Z, ∃ hσ : IsBlowupAlong n K σ,
      IsCanonical (coordinateMarked Q.S) (R.inv (coordinateMarked Q.S)) (.step W K σ hσ) ∧
      ∃ e' : CMfd.of (n := n) (openPreimage (.step T C π hπ) Q.U)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (.step W K σ hσ) Q.V),
        IsTowerIso Q.map (restrict Q.U (.step T C π hπ)) (restrict Q.V (.step W K σ hσ)) e' := by
  have hK : ∃ K : Set Z,
      (K = ∅ ∨ K = maxLocus (R.inv (coordinateMarked Q.S) W) (geoTransformAlong (coordinateMarked Q.S) W).cosupp) ∧
      e ⁻¹' ((Subtype.val : openPreimage W Q.V → Z) ⁻¹' K) =
        (Subtype.val : openPreimage T Q.U → D) ⁻¹' C := by
    by_cases hne : ((Subtype.val : openPreimage T Q.U → D) ⁻¹' C).Nonempty
    · exact ⟨_,Or.inr rfl,centre_preimage_of_nonempty_trace R hnk hH Q T C π hπ hstep W hmodel e hiso hne⟩
    · exact ⟨∅,Or.inl rfl,by simp only [preimage_empty,not_nonempty_iff_eq_empty.mp hne]⟩
  obtain ⟨K,hKchoice,hcentre⟩ := hK
  have hdom := model_domain.{u} Q.S hnk
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical hdom W hmodel
  have hAdm : (geoTransformAlong (coordinateMarked Q.S) W).IsAdmissibleCentre K := by
    rcases hKchoice with hK | hK
    · rw [hK]
      exact MarkedIdeal.isAdmissibleCentre_empty _
    · rw [hK]
      exact R.isInvValue.isAdmissibleCentre_maxLocus hdom W hmodel ht
  have hInt : interior K = ∅ := by
    rcases hKchoice with hK | hK
    · simp only [hK,interior_empty]
    · rw [hK]
      exact ResolutionInvariantDriver.interior_maxLocus_eq_empty hdom W ht _
  obtain ⟨Z',hZtop,hZchart,hZcm,σ,hσ⟩ := BlowupExistence.exists_isBlowupAlong K hAdm.1 hInt
  let := hZtop
  let := hZchart
  let := hZcm
  let F' := CMfd.of (n := n) Z'
  have hσ' : IsBlowupAlong n K (σ : F' → Z) := hσ
  let W' : BlowupTower (CoordinateBase.{u} n) F' := .step W K σ hσ'
  have hπU := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ (openPreimage T Q.U)
  have hσV := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hσ' (openPreimage W Q.V)
  obtain ⟨e',hnew⟩ := exists_oneStep_isTowerIso
    (A := CMfd.of (n := n) (openPreimage T Q.U)) (B := CMfd.of (n := n) (openPreimage W Q.V))
    (D := CMfd.of (n := n) (openPreimage (.step T C π hπ) Q.U))
    (F := CMfd.of (n := n) (openPreimage W' Q.V)) e hπU hσV hcentre
  exact ⟨K,F',σ,hσ',⟨hmodel,hKchoice⟩,e',
    IsTowerIso.step hiso hπU hσV e' (fun p => (hnew.proj_comm p).symm) hcentre⟩

/-- The chart is fixed while the actual original prefix is followed. Entire
model histories and actual full comparison lifts are produced at every slot. -/
theorem exists_model_history_for_chart
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n ≤ k)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) {x : A}
    (Q : OriginalCoordinateChart H x) (T : BlowupTower A D)
    (hcan : IsCanonical (originalMarkedIdeal H) (R.inv (originalMarkedIdeal H)) T) :
    ∃ Z : CMfd.{u} n, ∃ W : BlowupTower (CoordinateBase.{u} n) Z,
      IsCanonical (coordinateMarked Q.S) (R.inv (coordinateMarked Q.S)) W ∧ W.length = T.length ∧
      ∃ e : CMfd.of (n := n) (openPreimage T Q.U)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage W Q.V),
        IsTowerIso Q.map (restrict Q.U T) (restrict Q.V W) e := by
  revert hcan
  induction T with
  | refl => exact fun _ => ⟨CoordinateBase n,.refl,trivial,rfl,Q.map,.refl⟩
  | @step Y F T C π hπ ih =>
    intro hstep
    obtain ⟨Z,W,hmodel,hlen,e,hiso⟩ := ih hstep.1
    obtain ⟨K,Z',σ,hσ,hmodel',e',hnew⟩ :=
      exists_next_model_chart_history R hnk hH Q T C π hπ hstep W hmodel e hiso
    exact ⟨Z',.step W K σ hσ,hmodel',congrArg (·+1) hlen,e',hnew⟩

/-- Original general-NC geometry and the actual original CAN prefix internally
produce a genuine original chart, SAME-length entire model prefix and full actual
restricted-history isomorphism. No incoming model/history certificate is assumed. -/
theorem exists_original_nc_chart_model_history
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n ≤ k)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) (T : BlowupTower A D)
    (hcan : IsCanonical (originalMarkedIdeal H) (R.inv (originalMarkedIdeal H)) T) (x : A) :
    ∃ Q : OriginalCoordinateChart H x, ∃ Z : CMfd.{u} n,
      ∃ W : BlowupTower (CoordinateBase.{u} n) Z,
        IsCanonical (coordinateMarked Q.S) (R.inv (coordinateMarked Q.S)) W ∧ W.length = T.length ∧
        ∃ e : CMfd.of (n := n) (openPreimage T Q.U)
          ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage W Q.V),
          IsTowerIso Q.map (restrict Q.U T) (restrict Q.V W) e := by
  obtain ⟨Q⟩ := exists_original_coordinate_chart hH x
  exact ⟨Q,exists_model_history_for_chart R hnk hH Q T hcan⟩

end
end Hironaka.HironakaNormalCrossingsCanonicalChartHistories
