/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalBoundaryCanonicalPrincipalization
import Hironaka.Resolution.HironakaBoundaryRelativelyCompact

/-!
# Original local canonical principalization and the same smooth Cartesian stages

The stronger actual relatively compact driver supplies genuine CAN and terminal
witnesses for arbitrary original coherent, nonzero-along input and initial SNC
boundary. The same chosen target precedes every arbitrary smooth source.
Neither zero-locus/source compactness nor a functorial choice of neighbourhood
is required. Blueprint: `hironaka-original-local-canonical-principalization-extension.tex`.
-/

set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalLocalCanonicalPrincipalization
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings RestrictEmptyTower DivisorExponentAlong CanonicalCentres
  HironakaAdmissibleSequence HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionOrderedChoiceBaseChange
  MarkedIdealBiholomorphism
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X D : CMfd.{u} n}

/-- Whole actual terminal geometry; actual terminality is internally supplied
by the original-input existence theorems below. -/
theorem terminal_principalization_geometry (M : MarkedIdeal n X)
    (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1)
    (F : Set X) (hZ : M.ideal.zeroLocus = F) (T : BlowupTower X D)
    (hr : IsGeoResolution M T) :
    CentresOver F T ∧
      IsAdmissibleBlowupSequence n X M.E F D T.proj (geoTransformAlong M T).E ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      GermIdeal.pullback (m := n) T.proj M.ideal = (exceptionalDivisor T).ideal ∧
      (exceptionalDivisor T).support = T.proj ⁻¹' F ∧
      (exceptionalDivisor T).support = ⋃ H ∈ (geoTransformAlong M T).E.drop M.E.length, H ∧
      exceptionalLocus n T.proj ⊆ (exceptionalDivisor T).support ∧
      IsIsomorphismOver n T.proj Fᶜ ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj := by
  have hI := hM.isWellFormed.isCoherent
  have hcos : M.cosupp = M.ideal.zeroLocus := by
    change GermIdealOrder.cosupport n M.N M.ideal M.d = _
    rw [hN,hd,GermIdealOrder.cosupport_one
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg),univ_inter]
  have hover : CentresOver M.ideal.zeroLocus T := by
    rw [← hcos]
    exact centresOver_cosupp M hM.isWellFormed.isClosedSubmanifold_N hI T hr.1
  have hpb : GermIdeal.pullback (m := n) T.proj M.ideal = (exceptionalDivisor T).ideal :=
    pullback_eq_exceptionalDivisor_of_isGeoResolution M hN hI hd T hr
  have hsupp : (exceptionalDivisor T).support = T.proj ⁻¹' M.ideal.zeroLocus := by
    rw [EffectiveDivisor.support,← hpb,BlowupExceptionalDivisor.zeroLocus_pullback T.contMDiff_proj hI]
  have hiso : IsIsomorphismOver n T.proj M.ideal.zeroLocusᶜ := by
    refine HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      T.isBlowupSequence ?_
    rintro x ⟨z,hz,rfl⟩
    have hz' := HironakaPrincipalization.exceptionalLocus_subset_support T hz
    rw [hsupp] at hz'
    exact hz'
  rw [hZ] at hover hsupp hiso
  exact ⟨hover,isAdmissibleBlowupSequence_proj M F T hr.1 hover,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hr.1).isWellFormed.isSNCDivisor,
    hpb,hsupp,HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop
      M hM.isWellFormed.isSNCDivisor.1 T,HironakaPrincipalization.exceptionalLocus_subset_support T,
    hiso,T.contMDiff_proj,HironakaLocalPrincipalization.isProperMap_proj T,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence⟩

/-- A prescribed original open contained in a compact set has an actual CAN
terminal principalization, chosen BEFORE every genuine smooth source. -/
theorem exists_canonical_boundary_principalization_of_subset_isCompact
    (I : GermIdeal n X) (hI : I.IsCoherent) (hne : ∀ x, IsNonzeroAlongAt univ I x)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (U : Opens X) {L : Set X} (hL : IsCompact L) (hUL : (U : Set X) ⊆ L) :
    let M₀ : MarkedIdeal n X := ⟨univ,E₀,I,1⟩
    let M := MarkedIdeal.pullback (Subtype.val : U → X) M₀
    let F := (Subtype.val : U → X) ⁻¹' I.zeroLocus
    ∃ (D : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) D),
      IsInvDomain n M ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T ∧
      CentresOver F T ∧
      IsAdmissibleBlowupSequence n U (E₀.map ((Subtype.val : U → X) ⁻¹' ·))
        F D T.proj (geoTransformAlong M T).E ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      GermIdeal.pullback (m := n) T.proj M.ideal = (exceptionalDivisor T).ideal ∧
      (exceptionalDivisor T).support = T.proj ⁻¹' F ∧
      (exceptionalDivisor T).support = ⋃ H ∈ (geoTransformAlong M T).E.drop E₀.length, H ∧
      exceptionalLocus n T.proj ⊆ (exceptionalDivisor T).support ∧
      IsIsomorphismOver n T.proj Fᶜ ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧
      ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → U),
        Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b →
        let N := markedPullback (m := m) b M
        ∃ (C : CMfd.{u} m) (Q : BlowupTower Y C) (g : C → D),
          IsActualTowerPullback b Q T g ∧ IsInvDomain m N ∧
          N.N = univ ∧ N.E = M.E.map (b ⁻¹' ·) ∧
          N.ideal = GermIdeal.pullback (m := m) b M.ideal ∧ N.d = 1 ∧
          Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
          Q.length = T.length ∧ (∀ z, T.proj (g z) = b (Q.proj z)) ∧
          HolomorphicSquarePullback b g Q.proj T.proj ∧
          IsCanonical N ((canonicalInvariant m).inv N) Q ∧ IsGeoResolution N Q ∧
          CentresOver (b ⁻¹' F) Q ∧
          IsAdmissibleBlowupSequence m Y N.E (b ⁻¹' F) C Q.proj (geoTransformAlong N Q).E ∧
          IsSNCDivisor m (geoTransformAlong N Q).E ∧
          (geoTransformAlong N Q).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) ∧
          GermIdeal.pullback (m := m) Q.proj N.ideal = (exceptionalDivisor Q).ideal ∧
          (exceptionalDivisor Q).support = Q.proj ⁻¹' (b ⁻¹' F) ∧
          (exceptionalDivisor Q).support = ⋃ H ∈ (geoTransformAlong N Q).E.drop E₀.length, H ∧
          exceptionalLocus m Q.proj ⊆ (exceptionalDivisor Q).support ∧
          IsIsomorphismOver m Q.proj (b ⁻¹' F)ᶜ ∧
          ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ Q.proj ∧
          IsProperMap Q.proj ∧ Surjective Q.proj := by
  dsimp only
  let M₀ : MarkedIdeal n X := ⟨univ,E₀,I,1⟩
  let M := MarkedIdeal.pullback (Subtype.val : U → X) M₀
  let F := (Subtype.val : U → X) ⁻¹' I.zeroLocus
  have hM₀ : IsInvDomain n M₀ :=
    HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor hI hne hE₀
  have hM : IsInvDomain n M := InvDomainTowerAlong.isInvDomain_pullback_val U hM₀
  have hZ : M.ideal.zeroLocus = F :=
    BlowupExceptionalDivisor.zeroLocus_pullback contMDiff_subtype_val hI
  obtain ⟨D,T,hcan,hres⟩ := HironakaRelativelyCompact.exists_isCanonical_resolution_of_subset_isCompact
    (canonicalInvariant n) hM₀ hL U hUL
  obtain ⟨hover,hadm,hsnc,hpb,hsupp,hborn,hexc,hiso,hhol,hproper,hsurj⟩ :=
    terminal_principalization_geometry M hM rfl rfl F hZ T hres
  have hlen : M.E.length = E₀.length := List.length_map _
  rw [hlen] at hborn
  refine ⟨D,T,hM,hcan,hres,hover,hadm,hsnc,hpb,hsupp,hborn,hexc,hiso,hhol,hproper,hsurj,?_⟩
  intro m Y b hb
  let N := markedPullback (m := m) b M
  have hN : IsInvDomain m N :=
    original_ambient_domain_pullback (X := CMfd.of (n := n) U) (Y := Y) hb M hM
  obtain ⟨C,Q,g,hactual⟩ := exists_actual_tower hb T
  obtain ⟨htQ,hrecord⟩ :=
    HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
      hactual M hM.isWellFormed hres.1
  have hcQ := HironakaSmoothSubmersionOriginalAmbientCanonical.IsActualTowerPullback.original_ambient_canonical
    hactual M hM hcan
  have hrQ : IsGeoResolution N Q := by
    refine ⟨htQ,?_⟩
    rw [HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_cosupport_dictionary
      hactual M hM.isWellFormed hres.1,hres.2,preimage_empty]
  have hE : (geoTransformAlong N Q).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) :=
    congrArg MarkedIdeal.E hrecord
  have hNZ : N.ideal.zeroLocus = b ⁻¹' F :=
    (BlowupExceptionalDivisor.zeroLocus_pullback hb.contMDiff hM.isWellFormed.isCoherent).trans
      (congrArg (b ⁻¹' ·) hZ)
  obtain ⟨hoverQ,hadmQ,hsncQ,hpbQ,hsuppQ,hbornQ,hexcQ,hisoQ,hholQ,hproperQ,hsurjQ⟩ :=
    terminal_principalization_geometry N hN rfl rfl (b ⁻¹' F) hNZ Q hrQ
  have hlenN : N.E.length = E₀.length := (List.length_map _).trans hlen
  rw [hlenN] at hbornQ
  exact ⟨C,Q,g,hactual,hN,rfl,rfl,rfl,rfl,hactual.isSubmersion,hactual.length_eq,hactual.proj_comm,
    hactual.universal,hcQ,hrQ,hoverQ,hadmQ,hsncQ,hE,hpbQ,hsuppQ,hbornQ,hexcQ,hisoQ,
    hholQ,hproperQ,hsurjQ⟩

/-- An arbitrary compact set internally chooses ONE relatively compact original
neighbourhood and target CAN terminal tower before every smooth source.
No functorial choice between distinct neighbourhoods is asserted. -/
theorem exists_canonical_boundary_principalization_local
    (I : GermIdeal n X) (hI : I.IsCoherent) (hne : ∀ x, IsNonzeroAlongAt univ I x)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
    let M₀ : MarkedIdeal n X := ⟨univ,E₀,I,1⟩
    let M := MarkedIdeal.pullback (Subtype.val : U → X) M₀
    let F := (Subtype.val : U → X) ⁻¹' I.zeroLocus
    ∃ (D : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) D),
      IsInvDomain n M ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T ∧
      CentresOver F T ∧
      IsAdmissibleBlowupSequence n U (E₀.map ((Subtype.val : U → X) ⁻¹' ·))
        F D T.proj (geoTransformAlong M T).E ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      GermIdeal.pullback (m := n) T.proj M.ideal = (exceptionalDivisor T).ideal ∧
      (exceptionalDivisor T).support = T.proj ⁻¹' F ∧
      (exceptionalDivisor T).support = ⋃ H ∈ (geoTransformAlong M T).E.drop E₀.length, H ∧
      exceptionalLocus n T.proj ⊆ (exceptionalDivisor T).support ∧
      IsIsomorphismOver n T.proj Fᶜ ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧
      ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → U),
        Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b →
        let N := markedPullback (m := m) b M
        ∃ (C : CMfd.{u} m) (Q : BlowupTower Y C) (g : C → D),
          IsActualTowerPullback b Q T g ∧ IsInvDomain m N ∧
          N.N = univ ∧ N.E = M.E.map (b ⁻¹' ·) ∧
          N.ideal = GermIdeal.pullback (m := m) b M.ideal ∧ N.d = 1 ∧
          Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
          Q.length = T.length ∧ (∀ z, T.proj (g z) = b (Q.proj z)) ∧
          HolomorphicSquarePullback b g Q.proj T.proj ∧
          IsCanonical N ((canonicalInvariant m).inv N) Q ∧ IsGeoResolution N Q ∧
          CentresOver (b ⁻¹' F) Q ∧
          IsAdmissibleBlowupSequence m Y N.E (b ⁻¹' F) C Q.proj (geoTransformAlong N Q).E ∧
          IsSNCDivisor m (geoTransformAlong N Q).E ∧
          (geoTransformAlong N Q).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) ∧
          GermIdeal.pullback (m := m) Q.proj N.ideal = (exceptionalDivisor Q).ideal ∧
          (exceptionalDivisor Q).support = Q.proj ⁻¹' (b ⁻¹' F) ∧
          (exceptionalDivisor Q).support = ⋃ H ∈ (geoTransformAlong N Q).E.drop E₀.length, H ∧
          exceptionalLocus m Q.proj ⊆ (exceptionalDivisor Q).support ∧
          IsIsomorphismOver m Q.proj (b ⁻¹' F)ᶜ ∧
          ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ Q.proj ∧
          IsProperMap Q.proj ∧ Surjective Q.proj := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨U,hUo,hKU,hUc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  refine ⟨⟨U,hUo⟩,hKU,hUc,?_⟩
  exact exists_canonical_boundary_principalization_of_subset_isCompact
    I hI hne E₀ hE₀ ⟨U,hUo⟩ hUc subset_closure


end
end Hironaka.HironakaOriginalLocalCanonicalPrincipalization
