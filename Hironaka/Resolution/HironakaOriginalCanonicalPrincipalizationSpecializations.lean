/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalLocalCanonicalPrincipalization
import Hironaka.API2

/-!
# Canonical connected and germ-language principalization specializations

Natural original one-germ/pointwise-germ hypotheses are reduced by genuine
coherence and connected identity-principle theorems. The SAME actual canonical
target and every full smooth-source property are retained; no old existential
principalization witness is reused. Blueprint:
`hironaka-original-canonical-principalization-specializations-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCanonicalPrincipalizationSpecializations
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings RestrictEmptyTower DivisorExponentAlong CanonicalCentres
  HironakaAdmissibleSequence HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalTerminalFiniteIdentification HironakaSmoothSubmersionOriginalCompactTerminal
  HironakaSmoothSubmersionOriginalGlobalFinite HironakaSmoothSubmersionOriginalTerminalFunctor
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeControlledTower

open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower)

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

variable {n m : ℕ} {X D : CMfd.{u} n} {Y E : CMfd.{u} m}

open HironakaOriginalBoundaryCanonicalPrincipalization HironakaOriginalLocalCanonicalPrincipalization
  MarkedIdealBiholomorphism

/-- Explicit RESULT: the literal original chosen target and every full smooth
source, including finite/glued arrows and their entire comparison square. -/
def CanonicalBoundaryPrincipalizationSpec
    (I : GermIdeal n X) (hI : I.IsCoherent) (hne : ∀ x,IsNonzeroAlongAt univ I x)
    (hZ : IsCompact I.zeroLocus) (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) : Prop :=
  (
    let M : MarkedIdeal n X := ⟨univ,E₀,I,1⟩
    let hM := HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor hI hne hE₀
    let hK : IsCompact M.cosupp := (show M.cosupp = I.zeroLocus from cosupp_univ_one hI).symm ▸ hZ
    let P := compactCosupportCanonicalTower M hM hK
    let T := P.2.val
    let E := (geoTransformAlong M T).E
    IsCanonical M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T ∧
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧ CentresOver I.zeroLocus T ∧
      IsAdmissibleBlowupSequence n X E₀ I.zeroLocus P.1 T.proj E ∧
      GermIdeal.pullback (m := n) T.proj I = (exceptionalDivisor T).ideal ∧ IsSNCDivisor n E ∧
      (exceptionalDivisor T).support = ⋃ H ∈ E.drop E₀.length, H ∧
      (exceptionalDivisor T).support = T.proj ⁻¹' I.zeroLocus ∧
      exceptionalLocus n T.proj ⊆ (exceptionalDivisor T).support ∧
      IsIsomorphismOver n T.proj I.zeroLocusᶜ ∧
      ∃ η : originalTerminalManifold M hM ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ P.1,
        ∀ z, T.proj (η z) = originalTerminalGluedProjection M hM z ) ∧
  ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → X)
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b),
  (
    let M : MarkedIdeal n X := ⟨univ,E₀,I,1⟩
    let hM := HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor hI hne hE₀
    let hK : IsCompact M.cosupp := (show M.cosupp = I.zeroLocus from cosupp_univ_one hI).symm ▸ hZ
    let P := compactCosupportCanonicalTower M hM hK
    let T := P.2.val
    let hc := P.2.property.1
    let hr := P.2.property.2
    let N := markedPullback (m := m) b M
    let hN := original_ambient_domain_pullback hb M hM
    let Q := chosenActualTower defaultSmoothBlowupChoices hb T
    let S := Q.2.1
    let hS := originalFiniteSmoothSourceHistory_properties hb M hM T hc hr
    let g := terminalSmoothMap hb M hM S T hS.1 hc hS.2 hr
    let G := originalGlobalFiniteSmoothMap hb M hM S T hS.1 hc hS.2 hr
    let ηX := originalTerminalFiniteBiholomorphism M hM T hc hr
    let ηY := originalTerminalFiniteBiholomorphism N hN S hS.1 hS.2
    IsCanonical N ((canonicalInvariant m).inv N) S ∧ IsGeoResolution N S ∧
      GermIdeal.pullback (m := n) T.proj I = (exceptionalDivisor T).ideal ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      GermIdeal.pullback (m := m) S.proj (GermIdeal.pullback (m := m) b I) = (exceptionalDivisor S).ideal ∧
      IsSNCDivisor m (geoTransformAlong N S).E ∧
      (geoTransformAlong N S).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
      (∀ z, T.proj (g z) = b (S.proj z)) ∧ HolomorphicSquarePullback b g S.proj T.proj ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
      (∀ z, originalTerminalGluedProjection M hM (G z) = b (originalTerminalGluedProjection N hN z)) ∧
      HolomorphicSquarePullback b G (originalTerminalGluedProjection N hN) (originalTerminalGluedProjection M hM) ∧
      (∀ z, ηX (G z) = g (ηY z)) ∧
      (∀ z, T.proj (ηX z) = originalTerminalGluedProjection M hM z) ∧
      (∀ z, S.proj (ηY z) = originalTerminalGluedProjection N hN z) )

/-- Explicit RESULT: one actual local canonical target BEFORE every genuine
smooth source, retaining all whole original fields and elementary geometry. -/
def LocalCanonicalBoundaryPrincipalizationSpec
    (I : GermIdeal n X) (E₀ : List (Set X)) (U : Opens X) : Prop :=
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
          IsProperMap Q.proj ∧ Surjective Q.proj

/-- Genuine original canonical producers prove the full explicit result. -/
theorem canonical_spec_of_nonzeroAlong
    (I : GermIdeal n X) (hI : I.IsCoherent) (hne : ∀ x,IsNonzeroAlongAt univ I x)
    (hZ : IsCompact I.zeroLocus) (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) :
    CanonicalBoundaryPrincipalizationSpec I hI hne hZ E₀ hE₀ := by
  exact ⟨canonical_boundary_principalization I hI hne hZ E₀ hE₀,
    fun {m} Y b hb => canonical_boundary_principalization_smooth_base_change I hI hne hZ E₀ hE₀ hb⟩

/-- The connected coherent identity principle turns ONE actual nonzero germ
into nonzero-along at EVERY point, before any canonical tower is chosen. -/
theorem nonzeroAlong_of_nonzero_germ [ConnectedSpace X]
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hne : ∃ x g,I.mem x g ∧ ∃ᶠ y in 𝓝 x,g y ≠ 0) :
    ∀ x,IsNonzeroAlongAt univ I x := by
  intro x
  exact FactorizationDomain.isNonzeroAlongAt_of_not_le
    FactorizationDomain.isClosedConnectedSubmanifold_univ hI
    (Hironaka.not_le_vanishingIdeal_univ hne) x (mem_univ x)

/-- Original connected one-germ data give the SAME actual canonical target,
full original SNC boundary and ALL subsequent smooth-source properties. -/
theorem canonical_principalization_of_connected [ConnectedSpace X]
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hne : ∃ x g,I.mem x g ∧ ∃ᶠ y in 𝓝 x,g y ≠ 0)
    (hZ : IsCompact I.zeroLocus) (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) :
    CanonicalBoundaryPrincipalizationSpec I hI (nonzeroAlong_of_nonzero_germ I hI hne) hZ E₀ hE₀ :=
  canonical_spec_of_nonzeroAlong I hI (nonzeroAlong_of_nonzero_germ I hI hne) hZ E₀ hE₀

/-- Original compact ambient connected data derive actual compact cosupport
internally; the whole SNC boundary and same source family are retained. -/
theorem canonical_principalization_of_connected_compactSpace [CompactSpace X] [ConnectedSpace X]
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hne : ∃ x g,I.mem x g ∧ ∃ᶠ y in 𝓝 x,g y ≠ 0)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) :
    let hZ := (CodimOneSupport.isComplexAnalyticSubset_zeroLocus hI).isClosed.isCompact
    CanonicalBoundaryPrincipalizationSpec I hI (nonzeroAlong_of_nonzero_germ I hI hne) hZ E₀ hE₀ :=
  canonical_principalization_of_connected I hI hne
    (CodimOneSupport.isComplexAnalyticSubset_zeroLocus hI).isClosed.isCompact E₀ hE₀

/-- Exact original pointwise frequent-nonzero germs, compact zero locus and
original boundary supply the literal canonical tower and all smooth sources. -/
theorem canonical_principalization_of_germs
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hne : ∀ x,∃ g,I.mem x g ∧ ∃ᶠ y in 𝓝 x,g y ≠ 0)
    (hZ : IsCompact I.zeroLocus) (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) :
    CanonicalBoundaryPrincipalizationSpec I hI (Hironaka.forall_isNonzeroAlongAt_univ_iff.mpr hne)
      hZ E₀ hE₀ :=
  canonical_spec_of_nonzeroAlong I hI (Hironaka.forall_isNonzeroAlongAt_univ_iff.mpr hne) hZ E₀ hE₀

/-- Actual compact ambient pointwise germ data require no separate compact
zero locus premise and retain the full original SNC boundary. -/
theorem canonical_principalization_of_compactSpace [CompactSpace X]
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hne : ∀ x,∃ g,I.mem x g ∧ ∃ᶠ y in 𝓝 x,g y ≠ 0)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) :
    let hZ := (CodimOneSupport.isComplexAnalyticSubset_zeroLocus hI).isClosed.isCompact
    CanonicalBoundaryPrincipalizationSpec I hI (Hironaka.forall_isNonzeroAlongAt_univ_iff.mpr hne)
      hZ E₀ hE₀ :=
  canonical_principalization_of_germs I hI hne
    (CodimOneSupport.isComplexAnalyticSubset_zeroLocus hI).isClosed.isCompact E₀ hE₀

/-- Original germ-language prescribed-open data supply the actual canonical
local target BEFORE all smooth sources, without compact zero locus. -/
theorem canonical_principalization_of_subset_isCompact_germs
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hne : ∀ x,∃ g,I.mem x g ∧ ∃ᶠ y in 𝓝 x,g y ≠ 0)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (U : Opens X) {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    LocalCanonicalBoundaryPrincipalizationSpec I E₀ U :=
  exists_canonical_boundary_principalization_of_subset_isCompact I hI
    (Hironaka.forall_isNonzeroAlongAt_univ_iff.mpr hne) E₀ hE₀ U hK hUK

/-- One original compact set internally chooses an actual relatively compact
open and the same full local canonical source family, in germ language. -/
theorem canonical_principalization_local_germs
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hne : ∀ x,∃ g,I.mem x g ∧ ∃ᶠ y in 𝓝 x,g y ≠ 0)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X,K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
      LocalCanonicalBoundaryPrincipalizationSpec I E₀ U :=
  exists_canonical_boundary_principalization_local I hI
    (Hironaka.forall_isNonzeroAlongAt_univ_iff.mpr hne) E₀ hE₀ hK

end
end Hironaka.HironakaOriginalCanonicalPrincipalizationSpecializations
