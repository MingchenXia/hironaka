/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalFinite

/-!
# The original compact canonical tower as elementary principalization

The literal original marked record is `(X, X, [], I, 1)`.  Its actual
compact canonical tower supplies both the elementary whole-ideal dictionary
and the finite identification with the original global terminal manifold.
The same tower admits a genuine arbitrary smooth Cartesian base change;
the source need not be compact and no source history is an input.

This concerns full terminal ideal principalization.  It does not identify
the stopped prefix used for embedded resolution with the full terminal map.
Blueprint: `hironaka-original-canonical-elementary-principalization-extension.tex`.
-/

set_option autoImplicit false

open Set Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalCanonicalElementaryPrincipalization

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings RestrictEmptyTower DivisorExponentAlong CanonicalCentres
  HironakaAdmissibleSequence HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalTerminalFiniteIdentification HironakaSmoothSubmersionOriginalCompactTerminal
  HironakaSmoothSubmersionOriginalGlobalFinite HironakaSmoothSubmersionOriginalTerminalFunctor
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionCoefficientIdeals

open ResolutionInvariantSpec (IsInvDomain IsCanonical)

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

variable {n m : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m}

/-- The unchanged actual compact terminal tower is an elementary principalization,
with canonicality and its identification with the original global map retained. -/
theorem canonical_elementary_principalization [CompactSpace X]
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hne : ∀ x, IsNonzeroAlongAt univ I x) :
    let M : MarkedIdeal n X := ⟨univ, [], I, 1⟩
    let hM := HironakaPrincipalization.isInvDomain_univ hI hne
    let P := compactCanonicalTower M hM
    let T := P.2.val
    let D := exceptionalDivisor T
    let E := (geoTransformAlong M T).E
    ResolutionDriver.IsCanonicalSegment M ((canonicalInvariant n).inv M) T ∧
      IsCanonical M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧
      CentresOver I.zeroLocus T ∧
      IsAdmissibleBlowupSequence n X [] I.zeroLocus P.1 T.proj E ∧
      GermIdeal.pullback (m := n) T.proj I = D.ideal ∧ IsSNCDivisor n E ∧
      D.support = ⋃ H ∈ E, H ∧ D.support = T.proj ⁻¹' I.zeroLocus ∧
      exceptionalLocus n T.proj ⊆ D.support ∧
      IsIsomorphismOver n T.proj I.zeroLocusᶜ ∧
      ∃ η : originalTerminalManifold M hM ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ P.1,
        ∀ z, T.proj (η z) = originalTerminalGluedProjection M hM z := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, [], I, 1⟩
  let hM : IsInvDomain n M := HironakaPrincipalization.isInvDomain_univ hI hne
  let P := compactCanonicalTower M hM
  let T := P.2.val
  have hc : IsCanonical M ((canonicalInvariant n).inv M) T :=
    compactCanonicalTower_isCanonical M hM
  have hr : IsGeoResolution M T := P.2.property.2
  have hcos : M.cosupp = I.zeroLocus := cosupp_univ_one hI
  have hover : CentresOver I.zeroLocus T := by
    rw [← hcos]
    exact centresOver_cosupp M hM.isWellFormed.isClosedSubmanifold_N hI T hr.1
  have hadm := isAdmissibleBlowupSequence_proj M I.zeroLocus T hr.1 hover
  have hpb : GermIdeal.pullback (m := n) T.proj I = (exceptionalDivisor T).ideal :=
    pullback_eq_exceptionalDivisor_of_isGeoResolution M rfl hI rfl T hr
  have hsupp : (exceptionalDivisor T).support = T.proj ⁻¹' I.zeroLocus := by
    rw [EffectiveDivisor.support, ← hpb,
      BlowupExceptionalDivisor.zeroLocus_pullback T.contMDiff_proj hI]
  have hiso : IsIsomorphismOver n T.proj I.zeroLocusᶜ := by
    refine HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      T.isBlowupSequence ?_
    rintro x ⟨z, hz, rfl⟩
    have hz' := HironakaPrincipalization.exceptionalLocus_subset_support T hz
    rw [hsupp] at hz'
    exact hz'
  exact ⟨P.2.property.1, hc, hr, T.contMDiff_proj,
    HironakaLocalPrincipalization.isProperMap_proj T,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence,
    hover, hadm, hpb,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hr.1).isWellFormed.isSNCDivisor,
    HironakaPrincipalization.support_exceptionalDivisor_eq_biUnion M rfl T, hsupp,
    HironakaPrincipalization.exceptionalLocus_subset_support T, hiso,
    originalTerminalFiniteBiholomorphism M hM T hc hr,
    originalTerminalFiniteBiholomorphism_proj M hM T hc hr⟩

/-- A genuine smooth map from an arbitrary original source internally produces
the finite source resolution and Cartesian comparison with that same principalization. -/
theorem canonical_elementary_principalization_smooth_base_change [CompactSpace X]
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hne : ∀ x, IsNonzeroAlongAt univ I x) {b : Y → X}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b) :
    let M : MarkedIdeal n X := ⟨univ, [], I, 1⟩
    let hM := HironakaPrincipalization.isInvDomain_univ hI hne
    let P := compactCanonicalTower M hM
    let T := P.2.val
    let hc := compactCanonicalTower_isCanonical M hM
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
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
      (∀ z, T.proj (g z) = b (S.proj z)) ∧
      HolomorphicSquarePullback b g S.proj T.proj ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
      (∀ z, originalTerminalGluedProjection M hM (G z) =
        b (originalTerminalGluedProjection N hN z)) ∧
      HolomorphicSquarePullback b G
        (originalTerminalGluedProjection N hN) (originalTerminalGluedProjection M hM) ∧
      (∀ z, ηX (G z) = g (ηY z)) ∧
      (∀ z, T.proj (ηX z) = originalTerminalGluedProjection M hM z) ∧
      (∀ z, S.proj (ηY z) = originalTerminalGluedProjection N hN z) := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, [], I, 1⟩
  let hM : IsInvDomain n M := HironakaPrincipalization.isInvDomain_univ hI hne
  let P := compactCanonicalTower M hM
  let T := P.2.val
  let hc := compactCanonicalTower_isCanonical M hM
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
  have hg := terminalSmoothMap_properties hb M hM S T hS.1 hc hS.2 hr
  have hG := originalGlobalFiniteSmoothMap_properties hb M hM S T hS.1 hc hS.2 hr
  refine ⟨hS.1, hS.2,
    pullback_eq_exceptionalDivisor_of_isGeoResolution M rfl hI rfl T hr,
    hg.1, hg.2.1, hg.2.2, hG.1, hG.2.1, hG.2.2, ?_,
    originalTerminalFiniteBiholomorphism_proj M hM T hc hr,
    originalTerminalFiniteBiholomorphism_proj N hN S hS.1 hS.2⟩
  intro z
  change ηX (ηX.symm (g (ηY z))) = g (ηY z)
  exact ηX.apply_symm_apply _

end

end Hironaka.HironakaOriginalCanonicalElementaryPrincipalization
