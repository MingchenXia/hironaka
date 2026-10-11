/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.CanonicalResolution
import Hironaka.Resolution.HironakaPrincipalizationBoundary

set_option autoImplicit false

/-!
# Canonical elementary principalization with compact zero locus

The actual compact-cosupport driver retains its canonical segment, and
its geometric principalization consumer retains all elementary conclusions.
Open restriction and biholomorphism compatibility concern that same tower.
General smooth morphism base change is a separate remaining obligation.
Blueprint: `hironaka-canonical-principalization-extension.tex`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaCanonicalPrincipalization

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealRestrictOpen
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings DivisorExponentAlong
  HironakaAdmissibleSequence HironakaPrincipalizationBoundary
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (IsCanonicalSegment)
open ResolutionInvariantOrder (IsInvUSCOn)

noncomputable section

variable {n : ℕ}

/-- The actual compact-cosupport driver produces a segment without empty centres. -/
theorem exists_canonical_segment_of_isCompact {Λ : Type v} [LinearOrder Λ] [WellFoundedLT Λ]
    {k : ℕ} (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    (hK : IsCompact 𝔪.cosupp) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonicalSegment 𝔪 (R.inv 𝔪) T ∧ IsGeoResolution 𝔪 T := by
  have hcanseg : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsCanonicalSegment 𝔪 (R.inv 𝔪) T → IsCanonical 𝔪 (R.inv 𝔪) T :=
    fun T hT => ResolutionInvariantDriver.isCanonical_of_isCanonicalSegment (R.inv 𝔪) T hT
  exact MonomialCaseLocal.exists_isGeoResolution_of_wellFounded_invariant_of_isCompact 𝔪 (R.inv 𝔪)
    (fun T _ hT => MonomialCaseLocal.isCompact_cosupp_geoTransformAlong
      h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent hK T hT)
    (fun T hseg _ => R.isInvValue.usc 𝔪 h T (hcanseg T hseg))
    (fun T hseg hT _ => ⟨R.isInvValue.isAdmissibleCentre_maxLocus h T (hcanseg T hseg) hT,
      ResolutionInvariantDriver.interior_maxLocus_eq_empty h T hT _⟩)
    (fun {Y} T hseg hT x₀ hx₀ {Z} π hπ z hz => by
      have hcan := hcanseg T hseg
      have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
      have hzS : π z ∈ (geoTransformAlong 𝔪 T).cosupp :=
        TransformOffCentre.cosupp_geoTransform_subset_preimage _
          hdomT.isWellFormed.isClosedSubmanifold_N.1
          (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
            hdomT.isWellFormed.isCoherent hg) hπ (fun p hp => hp.1) hz
      obtain ⟨hdrop, heq⟩ := R.isInvValue.decrease 𝔪 h T _ π hπ hcan ⟨x₀, hx₀⟩ rfl z hz
      by_cases hzC : π z ∈ ResolutionDriver.maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp
      · exact (hdrop hzC).trans_le (hx₀.2 _ hzS)
      · rw [heq hzC]
        exact lt_of_le_of_ne (hx₀.2 _ hzS) fun hval =>
          hzC ⟨hzS, fun p hp => (hx₀.2 p hp).trans hval.ge⟩)

/-- Actual canonical resolution, with compatibility, needs only compact cosupport. -/
theorem canonicalResolution_of_isCompact {Λ : Type v} [LinearOrder Λ] [WellFoundedLT Λ]
    {k : ℕ} (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    (hK : IsCompact 𝔪.cosupp) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsGeoResolution 𝔪 T ∧
      IsCanonicalSegment 𝔪 (R.inv 𝔪) T ∧
      (∀ {Y₁ : CMfd.{u} n} (T₁ : BlowupTower X Y₁), IsCanonical 𝔪 (R.inv 𝔪) T₁ →
        IsInvUSCOn (R.inv 𝔪 T₁) (geoTransformAlong 𝔪 T₁).cosupp) ∧
      (∀ U : Opens X, IsCanonical (pullback (Subtype.val : U → X) 𝔪)
        (R.inv (pullback (Subtype.val : U → X) 𝔪)) (restrict U T)) ∧
      (∀ {X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
        {Y' : CMfd.{u} n} (T' : BlowupTower X' Y'),
        IsCanonicalSegment (pullback Φ 𝔪) (R.inv (pullback Φ 𝔪)) T' →
        IsGeoResolution (pullback Φ 𝔪) T' →
        ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y,
          IsTowerIso Φ T' T χ) := by
  obtain ⟨Y, T, hseg, hres⟩ := exists_canonical_segment_of_isCompact R h hK
  refine ⟨Y, T, hres, hseg, fun T₁ hT₁ => R.isInvValue.usc 𝔪 h T₁ hT₁,
    fun U => ?_, fun {_} Φ {_} T' hT' hres' =>
      CanonicalResolution.exists_isTowerIso_of_isGeoResolution R h Φ T' T hT' hseg hres' hres⟩
  exact Seq.ResolutionInvariantExt.isCanonical_restrict R h U T
    (ResolutionInvariantDriver.isCanonical_of_isCanonicalSegment _ T hseg)

/-- The elementary principalization and the canonical compatibility use the same real tower. -/
theorem exists_canonical_principalization_boundary {X : CMfd.{u} n}
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) (hne : ∀ x, IsNonzeroAlongAt univ 𝔞 x)
    (hZ : IsCompact 𝔞.zeroLocus) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y) (D : EffectiveDivisor n Y) (E : List (Set Y)),
      IsAdmissibleBlowupSequence n X E₀ 𝔞.zeroLocus Y T.proj E ∧
      GermIdeal.pullback (m := n) T.proj 𝔞 = D.ideal ∧ IsSNCDivisor n E ∧
      D.support = ⋃ H ∈ E.drop E₀.length, H ∧ D.support = T.proj ⁻¹' 𝔞.zeroLocus ∧
      IsIsomorphismOver n T.proj 𝔞.zeroLocusᶜ ∧
      IsGeoResolution (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X) T ∧
      IsCanonicalSegment (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X)
        ((CanonicalCentres.canonicalInvariant n).inv (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X)) T ∧
      (∀ U : Opens X, IsCanonical
        (pullback (Subtype.val : U → X) (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X))
        ((CanonicalCentres.canonicalInvariant n).inv
          (pullback (Subtype.val : U → X) (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X))) (restrict U T)) ∧
      (∀ {X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
        {Y' : CMfd.{u} n} (T' : BlowupTower X' Y'),
        IsCanonicalSegment (pullback Φ (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X))
          ((CanonicalCentres.canonicalInvariant n).inv
            (pullback Φ (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X))) T' →
        IsGeoResolution (pullback Φ (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X)) T' →
        ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y,
          IsTowerIso Φ T' T χ) := by
  let 𝔪 : MarkedIdeal n X := ⟨univ, E₀, 𝔞, 1⟩
  have hdom : IsInvDomain n 𝔪 := isInvDomain_univ_of_isSNCDivisor h𝔞 hne hE₀
  have hcos : 𝔪.cosupp = 𝔞.zeroLocus := by
    show GermIdealOrder.cosupport n univ 𝔞 1 = 𝔞.zeroLocus
    rw [GermIdealOrder.cosupport_one
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg), univ_inter]
  obtain ⟨Y, T, hres, hseg, -, hopen, hiso⟩ := canonicalResolution_of_isCompact
    (CanonicalCentres.canonicalInvariant.{u} n) hdom (by rw [hcos]; exact hZ)
  have hpb : GermIdeal.pullback (m := n) T.proj 𝔞 = (exceptionalDivisor T).ideal :=
    pullback_eq_exceptionalDivisor_of_isGeoResolution 𝔪 rfl h𝔞 rfl T hres
  have hsupp : (exceptionalDivisor T).support = T.proj ⁻¹' 𝔞.zeroLocus := by
    rw [EffectiveDivisor.support, ← hpb, BlowupExceptionalDivisor.zeroLocus_pullback T.contMDiff_proj h𝔞]
  have hadm := isAdmissibleBlowupSequence_proj 𝔪 _ T hres.1
    (centresOver_cosupp 𝔪 hdom.isWellFormed.isClosedSubmanifold_N h𝔞 T hres.1)
  rw [hcos] at hadm
  refine ⟨Y, T, exceptionalDivisor T, (geoTransformAlong 𝔪 T).E, hadm, hpb,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom T hres.1).isWellFormed.isSNCDivisor,
    support_exceptionalDivisor_eq_biUnion_drop 𝔪 hE₀.1 T, hsupp, ?_, hres, hseg, hopen, hiso⟩
  refine HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset T.isBlowupSequence ?_
  rintro x ⟨z, hz, rfl⟩
  have hz' := HironakaPrincipalization.exceptionalLocus_subset_support T hz
  rw [hsupp] at hz'
  exact hz'

end
end Hironaka.HironakaCanonicalPrincipalization
