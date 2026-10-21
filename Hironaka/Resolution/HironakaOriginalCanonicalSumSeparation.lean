/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalBoundaryCanonicalPrincipalization
import Hironaka.Resolution.HironakaOriginalStoppedPrefixSmoothComparison
import Hironaka.Resolution.HironakaActualSingularSubmersionPullback
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeRestriction
import Hironaka.Resolution.HironakaSeparation

/-!
# Canonical separation of original analytic parts and its same smooth source

The original sum vanishing ideal internally selects a genuine compact-cosupport
canonical terminal tower. Every smooth source is constructed after fixing that
same target, with literal intrinsic sum input, whole ordered boundaries and
whole conventional strict transforms. No separator or comparison is input.
Blueprint: `hironaka-original-canonical-sum-separation-extension.tex`.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalCanonicalSumSeparation

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings RestrictEmptyTower DivisorExponentAlong CanonicalCentres
  HironakaAdmissibleSequence HironakaOriginalBoundaryCanonicalPrincipalization
  HironakaSmoothSubmersionOriginalCompactTerminal HironakaSmoothSubmersionOriginalGlobalFinite
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeControlledTower
  HironakaOriginalStoppedPrefixSmoothComparison HironakaSmoothSubmersionRelativeRestriction
  HironakaSeparation RestrictedIdealExtension

open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n m : ℕ} {X D : CMfd.{u} n} {Y C : CMfd.{u} m}

/-- The unchanged original sum datum retains the entire ordered boundary. -/
def sumMarkedIdeal (A B : Set X) (E₀ : List (Set X)) : MarkedIdeal n X :=
  ⟨univ,E₀,sumIdeal (vanishingIdeal A) (vanishingIdeal B),1⟩

/-- Natural original analytic and SNC data supply the actual invariant domain. -/
theorem isInvDomain_sumMarkedIdeal {A B : Set X}
    (hAa : IsComplexAnalyticSubset (n := n) A) (hBa : IsComplexAnalyticSubset (n := n) B)
    (hint : interior A = ∅) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) :
    IsInvDomain n (sumMarkedIdeal A B E₀) := by
  apply HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor
    (RestrictedIdealExtension.isCoherent_sumIdeal
      (CartanIrreducible.cartanCoherence A hAa) (CartanIrreducible.cartanCoherence B hBa))
    (fun x => InvDomainCompanion.isNonzeroAlongAt_sumIdeal_left
      (𝔟 := vanishingIdeal (n := n) A) (𝔠 := vanishingIdeal (n := n) B)
      (fun _ _ h => h.1)
      (HironakaEmbeddedReducible.isNonzeroAlongAt_vanishingIdeal_of_interior_eq_empty hAa hint x)) hE₀

/-- Genuine singular-ideal pullback identifies every field of the intrinsic source record. -/
theorem pullback_sumMarkedIdeal_eq {A B : Set X}
    (hAa : IsComplexAnalyticSubset (n := n) A) (hBa : IsComplexAnalyticSubset (n := n) B)
    (E₀ : List (Set X)) {b : Y → X}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b) :
    markedPullback (m := m) b (sumMarkedIdeal A B E₀) =
      sumMarkedIdeal (b ⁻¹' A) (b ⁻¹' B) (E₀.map (b ⁻¹' ·)) := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · simp only [markedPullback,sumMarkedIdeal,preimage_univ]
  · rfl
  · change GermIdeal.pullback (m := m) b (sumIdeal (vanishingIdeal A) (vanishingIdeal B)) = _
    rw [pullback_sumIdeal_dimensions hb.contMDiff
      (CartanIrreducible.cartanCoherence A hAa) (CartanIrreducible.cartanCoherence B hBa),
      HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion hb A,
      HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion hb B]
    rfl
  · rfl

private theorem terminal_geometry (I : GermIdeal n X) (E₀ : List (Set X))
    (hM : IsInvDomain n (⟨univ,E₀,I,1⟩ : MarkedIdeal n X))
    (F : Set X) (hZ : I.zeroLocus = F) (T : BlowupTower X D)
    (hr : IsGeoResolution (⟨univ,E₀,I,1⟩ : MarkedIdeal n X) T) :
    let M : MarkedIdeal n X := ⟨univ,E₀,I,1⟩
    CentresOver F T ∧
      IsAdmissibleBlowupSequence n X E₀ F D T.proj (geoTransformAlong M T).E ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      GermIdeal.pullback (m := n) T.proj I = (exceptionalDivisor T).ideal ∧
      (exceptionalDivisor T).support = T.proj ⁻¹' F ∧
      IsIsomorphismOver n T.proj Fᶜ := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,E₀,I,1⟩
  have hI : I.IsCoherent := hM.isWellFormed.isCoherent
  have hcos : M.cosupp = I.zeroLocus := cosupp_univ_one hI
  have hover : CentresOver I.zeroLocus T := by
    rw [← hcos]
    exact centresOver_cosupp M hM.isWellFormed.isClosedSubmanifold_N hI T hr.1
  have hpb : GermIdeal.pullback (m := n) T.proj I = (exceptionalDivisor T).ideal :=
    pullback_eq_exceptionalDivisor_of_isGeoResolution M rfl hI rfl T hr
  have hsupp : (exceptionalDivisor T).support = T.proj ⁻¹' I.zeroLocus := by
    rw [EffectiveDivisor.support,← hpb,BlowupExceptionalDivisor.zeroLocus_pullback T.contMDiff_proj hI]
  have hiso : IsIsomorphismOver n T.proj I.zeroLocusᶜ := by
    refine HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      T.isBlowupSequence ?_
    rintro x ⟨z,hz,rfl⟩
    have hz' := HironakaPrincipalization.exceptionalLocus_subset_support T hz
    rw [hsupp] at hz'
    exact hz'
  rw [hZ] at hover hsupp hiso
  exact ⟨hover,isAdmissibleBlowupSequence_proj M F T hr.1 hover,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hr.1).isWellFormed.isSNCDivisor,
    hpb,hsupp,hiso⟩

/-- Original analytic parts internally select one canonical terminal sum separator;
every genuine smooth source subsequently retains that SAME target tower. -/
theorem exists_canonical_sum_separation {A B : Set X}
    (hAa : IsComplexAnalyticSubset (n := n) A) (hBa : IsComplexAnalyticSubset (n := n) B)
    (hint : interior A = ∅) (hK : IsCompact (A ∩ B))
    (hAB : A ⊆ closure (A \ B)) (hBA : B ⊆ closure (B \ A))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) :
    let M := sumMarkedIdeal A B E₀
    ∃ (D : CMfd.{u} n) (T : BlowupTower X D),
      IsInvDomain n M ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T ∧
      CentresOver (A ∩ B) T ∧
      IsAdmissibleBlowupSequence n X E₀ (A ∩ B) D T.proj (geoTransformAlong M T).E ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      GermIdeal.pullback (m := n) T.proj M.ideal = (exceptionalDivisor T).ideal ∧
      (exceptionalDivisor T).support = T.proj ⁻¹' (A ∩ B) ∧
      Disjoint (strictTransform n T.proj A) (strictTransform n T.proj B) ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧ IsIsomorphismOver n T.proj (A ∩ B)ᶜ ∧
      ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → X),
        Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b →
        let N := sumMarkedIdeal (b ⁻¹' A) (b ⁻¹' B) (E₀.map (b ⁻¹' ·))
        ∃ (C : CMfd.{u} m) (Q : BlowupTower Y C) (g : C → D),
          IsActualTowerPullback b Q T g ∧ markedPullback (m := m) b M = N ∧
          IsInvDomain m N ∧
          Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
          Q.length = T.length ∧ (∀ z, T.proj (g z) = b (Q.proj z)) ∧
          HolomorphicSquarePullback b g Q.proj T.proj ∧
          IsCanonical N ((canonicalInvariant m).inv N) Q ∧ IsGeoResolution N Q ∧
          CentresOver (b ⁻¹' (A ∩ B)) Q ∧
          IsAdmissibleBlowupSequence m Y (E₀.map (b ⁻¹' ·)) (b ⁻¹' (A ∩ B))
            C Q.proj (geoTransformAlong N Q).E ∧
          IsSNCDivisor m (geoTransformAlong N Q).E ∧
          (geoTransformAlong N Q).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) ∧
          GermIdeal.pullback (m := m) Q.proj N.ideal = (exceptionalDivisor Q).ideal ∧
          (exceptionalDivisor Q).support = Q.proj ⁻¹' (b ⁻¹' (A ∩ B)) ∧
          strictTransform m Q.proj (b ⁻¹' A) = g ⁻¹' strictTransform n T.proj A ∧
          strictTransform m Q.proj (b ⁻¹' B) = g ⁻¹' strictTransform n T.proj B ∧
          Disjoint (strictTransform m Q.proj (b ⁻¹' A)) (strictTransform m Q.proj (b ⁻¹' B)) ∧
          ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ Q.proj ∧
          IsProperMap Q.proj ∧ Surjective Q.proj ∧
          IsIsomorphismOver m Q.proj (b ⁻¹' (A ∩ B))ᶜ := by
  dsimp only
  let M := sumMarkedIdeal A B E₀
  have hM : IsInvDomain n M := isInvDomain_sumMarkedIdeal hAa hBa hint hE₀
  have hI : M.ideal.IsCoherent := hM.isWellFormed.isCoherent
  have hZ : M.ideal.zeroLocus = A ∩ B :=
    zeroLocus_sumIdeal_vanishingIdeal hAa.isClosed hBa.isClosed
  have hcos : M.cosupp = A ∩ B := (cosupp_univ_one hI).trans hZ
  let P := compactCosupportCanonicalTower M hM (hcos.symm ▸ hK)
  let T := P.2.val
  have hc := P.2.property.1
  have hr := P.2.property.2
  obtain ⟨hover,hadm,hsnc,hpb,hsupp,hiso⟩ := terminal_geometry M.ideal E₀ hM (A ∩ B) hZ T hr
  have hdis : Disjoint (strictTransform n T.proj A) (strictTransform n T.proj B) :=
    disjoint_strictTransform_of_pullback_sumIdeal T.contMDiff_proj hAB hBA
      (exceptionalDivisor T) hpb hsupp.le
  refine ⟨P.1,T,hM,hc,hr,hover,hadm,hsnc,hpb,hsupp,hdis,T.contMDiff_proj,
    HironakaLocalPrincipalization.isProperMap_proj T,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence,hiso,?_⟩
  intro m Y b hb
  let N := sumMarkedIdeal (b ⁻¹' A) (b ⁻¹' B) (E₀.map (b ⁻¹' ·))
  have heq : markedPullback (m := m) b M = N := pullback_sumMarkedIdeal_eq hAa hBa E₀ hb
  have hN : IsInvDomain m N := by
    rw [← heq]
    exact original_ambient_domain_pullback hb M hM
  let S := chosenActualTower defaultSmoothBlowupChoices hb T
  let Q := S.2.1
  let g := S.2.2.val
  have hactual : IsActualTowerPullback b Q T g := S.2.2.property
  have hQ := originalFiniteSmoothSourceHistory_properties hb M hM T hc hr
  change IsCanonical (markedPullback (m := m) b M)
    ((canonicalInvariant m).inv (markedPullback (m := m) b M)) Q ∧
    IsGeoResolution (markedPullback (m := m) b M) Q at hQ
  rw [heq] at hQ
  have hrecord := (HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
    hactual M hM.isWellFormed hr.1).2
  rw [heq] at hrecord
  have hE : (geoTransformAlong N Q).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) :=
    congrArg MarkedIdeal.E hrecord
  have hNI : GermIdeal.pullback (m := m) b M.ideal = N.ideal := congrArg MarkedIdeal.ideal heq
  have hNZ : N.ideal.zeroLocus = b ⁻¹' (A ∩ B) := by
    rw [← hNI,BlowupExceptionalDivisor.zeroLocus_pullback hb.contMDiff hI,hZ]
  obtain ⟨hoverQ,hadmQ,hsncQ,hpbQ,hsuppQ,hisoQ⟩ :=
    terminal_geometry N.ideal N.E hN (b ⁻¹' (A ∩ B)) hNZ Q hQ.2
  let O : Opens X := ⟨(A ∩ B)ᶜ,(hAa.isClosed.inter hBa.isClosed).isOpen_compl⟩
  have havoid : CentresAvoid O T :=
    centresAvoid_of_centresOver O disjoint_compl_left T hover
  have hdenA : A ⊆ closure (A ∩ (O : Set X)) := by
    have he : A ∩ (O : Set X) = A \ B := by
      ext x
      simp only [O,Opens.coe_mk,mem_inter_iff,mem_compl_iff,Set.mem_sdiff]
      tauto
    rw [he]
    exact hAB
  have hdenB : B ⊆ closure (B ∩ (O : Set X)) := by
    have he : B ∩ (O : Set X) = B \ A := by
      ext x
      simp only [O,Opens.coe_mk,mem_inter_iff,mem_compl_iff,Set.mem_sdiff]
      tauto
    rw [he]
    exact hBA
  have hA := IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hactual O havoid A hdenA
  have hB := IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hactual O havoid B hdenB
  have hdisQ : Disjoint (strictTransform m Q.proj (b ⁻¹' A))
      (strictTransform m Q.proj (b ⁻¹' B)) := by
    rw [hA,hB]
    exact hdis.preimage g
  exact ⟨S.1,Q,g,hactual,heq,hN,hactual.isSubmersion,hactual.length_eq,hactual.proj_comm,
    hactual.universal,hQ.1,hQ.2,hoverQ,hadmQ,hsncQ,hE,hpbQ,hsuppQ,hA,hB,hdisQ,
    Q.contMDiff_proj,HironakaLocalPrincipalization.isProperMap_proj Q,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective Q.isBlowupSequence,hisoQ⟩

end

end Hironaka.HironakaOriginalCanonicalSumSeparation
