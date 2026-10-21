/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCanonicalSumSeparation
import Hironaka.Resolution.HironakaOriginalLocalCanonicalPrincipalization
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedGlobalTrace

/-!
# Original individual-sum canonical separation on a prescribed relatively compact open

The same actual canonical individual-sum algorithm is constructed from original
analytic data without compactness of the parts or their intersection. Its target
is fixed before every smooth source, with intrinsic whole records and strict sets.
Blueprint: `hironaka-original-local-canonical-sum-separation-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalLocalCanonicalSumSeparation
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

variable {n : ℕ} {X D : CMfd.{u} n}

open HironakaOriginalCanonicalSumSeparation HironakaOriginalLocalCanonicalPrincipalization
  HironakaSmoothSubmersionOrderedGlobalTrace MarkedIdealBiholomorphism

/-- The whole actual open pullback equals the independently intrinsic local sum record. -/
theorem local_sum_record {A B : Set X}
    (hAa : IsComplexAnalyticSubset (n := n) A) (hBa : IsComplexAnalyticSubset (n := n) B)
    (E₀ : List (Set X)) (U : Opens X) :
    MarkedIdeal.pullback (Subtype.val : U → X) (sumMarkedIdeal A B E₀) =
      sumMarkedIdeal (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' A) ((Subtype.val : U → X) ⁻¹' B)
        (E₀.map ((Subtype.val : U → X) ⁻¹' ·)) := by
  exact pullback_sumMarkedIdeal_eq (Y := CMfd.of (n := n) U) hAa hBa E₀ (isSubmersion_val U)

/-- Actual open inverse images retain both whole mutual-density conditions. -/
theorem local_sum_density {A B : Set X}
    (hAB : A ⊆ closure (A \ B)) (hBA : B ⊆ closure (B \ A)) (U : Opens X) :
    let Aᵤ := (Subtype.val : U → X) ⁻¹' A
    let Bᵤ := (Subtype.val : U → X) ⁻¹' B
    Aᵤ ⊆ closure (Aᵤ \ Bᵤ) ∧ Bᵤ ⊆ closure (Bᵤ \ Aᵤ) := by
  have ho := HironakaBaseChange.isOpenHoloEmbedding_val (n := n) U
  constructor
  · simpa only [ho.preimage_closure,preimage_sdiff] using
      (preimage_mono hAB : (Subtype.val : U → X) ⁻¹' A ⊆ _)
  · simpa only [ho.preimage_closure,preimage_sdiff] using
      (preimage_mono hBA : (Subtype.val : U → X) ⁻¹' B ⊆ _)

/-- Original local data construct an actual terminal individual-sum stage;
the SAME target precedes every genuine smooth source. -/
theorem exists_local_canonical_sum_separation {A B : Set X}
    (hAa : IsComplexAnalyticSubset (n := n) A) (hBa : IsComplexAnalyticSubset (n := n) B)
    (hint : interior A = ∅)
    (hAB : A ⊆ closure (A \ B)) (hBA : B ⊆ closure (B \ A))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (U : Opens X) {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    let Aᵤ := (Subtype.val : U → X) ⁻¹' A
    let Bᵤ := (Subtype.val : U → X) ⁻¹' B
    let Eᵤ := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
    let M := sumMarkedIdeal (X := CMfd.of (n := n) U) Aᵤ Bᵤ Eᵤ
    ∃ (D : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) D),
      IsInvDomain n M ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T ∧
      CentresOver (Aᵤ ∩ Bᵤ) T ∧
      IsAdmissibleBlowupSequence n U Eᵤ (Aᵤ ∩ Bᵤ) D T.proj (geoTransformAlong M T).E ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      GermIdeal.pullback (m := n) T.proj M.ideal = (exceptionalDivisor T).ideal ∧
      (exceptionalDivisor T).support = T.proj ⁻¹' (Aᵤ ∩ Bᵤ) ∧
      Disjoint (strictTransform n T.proj Aᵤ) (strictTransform n T.proj Bᵤ) ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧ IsIsomorphismOver n T.proj (Aᵤ ∩ Bᵤ)ᶜ ∧
      ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → U),
        Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b →
        let N := sumMarkedIdeal (X := Y) (b ⁻¹' Aᵤ) (b ⁻¹' Bᵤ) (Eᵤ.map (b ⁻¹' ·))
        ∃ (C : CMfd.{u} m) (Q : BlowupTower Y C) (g : C → D),
          IsActualTowerPullback b Q T g ∧ markedPullback (m := m) b M = N ∧
          IsInvDomain m N ∧
          Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
          Q.length = T.length ∧ (∀ z, T.proj (g z) = b (Q.proj z)) ∧
          HolomorphicSquarePullback b g Q.proj T.proj ∧
          IsCanonical N ((canonicalInvariant m).inv N) Q ∧ IsGeoResolution N Q ∧
          CentresOver (b ⁻¹' (Aᵤ ∩ Bᵤ)) Q ∧
          IsAdmissibleBlowupSequence m Y (Eᵤ.map (b ⁻¹' ·)) (b ⁻¹' (Aᵤ ∩ Bᵤ))
            C Q.proj (geoTransformAlong N Q).E ∧
          IsSNCDivisor m (geoTransformAlong N Q).E ∧
          (geoTransformAlong N Q).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) ∧
          GermIdeal.pullback (m := m) Q.proj N.ideal = (exceptionalDivisor Q).ideal ∧
          (exceptionalDivisor Q).support = Q.proj ⁻¹' (b ⁻¹' (Aᵤ ∩ Bᵤ)) ∧
          strictTransform m Q.proj (b ⁻¹' Aᵤ) = g ⁻¹' strictTransform n T.proj Aᵤ ∧
          strictTransform m Q.proj (b ⁻¹' Bᵤ) = g ⁻¹' strictTransform n T.proj Bᵤ ∧
          Disjoint (strictTransform m Q.proj (b ⁻¹' Aᵤ)) (strictTransform m Q.proj (b ⁻¹' Bᵤ)) ∧
          ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ Q.proj ∧
          IsProperMap Q.proj ∧ Surjective Q.proj ∧
          IsIsomorphismOver m Q.proj (b ⁻¹' (Aᵤ ∩ Bᵤ))ᶜ := by
  dsimp only
  let Aᵤ := (Subtype.val : U → X) ⁻¹' A
  let Bᵤ := (Subtype.val : U → X) ⁻¹' B
  let Eᵤ := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
  let M := sumMarkedIdeal (X := CMfd.of (n := n) U) Aᵤ Bᵤ Eᵤ
  let J := sumIdeal (vanishingIdeal (n := n) A) (vanishingIdeal (n := n) B)
  have hI : J.IsCoherent := RestrictedIdealExtension.isCoherent_sumIdeal
    (CartanIrreducible.cartanCoherence A hAa) (CartanIrreducible.cartanCoherence B hBa)
  have hne : ∀ x,IsNonzeroAlongAt univ J x := fun x =>
    InvDomainCompanion.isNonzeroAlongAt_sumIdeal_left
      (𝔟 := vanishingIdeal (n := n) A) (𝔠 := vanishingIdeal (n := n) B)
      (fun _ _ h => h.1)
      (HironakaEmbeddedReducible.isNonzeroAlongAt_vanishingIdeal_of_interior_eq_empty hAa hint x)
  have hZ : J.zeroLocus = A ∩ B := zeroLocus_sumIdeal_vanishingIdeal hAa.isClosed hBa.isClosed
  obtain ⟨D,T,hM,hc,hr,hover,hadm,hsnc,hpb,hsupp,_hborn,_hexc,hiso,hhol,hproper,hsurj,hSources⟩ :=
    exists_canonical_boundary_principalization_of_subset_isCompact J hI hne E₀ hE₀ U hK hUK
  have hlocal : MarkedIdeal.pullback (Subtype.val : U → X)
      (⟨univ,E₀,J,1⟩ : MarkedIdeal n X) = M := local_sum_record hAa hBa E₀ U
  rw [hlocal] at hM hc hr hadm hsnc hpb hSources
  have hF : (Subtype.val : U → X) ⁻¹' J.zeroLocus = Aᵤ ∩ Bᵤ := by rw [hZ,preimage_inter]
  rw [hF] at hover hadm hsupp hiso hSources
  obtain ⟨hABU,hBAU⟩ := local_sum_density hAB hBA U
  have hdis : Disjoint (strictTransform n T.proj Aᵤ) (strictTransform n T.proj Bᵤ) :=
    disjoint_strictTransform_of_pullback_sumIdeal T.contMDiff_proj hABU hBAU
      (exceptionalDivisor T) hpb hsupp.le
  refine ⟨D,T,hM,hc,hr,hover,hadm,hsnc,hpb,hsupp,hdis,hhol,hproper,hsurj,hiso,?_⟩
  intro m Y b hb
  have hAaU : IsComplexAnalyticSubset (n := n) Aᵤ := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hAa
  have hBaU : IsComplexAnalyticSubset (n := n) Bᵤ := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hBa
  let N := sumMarkedIdeal (X := Y) (b ⁻¹' Aᵤ) (b ⁻¹' Bᵤ) (Eᵤ.map (b ⁻¹' ·))
  have heq : markedPullback (m := m) b M = N :=
    pullback_sumMarkedIdeal_eq (X := CMfd.of (n := n) U) hAaU hBaU Eᵤ hb
  obtain ⟨C,Q,g,hactual,hN,_hNN,_hNE,_hNI,_hNd,hg,hlen,hcomm,hcart,hcQ,hrQ,
      hoverQ,hadmQ,hsncQ,hE,hpbQ,hsuppQ,_hbornQ,_hexcQ,hisoQ,hholQ,hproperQ,hsurjQ⟩ := hSources Y b hb
  rw [heq] at hN hcQ hrQ hadmQ hsncQ hE hpbQ
  let O : Opens (CMfd.of (n := n) U) := ⟨(Aᵤ ∩ Bᵤ)ᶜ,(hAaU.isClosed.inter hBaU.isClosed).isOpen_compl⟩
  have havoid : CentresAvoid O T := centresAvoid_of_centresOver O disjoint_compl_left T hover
  have hdenA : Aᵤ ⊆ closure (Aᵤ ∩ (O : Set U)) := by
    have he : Aᵤ ∩ (O : Set U) = Aᵤ \ Bᵤ := by
      ext x
      simp only [O,Opens.coe_mk,mem_inter_iff,mem_compl_iff,Set.mem_sdiff]
      tauto
    rw [he]
    exact hABU
  have hdenB : Bᵤ ⊆ closure (Bᵤ ∩ (O : Set U)) := by
    have he : Bᵤ ∩ (O : Set U) = Bᵤ \ Aᵤ := by
      ext x
      simp only [O,Opens.coe_mk,mem_inter_iff,mem_compl_iff,Set.mem_sdiff]
      tauto
    rw [he]
    exact hBAU
  have hA := IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hactual O havoid Aᵤ hdenA
  have hB := IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hactual O havoid Bᵤ hdenB
  have hdisQ : Disjoint (strictTransform m Q.proj (b ⁻¹' Aᵤ))
      (strictTransform m Q.proj (b ⁻¹' Bᵤ)) := by
    rw [hA,hB]
    exact hdis.preimage g
  exact ⟨C,Q,g,hactual,heq,hN,hg,hlen,hcomm,hcart,hcQ,hrQ,hoverQ,hadmQ,hsncQ,hE,
    hpbQ,hsuppQ,hA,hB,hdisQ,hholQ,hproperQ,hsurjQ,hisoQ⟩

end
end Hironaka.HironakaOriginalLocalCanonicalSumSeparation
