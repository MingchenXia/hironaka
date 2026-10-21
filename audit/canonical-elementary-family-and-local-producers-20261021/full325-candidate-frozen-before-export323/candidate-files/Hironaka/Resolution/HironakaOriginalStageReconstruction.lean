/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPureHeadChoice

/-!
# Constructing actual stages over genuine bases with empty-only boundary differences

Equal filtered original lists give real history conditions for the SAME tower.
Actual tower transport constructs all source histories and endpoint maps.
Blueprint: `hironaka-original-stage-reconstruction-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalStageReconstruction
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealTowerTransport BlowupTowerIsomorphism NormalCrossings
  HironakaOriginalBoundaryEmptyFilterComparison HironakaOriginalBoundaryEmptyBaseComparison
  HironakaSmoothSubmersionOrderedChoiceBaseChange RestrictEmptyTower
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
variable {n : ℕ} {X X' D : CMfd.{u} n}

/-- Equal ordered nonempty initial filters reconstruct genuine conditions
for the SAME actual tower, with its whole cosupport and maxima. -/
theorem same_filtered_boundary_stage_dictionary (M : MarkedIdeal n X)
    (hM : IsInvDomain n M) (hN : M.N=univ) (E' : List (Set X))
    (hE' : IsSNCDivisor n E')
    (hfilter : E'.filter (fun H => decide H.Nonempty)=M.E.filter (fun H => decide H.Nonempty))
    (T : BlowupTower X D) :
    let J : MarkedIdeal n X := {M with E := E'}
    IsInvDomain n J ∧
      (IsCanonical J ((CanonicalCentres.canonicalInvariant n).inv J) T ↔
        IsCanonical M ((CanonicalCentres.canonicalInvariant n).inv M) T) ∧
      (IsGeoTestTower J T ↔ IsGeoTestTower M T) ∧
      (IsGeoResolution J T ↔ IsGeoResolution M T) ∧
      (geoTransformAlong J T).cosupp=(geoTransformAlong M T).cosupp ∧
      (∀ K : Set D,maxLocus ((CanonicalCentres.canonicalInvariant n).inv J T) K=
        maxLocus ((CanonicalCentres.canonicalInvariant n).inv M T) K) ∧
      (geoTransformAlong J T).E.filter (fun H => decide H.Nonempty)=
        (geoTransformAlong M T).E.filter (fun H => decide H.Nonempty) := by
  dsimp only
  let J : MarkedIdeal n X := {M with E := E'}
  have hd : IsInvDomain n J :=
    ⟨⟨hM.isWellFormed.isClosedSubmanifold_N,hM.isWellFormed.isCoherent,hE',by
      change IsTransverse n M.N E'
      rw [hN]
      exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE'⟩,
      hM.dimLE,hM.one_le_d,hM.isNonzeroAlongAt⟩
  have heq : nonemptyBoundary J=nonemptyBoundary M := by
    change ({M with E := E'.filter (fun H => decide H.Nonempty)} : MarkedIdeal n X)=_
    rw [hfilter]
    rfl
  refine ⟨hd,?_,?_,?_,?_,?_,?_⟩
  · rw [← isCanonical_nonemptyBoundary_iff J T,heq,isCanonical_nonemptyBoundary_iff M T]
  · rw [← isGeoTestTower_nonemptyBoundary_iff J T,heq,isGeoTestTower_nonemptyBoundary_iff M T]
  · rw [← isGeoResolution_nonemptyBoundary_iff J T,heq,isGeoResolution_nonemptyBoundary_iff M T]
  · rw [← cosupp_nonemptyBoundary_along J T,heq,cosupp_nonemptyBoundary_along M T]
  · intro K
    rw [← maxLocus_nonemptyBoundary J T K,heq,maxLocus_nonemptyBoundary M T K]
  · rw [← filtered_boundary_nonemptyBoundary_along J T,heq,filtered_boundary_nonemptyBoundary_along M T]

private theorem filter_nonempty_map_preimage {P Q : Type*} (f : P → Q)
    (hf : Function.Surjective f) (E : List (Set Q)) :
    (E.map (f ⁻¹' ·)).filter (fun H => decide H.Nonempty)=
      (E.filter (fun H => decide H.Nonempty)).map (f ⁻¹' ·) := by
  induction E with
  | nil => rfl
  | cons H E ih =>
    have hh : (f ⁻¹' H).Nonempty ↔ H.Nonempty :=
      ⟨fun ⟨x,hx⟩ => ⟨f x,hx⟩,fun h => h.preimage hf⟩
    by_cases hne : H.Nonempty <;> simp [hh,hne,ih]

/-- Genuine prescribed-base tower transport, with actual source canonicality
and all whole filtered/locus dictionaries internally reconstructed. -/
theorem canonical_stage_reconstruction_over_base (M : MarkedIdeal n X)
    (hM : IsInvDomain n M) (hN : M.N=univ)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (E' : List (Set X')) (hE' : IsSNCDivisor n E')
    (hfilter : E'.filter (fun H => decide H.Nonempty)=
      (M.E.map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty))
    (T : BlowupTower X D)
    (hc : IsCanonical M ((CanonicalCentres.canonicalInvariant n).inv M) T) :
    let P := transport Φ T
    let J : MarkedIdeal n X' := {MarkedIdeal.pullback Φ M with E := E'}
    IsInvDomain n J ∧ IsCanonical J ((CanonicalCentres.canonicalInvariant n).inv J) P.tower ∧
      IsTowerIso Φ P.tower T P.back ∧
      (∀ z,T.proj (P.back z)=Φ (P.tower.proj z)) ∧
      (geoTransformAlong J P.tower).cosupp=P.back ⁻¹' (geoTransformAlong M T).cosupp ∧
      (∀ K : Set D,K ⊆ (geoTransformAlong M T).cosupp →
        maxLocus ((CanonicalCentres.canonicalInvariant n).inv J P.tower) (P.back ⁻¹' K)=
        P.back ⁻¹' maxLocus ((CanonicalCentres.canonicalInvariant n).inv M T) K) ∧
      (geoTransformAlong J P.tower).E.filter (fun H => decide H.Nonempty)=
        ((geoTransformAlong M T).E.filter (fun H => decide H.Nonempty)).map (P.back ⁻¹' ·) ∧
      (IsGeoResolution M T → IsGeoResolution J P.tower) ∧
      (∀ O : TopologicalSpace.Opens X,CentresAvoid O T → CentresAvoid (baseOpen Φ O) P.tower) ∧
      ∀ A : Set X,IsClosed A → strictTransform n P.tower.proj (Φ ⁻¹' A)=
        P.back ⁻¹' strictTransform n T.proj A := by
  dsimp only
  let P := transport Φ T
  let B := MarkedIdeal.pullback Φ M
  let J : MarkedIdeal n X' := {B with E := E'}
  obtain ⟨hB,hcB,hi,hcomm,hrec,_hmax,hr,ha⟩ := canonical_transport_dictionary M hM Φ T hc
  have hBN : B.N=univ := by change Φ ⁻¹' M.N=univ;rw [hN,preimage_univ]
  obtain ⟨hJ,hcan,htest,hres,hcos,hmax,hE⟩ :=
    same_filtered_boundary_stage_dictionary B hB hBN E' hE' hfilter P.tower
  have hcosB : (geoTransformAlong B P.tower).cosupp=P.back ⁻¹' (geoTransformAlong M T).cosupp :=
    hi.cosupp_geoTransformAlong Φ hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent
      ((CanonicalCentres.canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hM T hc)
  refine ⟨hJ,hcan.mpr hcB,hi,hcomm,hcos.trans hcosB,?_,?_,fun h => hres.mpr (hr h),ha,?_⟩
  · intro K hK
    rw [hmax]
    exact ResolutionInvariantSegments.maxLocus_preimage_of_surjective P.back.surjective
      (fun z hz => (CanonicalCentres.canonicalInvariant n).isInvValue.towerIso Φ M hM
        P.tower T P.back hi hc z (hK hz))
  · rw [hE,congrArg MarkedIdeal.E hrec]
    exact filter_nonempty_map_preimage P.back P.back.surjective _
  · intro A hA
    exact HironakaNormalCrossingsSeparationChoiceComparison.strictTransform_preimage_of_square
      Φ P.back P.tower.contMDiff_proj T.contMDiff_proj A hA hcomm

end
end Hironaka.HironakaOriginalStageReconstruction
