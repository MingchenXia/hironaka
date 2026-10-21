/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyFilterComparison
import Hironaka.Resolution.HironakaOriginalTerminalOverlapComparison
/-!
# Actual canonical stages over a genuine base biholomorphism and empty entries

The actual transported tower and its whole dictionary are internally supplied
before comparing independently chosen terminal or first-meeting histories.
Blueprint: `hironaka-original-boundary-empty-base-comparison-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalBoundaryEmptyBaseComparison
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealTowerTransport
  CanonicalCentres RestrictEmptyTower HironakaOriginalBoundaryEmptyFilterComparison
  HironakaOriginalTerminalProjectionUniqueness
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

/-- The literal original open on the prescribed biholomorphic base. -/
def baseOpen (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (O : Opens X) : Opens X' :=
  ⟨Φ ⁻¹' (O : Set X),O.isOpen.preimage Φ.contMDiff.continuous⟩

private theorem centresAvoid_of_isTowerIso
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {S : BlowupTower X' Y'} {T : BlowupTower X Y}
    {β : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hi : IsTowerIso Φ S T β) (O : Opens X) (ha : CentresAvoid O T) :
    CentresAvoid (baseOpen Φ O) S := by
  induction hi with
  | refl => trivial
  | @step D' D Z' Z S T χ h C' ρ hρ C π hπ χ₁ hcomm hC ih =>
    refine ⟨ih ha.1,Set.disjoint_left.mpr ?_⟩
    intro z hzC hzO
    apply Set.disjoint_left.mp ha.2
    · rw [← hC] at hzC
      exact hzC
    · change T.proj (χ z) ∈ O
      rw [← h.proj_comm z]
      exact hzO

/-- Internally actual tower transport gives whole geometry, whole maximum
loci, terminality and preserved opens for the SAME transported history. -/
theorem canonical_transport_dictionary (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (T : BlowupTower X Y) (hc : IsCanonical M ((canonicalInvariant n).inv M) T) :
    let P := transport Φ T
    let J := MarkedIdeal.pullback Φ M
    IsInvDomain n J ∧ IsCanonical J ((canonicalInvariant n).inv J) P.tower ∧
      IsTowerIso Φ P.tower T P.back ∧
      (∀ z, T.proj (P.back z) = Φ (P.tower.proj z)) ∧
      geoTransformAlong J P.tower = MarkedIdeal.pullback P.back (geoTransformAlong M T) ∧
      maxLocus ((canonicalInvariant n).inv J P.tower) (geoTransformAlong J P.tower).cosupp =
        P.back ⁻¹' maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp ∧
      (IsGeoResolution M T → IsGeoResolution J P.tower) ∧
      ∀ O : Opens X, CentresAvoid O T → CentresAvoid (baseOpen Φ O) P.tower := by
  dsimp only
  let P := transport Φ T
  have hi : IsTowerIso Φ P.tower T P.back := transport_isTowerIso Φ T
  have ht := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  have hcan := HironakaEmbeddedResolutionLocal.isCanonical_of_isTowerIso
    (HironakaFromSeqInvariant.embeddingFields_of_seq (canonicalInvariant n)) hM Φ hi hc
  have hrec := hi.geoTransformAlong_eq Φ hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent ht
  have hcos := hi.cosupp_geoTransformAlong Φ hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent ht
  have hmax : maxLocus ((canonicalInvariant n).inv (MarkedIdeal.pullback Φ M) P.tower)
      (geoTransformAlong (MarkedIdeal.pullback Φ M) P.tower).cosupp =
      P.back ⁻¹' maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp := by
    rw [hcos]
    exact ResolutionInvariantSegments.maxLocus_preimage_of_surjective P.back.surjective
      (fun z hz => (canonicalInvariant n).isInvValue.towerIso Φ M hM P.tower T P.back hi hc z hz)
  exact ⟨InvDomainTowerAlong.isInvDomain_pullback Φ hM,hcan,hi,
    fun z => (hi.proj_comm z).symm,hrec,hmax,
    fun hr => (hi.isGeoResolution_iff Φ hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent).mpr hr,
    fun O ha => centresAvoid_of_isTowerIso Φ hi O ha⟩

private theorem filter_nonempty_map_preimage {P Q : Type*} (f : P → Q)
    (hf : Surjective f) (E : List (Set Q)) :
    (E.map (f ⁻¹' ·)).filter (fun H => decide H.Nonempty) =
      (E.filter (fun H => decide H.Nonempty)).map (f ⁻¹' ·) := by
  induction E with
  | nil => rfl
  | cons H E ih =>
    have hh : (f ⁻¹' H).Nonempty ↔ H.Nonempty :=
      ⟨fun ⟨x,hx⟩ => ⟨f x,hx⟩,fun h => h.preimage hf⟩
    by_cases hne : H.Nonempty <;> simp [hh,hne,ih]

private theorem compose_filtered_boundary {A : CMfd.{u} n}
    (κ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A)
    (β : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (E : List (Set Y)) (E₁ : List (Set A)) (E₂ : List (Set Y'))
    (hE : E₁ = E.map (β ⁻¹' ·))
    (hκ : E₂.filter (fun H => decide H.Nonempty) =
      (E₁.filter (fun H => decide H.Nonempty)).map (κ ⁻¹' ·)) :
    E₂.filter (fun H => decide H.Nonempty) =
      (E.filter (fun H => decide H.Nonempty)).map ((κ.trans β) ⁻¹' ·) := by
  rw [hE,filter_nonempty_map_preimage β β.surjective,List.map_map] at hκ
  exact hκ

/-- Original stage data and a genuine base biholomorphism internally give
the UNIQUE actual terminal comparison and its SAME whole filtered boundary. -/
theorem terminal_choice_over_base_across_empty_boundaries
    (M : MarkedIdeal n X) (M' : MarkedIdeal n X') (hM : IsInvDomain n M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (hN : M'.N = Φ ⁻¹' M.N) (hI : M'.ideal = GermIdeal.pullback (m := n) Φ M.ideal)
    (hd : M'.d = M.d)
    (hE : M'.E.filter (fun H => decide H.Nonempty) =
      (M.E.map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty))
    (S : BlowupTower X' Y') (T : BlowupTower X Y)
    (hcS : IsCanonical M' ((canonicalInvariant n).inv M') S)
    (hcT : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hrS : IsGeoResolution M' S) (hrT : IsGeoResolution M T) :
    ∃! η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      (∀ z, T.proj (η z) = Φ (S.proj z)) ∧
      (geoTransformAlong M' S).E.filter (fun H => decide H.Nonempty) =
        ((geoTransformAlong M T).E.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  let P := transport Φ T
  let J := MarkedIdeal.pullback Φ M
  obtain ⟨hJ,hcQ,_hi,hproj,hrec,_hmax,hres,_ha⟩ := canonical_transport_dictionary M hM Φ T hcT
  obtain ⟨κ,⟨hκ,hbκ⟩,_huκ⟩ := terminal_choice_across_empty_boundaries
    J M' hJ hN hI hd hE S P.tower hcS hcQ hrS (hres hrT)
  let η := κ.trans P.back
  have hp : ∀ z, T.proj (η z) = Φ (S.proj z) :=
    fun z => (hproj (κ z)).trans (congrArg Φ (hκ z))
  refine ⟨η,⟨hp,?_⟩,?_⟩
  · exact compose_filtered_boundary κ P.back (geoTransformAlong M T).E
      (geoTransformAlong J P.tower).E (geoTransformAlong M' S).E
      (congrArg MarkedIdeal.E hrec) hbκ
  · intro η' hh
    exact biholomorphisms_eq_of_actual_proj_eq T η' η (fun z => (hh.1 z).trans (hp z).symm)

/-- The actual next-maximum point and avoided open are transported internally;
no source terminality, common index or comparison map is an input. -/
theorem first_meeting_choice_over_base_across_empty_boundaries
    (M : MarkedIdeal n X) (M' : MarkedIdeal n X') (hM : IsInvDomain n M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (hN : M'.N = Φ ⁻¹' M.N) (hI : M'.ideal = GermIdeal.pullback (m := n) Φ M.ideal)
    (hd : M'.d = M.d)
    (hE : M'.E.filter (fun H => decide H.Nonempty) =
      (M.E.map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty))
    (S : BlowupTower X' Y') (T : BlowupTower X Y)
    (hcS : IsCanonical M' ((canonicalInvariant n).inv M') S)
    (hcT : IsCanonical M ((canonicalInvariant n).inv M) T)
    (O : Opens X) (haS : CentresAvoid (baseOpen Φ O) S) (haT : CentresAvoid O T)
    (hmS : ∃ c ∈ maxLocus ((canonicalInvariant n).inv M' S) (geoTransformAlong M' S).cosupp,
      S.proj c ∈ baseOpen Φ O)
    (hmT : ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp,
      T.proj c ∈ O) :
    ∃! η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      (∀ z, T.proj (η z) = Φ (S.proj z)) ∧
      (geoTransformAlong M' S).E.filter (fun H => decide H.Nonempty) =
        ((geoTransformAlong M T).E.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  let P := transport Φ T
  let J := MarkedIdeal.pullback Φ M
  obtain ⟨hJ,hcQ,_hi,hproj,hrec,hmax,_hres,ha⟩ := canonical_transport_dictionary M hM Φ T hcT
  have hmQ : ∃ c ∈ maxLocus ((canonicalInvariant n).inv J P.tower)
      (geoTransformAlong J P.tower).cosupp, P.tower.proj c ∈ baseOpen Φ O := by
    obtain ⟨c,hc,hcO⟩ := hmT
    refine ⟨P.back.symm c,?_,?_⟩
    · rw [hmax]
      change P.back (P.back.symm c) ∈
        maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp
      rw [P.back.apply_symm_apply]
      exact hc
    · change Φ (P.tower.proj (P.back.symm c)) ∈ O
      rw [← hproj,P.back.apply_symm_apply]
      exact hcO
  obtain ⟨κ,⟨hκ,hbκ⟩,_huκ⟩ := first_meeting_choice_across_empty_boundaries
    J M' hJ hN hI hd hE S P.tower hcS hcQ (baseOpen Φ O) haS (ha O haT) hmS hmQ
  let η := κ.trans P.back
  have hp : ∀ z, T.proj (η z) = Φ (S.proj z) :=
    fun z => (hproj (κ z)).trans (congrArg Φ (hκ z))
  refine ⟨η,⟨hp,?_⟩,?_⟩
  · exact compose_filtered_boundary κ P.back (geoTransformAlong M T).E
      (geoTransformAlong J P.tower).E (geoTransformAlong M' S).E
      (congrArg MarkedIdeal.E hrec) hbκ
  · intro η' hh
    exact biholomorphisms_eq_of_actual_proj_eq T η' η (fun z => (hh.1 z).trans (hp z).symm)

end
end Hironaka.HironakaOriginalBoundaryEmptyBaseComparison
