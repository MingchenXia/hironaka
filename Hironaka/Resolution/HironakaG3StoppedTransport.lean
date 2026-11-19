import Hironaka.Resolution.HironakaG3LocalStoppedCover
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3StoppedTransport
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail MarkedIdealTowerTransport
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism CanonicalCentres RestrictEmptyTower
  HironakaOriginalBoundaryEmptyBaseComparison HironakaG3RStoppedOverlap
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)

private theorem avoid_of_iso {n : ℕ} {X X' Y Y' : CMfd.{u} n}
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

/-- A physical tower isomorphism transports the entire stopped condition,
including the actual first-meeting open and resolution alternative. -/
theorem stopped_of_isTowerIso {n : ℕ} {X X' Y Y' : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (O : Opens X) {S : BlowupTower X' Y'} {T : BlowupTower X Y}
    {β : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hi : IsTowerIso Φ S T β) (hT : IsStopped M O T) :
    IsStopped (MarkedIdeal.pullback Φ M) (baseOpen Φ O) S := by
  have hc := HironakaEmbeddedResolutionLocal.isCanonical_of_isTowerIso
    (HironakaFromSeqInvariant.embeddingFields_of_seq (canonicalInvariant n)) hM Φ hi hT.1
  have ht := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hM T hT.1
  have hcos := hi.cosupp_geoTransformAlong Φ hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent ht
  have hmax : maxLocus ((canonicalInvariant n).inv (MarkedIdeal.pullback Φ M) S)
      (geoTransformAlong (MarkedIdeal.pullback Φ M) S).cosupp =
      β ⁻¹' maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp := by
    rw [hcos]
    exact ResolutionInvariantSegments.maxLocus_preimage_of_surjective β.surjective
      (fun z hz => (canonicalInvariant n).isInvValue.towerIso Φ M hM S T β hi hT.1 z hz)
  refine ⟨hc,avoid_of_iso Φ hi O hT.2.1,?_⟩
  rcases hT.2.2 with hm | hr
  · left
    obtain ⟨c,hc,hcO⟩ := hm
    refine ⟨β.symm c,?_,?_⟩
    · rw [hmax]
      change β (β.symm c) ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp
      rwa [β.apply_symm_apply]
    · change Φ (S.proj (β.symm c)) ∈ O
      rw [hi.proj_comm,β.apply_symm_apply]
      exact hcO
  · exact Or.inr ((hi.isGeoResolution_iff Φ hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent).mpr hr)

/-- Transporting a stopped history to a biholomorphic base and back retains
the stopped property of the actual twice-transported tower. -/
theorem stopped_roundtrip {n : ℕ} {X X' Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (O : Opens X) (T : BlowupTower X Y) (hT : IsStopped M O T) :
    IsStopped M O (transport Φ.symm (transport Φ T).tower).tower := by
  have h₁ := transport_isTowerIso Φ T
  have h₂ := transport_isTowerIso Φ.symm (transport Φ T).tower
  have hi := h₂.trans h₁
  have hbase : Φ.symm.trans Φ = Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞ := by
    ext x
    exact Φ.apply_symm_apply x
  rw [hbase] at hi
  have h := stopped_of_isTowerIso M hM (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) O hi hT
  have hMrefl : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) M = M := by
    change MarkedIdeal.pullback (id : X → X) M = M
    exact ContactCanonicalAlong.pullback_id M hM.isWellFormed.isCoherent
  have hOrefl : baseOpen (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) O = O := by
    ext x
    rfl
  rw [hMrefl,hOrefl] at h
  exact h

end
end Hironaka.HironakaG3StoppedTransport
