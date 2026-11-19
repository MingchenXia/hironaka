import Hironaka.Resolution.HironakaG4ProcessedMaskWindowComparison
import Hironaka.Resolution.HironakaG3EmptyAwareFullBoundary
import Hironaka.Resolution.HironakaG3EmptyAwareOldSlots
import Hironaka.Resolution.HironakaG34ProcessedMaskEquivariance
import Hironaka.Resolution.HironakaG4RetainedRankTowerIso

/-! An already compared pair of physical prefixes can be extended by the
same processed canonical mask, even when their empty born slots differ. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4ProcessedMaskFilteredPrefix

noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism NormalCrossings HomogenizedGlueingTower
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareFullBoundary
  HironakaG3EmptyAwareOldSlots HironakaG3EmptyAwareBornSlots
  HironakaOriginalBoundaryEmptyFilterComparison HironakaG34JointMaskEquivariance
  HironakaG34ProcessedMaskEquivariance HironakaOriginalTerminalPhysicalComparison
  HironakaG4ProcessedMaskRestriction
  HironakaG4RecordedTowerResidualCompatibility HironakaActualProcessedMaskControlledSum
  HironakaActualProcessedMaskFiniteBlock HironakaSharpActualFiniteChronologicalHistory
  HironakaG4RetainedRankTowerIso HironakaG8DisjointPhaseMerge
  MonomialPartAlong MonomialInvariantEmptyMember RestrictedIdealExtension
  InvertibleIdealQuotient CanonicalCentres ResolutionInvariantSpec

variable {n : ℕ} {X X' Y Y' Z Z' : CMfd.{u} n}

private theorem factor_ignores_empty_born (N H : Set Y) (born : List (Set Y)) :
    (factorOf N H (born.filter (fun B => decide B.Nonempty))).ideal =
      (factorOf N H born).ideal := by
  exact filter_value_of_empty_insertion (fun B => (factorOf N H B).ideal)
    (fun L _j hj => monomialPartAlong_insertIdx_empty N _ L hj) born

set_option maxHeartbeats 650000 in
/-- Both selected spans descend from the same finite set of old row
positions. Unselected rows on either side have no role in the mask. -/
theorem processed_mask_eq_after_filter_of_two_row_embeddings
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    {T' : BlowupTower X' Y'} {ψ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : EmptyAwareTowerIso φ T' T ψ)
    (E' : List (Set X')) {ρ : Type v} (e : ρ ↪ Fin E.length) (e' : ρ ↪ Fin E'.length)
    (hSlots : ∀ i,E'.get (e' i) = φ ⁻¹' E.get (e i)) (P : Finset ρ) :
    let M' := processedMaskMarked (φ ⁻¹' W) E' T' (P.map e')
    let M := processedMaskMarked W E T (P.map e)
    nonemptyBoundary M' = MarkedIdeal.pullback ψ (nonemptyBoundary M) := by
  intro M' M
  let A := geoTransformAlong (geometricTemplate W []) T
  let A' := geoTransformAlong (geometricTemplate (φ ⁻¹' W) []) T'
  let H := fun i : Fin E.length => strictAlong T (E.get i)
  let H' := fun i : Fin E'.length => strictAlong T' (E'.get i)
  have hCarrier : A'.N = ψ ⁻¹' A.N := by
    unfold A A'
    rw [N_geoTransformAlong,N_geoTransformAlong]
    exact emptyAware_strictAlong_eq hIso W hW.1
  have hOld (i : ρ) : H' (e' i) = ψ ⁻¹' H (e i) := by
    unfold H H'
    rw [hSlots i]
    exact emptyAware_strictAlong_eq hIso (E.get (e i)) (hE.1 _ (List.get_mem E (e i)))
  have hBorn : A'.E.filter (fun B => decide B.Nonempty) =
      (A.E.filter (fun B => decide B.Nonempty)).map (ψ ⁻¹' ·) :=
    full_boundary_transport hIso (geometricTemplate (φ ⁻¹' W) [])
      (geometricTemplate W []) rfl (fun _ h => (List.not_mem_nil h).elim)
  have hBorn' : A'.E.filter (fun B => decide B.Nonempty) =
      (A.E.map (ψ ⁻¹' ·)).filter (fun B => decide B.Nonempty) := by
    rw [filter_map_bijection ψ ψ.surjective]
    exact hBorn
  have hRead := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hC (i : Fin E.length) : (vanishingIdeal (n := n) (H i)).IsCoherent :=
    isCoherent_vanishingIdeal_of_mem hn hRead.2.1
      (List.mem_append_left _ (List.mem_map_of_mem (List.get_mem E i)))
  let D := fun i : Fin E.length =>
    (factorOf (ψ ⁻¹' A.N) (ψ ⁻¹' H i) (A.E.map (ψ ⁻¹' ·))).ideal
  let D' := fun i : Fin E'.length => (factorOf A'.N (H' i) A'.E).ideal
  have hFactor (i : ρ) : D' (e' i) = D (e i) := by
    unfold D' D
    rw [hCarrier,hOld,←factor_ignores_empty_born,←factor_ignores_empty_born
      (ψ ⁻¹' A.N) (ψ ⁻¹' H (e i)) (A.E.map (ψ ⁻¹' ·)),hBorn']
  have hPull : MarkedIdeal.pullback ψ M =
      maskSumMarked (ψ ⁻¹' A.N) (fun i => ψ ⁻¹' H i) (A.E.map (ψ ⁻¹' ·)) (P.map e) :=
    pullback_maskSumMarked (isOpenHoloEmbedding_diffeomorph ψ) hRead.1 hC (P.map e)
  have hIdeal : M'.ideal = (MarkedIdeal.pullback ψ M).ideal := by
    rw [hPull]
    change maskSum D' (P.map e') = maskSum D (P.map e)
    rw [mask_sum_map e' P hFactor,mask_sum_map e P (fun _ => rfl)]
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of hCarrier hBorn hIdeal rfl


set_option maxHeartbeats 650000 in
/-- The selected original span only uses the matched old rows. Extra old
labels on one side therefore do not enter a phase for this mapped mask. -/
theorem processed_mask_eq_after_filter_of_row_embedding
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    {T' : BlowupTower X' Y'} {ψ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : EmptyAwareTowerIso φ T' T ψ)
    (E' : List (Set X')) (e : Fin E.length ↪ Fin E'.length)
    (hSlots : ∀ i,E'.get (e i) = φ ⁻¹' E.get i) (P : Finset (Fin E.length)) :
    let M' := processedMaskMarked (φ ⁻¹' W) E' T' (P.map e)
    let M := processedMaskMarked W E T P
    nonemptyBoundary M' = MarkedIdeal.pullback ψ (nonemptyBoundary M) := by

  intro M' M
  simpa only [Finset.map_refl] using
    processed_mask_eq_after_filter_of_two_row_embeddings hn hW hE hdense T hT hFull hIso E'
      (Function.Embedding.refl _) e hSlots P

set_option maxHeartbeats 650000 in
/-- The canonical mask of the rebased prefix has exactly the same original
span and filtered born list. This computation uses the actual prefix
comparison and the original chronological old index bijection. -/
theorem processed_mask_eq_after_filter_of_emptyAware
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    {T' : BlowupTower X' Y'} {ψ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : EmptyAwareTowerIso φ T' T ψ) (P : Finset (Fin E.length)) :
    let E' := E.map (φ ⁻¹' ·)
    let e : Fin E.length ≃ Fin E'.length := finCongr (List.length_map _).symm
    let M' := processedMaskMarked (φ ⁻¹' W) E' T' (P.map e.toEmbedding)
    let M := processedMaskMarked W E T P
    nonemptyBoundary M' = MarkedIdeal.pullback ψ (nonemptyBoundary M) := by

  intro E' e M' M
  refine processed_mask_eq_after_filter_of_row_embedding hn hW hE hdense T hT hFull hIso E'
    e.toEmbedding ?_ P
  intro i
  simp [E',e]

/-- A matched mask of two independently padded lists extends the actual
prefix comparison through the same two physical resolving tails. -/
theorem processed_mask_append_emptyAware_of_two_row_embeddings (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    {T' : BlowupTower X' Y'} {ψ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : EmptyAwareTowerIso φ T' T ψ)
    (E' : List (Set X')) {ρ : Type v} (e : ρ ↪ Fin E.length) (e' : ρ ↪ Fin E'.length)
    (hSlots : ∀ i,E'.get (e' i) = φ ⁻¹' E.get (e i)) (P : Finset ρ)
    (S' : BlowupTower Y' Z') (S : BlowupTower Y Z) :
    let M := processedMaskMarked W E T (P.map e)
    let M' := processedMaskMarked (φ ⁻¹' W) E' T' (P.map e')
    IsInvDomain (n+1) M →
    IsCanonical M' ((invFamily hn (n+1)).inv M') S' →
    IsCanonical M ((invFamily hn (n+1)).inv M) S →
    IsGeoResolution M' S' → IsGeoResolution M S →
    ∃ χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Z,
      EmptyAwareTowerIso φ (T'.append S') (T.append S) χ := by
  intro M M' hM hCan' hCan hRes' hRes
  have hEq : nonemptyBoundary M' = MarkedIdeal.pullback ψ (nonemptyBoundary M) :=
    processed_mask_eq_after_filter_of_two_row_embeddings hn hW hE hdense T hT hFull hIso E' e e' hSlots P
  have hCF' := (isCanonical_invFamily_nonemptyBoundary_iff hn (n+1) M' S').mpr hCan'
  have hRF' := (isGeoResolution_nonemptyBoundary_iff M' S').mpr hRes'
  rw [hEq] at hCF' hRF'
  obtain ⟨χ,hTail⟩ := original_terminal_histories_emptyAware_over_pullback hn
    (nonemptyBoundary M) (isInvDomain_nonemptyBoundary M hM) ψ S' S hCF'
    ((isCanonical_invFamily_nonemptyBoundary_iff hn (n+1) M S).mpr hCan)
    hRF' ((isGeoResolution_nonemptyBoundary_iff M S).mpr hRes)
  exact ⟨χ,emptyAware_append hIso hTail⟩

/-- A phase with corresponding selected old labels extends the physical
prefix comparison, including when one old list has extra labels. -/
theorem processed_mask_append_emptyAware_of_row_embedding (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    {T' : BlowupTower X' Y'} {ψ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : EmptyAwareTowerIso φ T' T ψ)
    (E' : List (Set X')) (e : Fin E.length ↪ Fin E'.length)
    (hSlots : ∀ i,E'.get (e i) = φ ⁻¹' E.get i) (P : Finset (Fin E.length))
    (S' : BlowupTower Y' Z') (S : BlowupTower Y Z) :
    let M := processedMaskMarked W E T P
    let M' := processedMaskMarked (φ ⁻¹' W) E' T' (P.map e)
    IsInvDomain (n+1) M →
    IsCanonical M' ((invFamily hn (n+1)).inv M') S' →
    IsCanonical M ((invFamily hn (n+1)).inv M) S →
    IsGeoResolution M' S' → IsGeoResolution M S →
    ∃ χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Z,
      EmptyAwareTowerIso φ (T'.append S') (T.append S) χ := by

  simpa only [Finset.map_refl] using
    processed_mask_append_emptyAware_of_two_row_embeddings hn hW hE hdense T hT hFull hIso E'
      (Function.Embedding.refl _) e hSlots P S' S

/-- Empty-aware physical comparison of the original prefixes extends through
one aligned canonical mask block on the actual current carrier. -/
theorem processed_mask_append_emptyAware (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    {T' : BlowupTower X' Y'} {ψ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : EmptyAwareTowerIso φ T' T ψ) (P : Finset (Fin E.length))
    (S' : BlowupTower Y' Z') (S : BlowupTower Y Z) :
    let E' := E.map (φ ⁻¹' ·)
    let e : Fin E.length ≃ Fin E'.length := finCongr (List.length_map _).symm
    let M := processedMaskMarked W E T P
    let M' := processedMaskMarked (φ ⁻¹' W) E' T' (P.map e.toEmbedding)
    IsInvDomain (n+1) M →
    IsCanonical M' ((invFamily hn (n+1)).inv M') S' →
    IsCanonical M ((invFamily hn (n+1)).inv M) S →
    IsGeoResolution M' S' → IsGeoResolution M S →
    ∃ χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Z,
      EmptyAwareTowerIso φ (T'.append S') (T.append S) χ := by

  intro E' e M M' hM hCan' hCan hRes' hRes
  exact processed_mask_append_emptyAware_of_row_embedding hn hW hE hdense T hT hFull hIso E'
    e.toEmbedding (fun i => by simp [E',e]) P S' S hM hCan' hCan hRes' hRes

end
end Hironaka.HironakaG4ProcessedMaskFilteredPrefix
