/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.NormalCrossingsWellFormedSublistOriginalExact
import Hironaka.Resolution.HironakaOriginalInvariantEmptyInsertion
import Hironaka.Resolution.HironakaOriginalCrossingValueTransport
import Hironaka.Resolution.HironakaOriginalPureBoundaryIndependentSource
/-!
# Actual canonical stages across literal empty original boundary positions

Finite list induction removes the original empty entries internally. Actual
testness, terminality, whole maximum loci, canonicality and final filtered
boundaries are retained, including the true ambient-dimension-zero branch.
Blueprint: `hironaka-original-boundary-empty-filter-comparison-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalBoundaryEmptyFilterComparison
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism CanonicalCentres
  MonomialInvariantEmptyMember HironakaOriginalInvariantEmptyInsertion
  HironakaOriginalCrossingValueTransport HironakaOriginalTerminalProjectionUniqueness
  HironakaOriginalTerminalChoiceComparison HironakaOriginalFirstMeetingPrefixUniqueness
  HironakaOriginalStoppedBoundaryTransport HironakaOriginalPureBoundaryIndependentSource
  RestrictEmptyTower
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower)
open ResolutionDriver (maxLocus)
variable {n : ℕ} {X Y Y' : CMfd.{u} n}

/-- Literal original boundary filtering; all three other fields are unchanged. -/
def nonemptyBoundary (M : MarkedIdeal n X) : MarkedIdeal n X :=
  {M with E := M.E.filter (fun H => decide H.Nonempty)}

private theorem insert_at_append_length {P : Type*} (A B : List (Set P)) :
    (A++B).insertIdx A.length ∅ = A++∅::B := by
  induction A with
  | nil => rfl
  | cons H A ih => simpa only [List.cons_append,List.length_cons,List.insertIdx_succ_cons] using
      (congrArg (List.cons H) ih)

private theorem filter_value_of_empty_insertion {P α : Type*} (V : List (Set P) → α)
    (hV : ∀ E j, j ≤ E.length → V (E.insertIdx j ∅) = V E) (E : List (Set P)) :
    V (E.filter (fun H => decide H.Nonempty)) = V E := by
  have aux : ∀ B A : List (Set P),
      V (A++B.filter (fun H => decide H.Nonempty)) = V (A++B) := by
    intro B
    induction B with
    | nil => intro A; rfl
    | cons H B ih =>
      intro A
      by_cases hH : H.Nonempty
      · simpa only [List.filter_cons,decide_eq_true hH,reduceIte,List.append_assoc,
          List.singleton_append] using ih (A++[H])
      · have he : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hH
        subst H
        simp only [List.filter_cons,Set.not_nonempty_empty,decide_false,Bool.false_eq_true,reduceIte]
        exact (ih A).trans (by
          have h := hV (A++B) A.length (by simp)
          rw [insert_at_append_length] at h
          exact h.symm)
  simpa only [List.nil_append] using aux E []

private theorem filter_nonempty_insert_empty {P : Type*} (E : List (Set P)) (j : ℕ) :
    (E.insertIdx j ∅).filter (fun H => decide H.Nonempty) = E.filter (fun H => decide H.Nonempty) := by
  induction E generalizing j with
  | nil => cases j <;> simp
  | cons H E ih => cases j with
    | zero => simp
    | succ j => by_cases hH : H.Nonempty <;> simp [hH,ih]

theorem isInvDomain_nonemptyBoundary {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) :
    IsInvDomain k (nonemptyBoundary M) :=
  ⟨NormalCrossingsComparison.isWellFormed_withE hM.isWellFormed List.filter_sublist,
    hM.dimLE,hM.one_le_d,hM.isNonzeroAlongAt⟩

theorem isGeoTestTower_nonemptyBoundary_iff (M : MarkedIdeal n X) (T : BlowupTower X Y) :
    IsGeoTestTower (nonemptyBoundary M) T ↔ IsGeoTestTower M T := by
  apply Iff.of_eq
  exact filter_value_of_empty_insertion (fun E => IsGeoTestTower ({M with E := E}) T)
    (fun E j hj => propext (isGeoTestTower_insertEmpty_iff ({M with E := E}) hj T)) M.E

theorem cosupp_nonemptyBoundary_along (M : MarkedIdeal n X) (T : BlowupTower X Y) :
    (geoTransformAlong (nonemptyBoundary M) T).cosupp = (geoTransformAlong M T).cosupp :=
  filter_value_of_empty_insertion (fun E => (geoTransformAlong ({M with E := E}) T).cosupp)
    (fun E _j hj => cosupp_geoTransformAlong_insertEmpty ({M with E := E}) hj T) M.E

theorem isGeoResolution_nonemptyBoundary_iff (M : MarkedIdeal n X) (T : BlowupTower X Y) :
    IsGeoResolution (nonemptyBoundary M) T ↔ IsGeoResolution M T := by
  change (IsGeoTestTower (nonemptyBoundary M) T ∧ _) ↔ (IsGeoTestTower M T ∧ _)
  rw [isGeoTestTower_nonemptyBoundary_iff,cosupp_nonemptyBoundary_along]

theorem filtered_boundary_nonemptyBoundary_along (M : MarkedIdeal n X) (T : BlowupTower X Y) :
    (geoTransformAlong (nonemptyBoundary M) T).E.filter (fun H => decide H.Nonempty) =
      (geoTransformAlong M T).E.filter (fun H => decide H.Nonempty) := by
  apply filter_value_of_empty_insertion
    (fun E => (geoTransformAlong ({M with E := E}) T).E.filter (fun H => decide H.Nonempty))
    ?_ M.E
  intro E j hj
  rw [show ({M with E := E.insertIdx j ∅} : MarkedIdeal n X) = insertEmpty j ({M with E := E}) from rfl,
    geoTransformAlong_insertEmpty _ hj]
  exact filter_nonempty_insert_empty _ j

private theorem canonical_insertEmpty_iff (M : MarkedIdeal n X) {j : ℕ} (hj : j ≤ M.E.length)
    (T : BlowupTower X Y) :
    IsCanonical (insertEmpty j M) ((canonicalInvariant n).inv (insertEmpty j M)) T ↔
      IsCanonical M ((canonicalInvariant n).inv M) T := by
  cases n with
  | zero =>
    induction T with
    | refl => rfl
    | step T C π hπ ih =>
      change (_ ∧ (C=∅ ∨ C=maxLocus (fun _ => (0 : ℕ)) (geoTransformAlong (insertEmpty j M) T).cosupp)) ↔
        (_ ∧ (C=∅ ∨ C=maxLocus (fun _ => (0 : ℕ)) (geoTransformAlong M T).cosupp))
      rw [ih,cosupp_geoTransformAlong_insertEmpty M hj T]
  | succ n => exact isCanonical_invFamily_insertEmpty_iff (Nat.succ_pos n) (n+1) M hj T

theorem isCanonical_nonemptyBoundary_iff (M : MarkedIdeal n X) (T : BlowupTower X Y) :
    IsCanonical (nonemptyBoundary M) ((canonicalInvariant n).inv (nonemptyBoundary M)) T ↔
      IsCanonical M ((canonicalInvariant n).inv M) T := by
  apply Iff.of_eq
  exact filter_value_of_empty_insertion
    (fun E => IsCanonical ({M with E := E}) ((canonicalInvariant n).inv ({M with E := E})) T)
    (fun E j hj => propext (canonical_insertEmpty_iff ({M with E := E}) hj T)) M.E

theorem maxLocus_nonemptyBoundary (M : MarkedIdeal n X) (T : BlowupTower X Y) (S : Set Y) :
    maxLocus ((canonicalInvariant n).inv (nonemptyBoundary M) T) S =
      maxLocus ((canonicalInvariant n).inv M T) S := by
  apply filter_value_of_empty_insertion
    (fun E => maxLocus ((canonicalInvariant n).inv ({M with E := E}) T) S) ?_ M.E
  intro E j hj
  cases n with
  | zero => rfl
  | succ n => exact maxLocus_invFamily_insertEmpty (Nat.succ_pos n) (n+1) ({M with E := E}) hj T S

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

private theorem all_empty_zero {X Y : CMfd.{u} 0} (M : MarkedIdeal 0 X) (hM : IsInvDomain 0 M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((canonicalInvariant 0).inv M) T) :
    IsEmptyTower T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    refine ⟨ih hc.1,?_⟩
    have ht := (ResolutionInvariantSpec.countCentresMeeting_eq_zero_of_dimLE_zero hM
      ((canonicalInvariant 0).inv M) ∅ T hc.1).1
    have hs := ResolutionInvariantSpec.cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hM T ht
    rcases hc.2 with he | hm
    · exact he
    · rw [hm,hs]
      exact eq_empty_iff_forall_notMem.mpr fun _ hy => hy.1

private theorem avoids_empty (T : BlowupTower X Y) : CentresAvoid (⊥ : Opens X) T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih => exact ⟨ih,by simp⟩

private theorem boundary_of_isTowerIso_id (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {T' : BlowupTower X Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hi : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T' T χ)
    (ht : IsGeoTestTower M T) :
    (geoTransformAlong M T').E = (geoTransformAlong M T).E.map (χ ⁻¹' ·) := by
  have hh := hi.geoTransformAlong_eq (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
    hM.isClosedSubmanifold_N hM.isCoherent ht
  have hpull : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) M = M :=
    ContactCanonicalAlong.pullback_id M hM.isCoherent
  rw [hpull] at hh
  exact congrArg MarkedIdeal.E hh

/-- Actual terminal compression retains the full ordered filtered boundary,
for the same genuine over-base map, including ambient dimension zero. -/
theorem terminal_filtered_boundary_transport
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T' : BlowupTower X Y') (T : BlowupTower X Y)
    (hc' : IsCanonical M ((canonicalInvariant n).inv M) T')
    (hc : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hr' : IsGeoResolution M T') (hr : IsGeoResolution M T)
    (η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (hη : ∀ z, T.proj (η z) = T'.proj z) :
    (geoTransformAlong M T').E.filter (fun H => decide H.Nonempty) =
      ((geoTransformAlong M T).E.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  cases n with
  | zero =>
    have hh := empty_towers_filtered_boundary_transport M hM.isWellFormed.isSNCDivisor.1
      T' T (all_empty_zero M hM T' hc') (all_empty_zero M hM T hc) η hη
    rwa [filter_nonempty_map_preimage η η.surjective] at hh
  | succ n =>
    obtain ⟨Z',Q',χ',F',hne',_hlen',hcQ',hp',hs',_hv',_haQ',_hmQ',hE'⟩ :=
      empty_free_compression_preserves_boundary (Nat.succ_pos n) (n+1) M hM T' hc' ⊥ (avoids_empty T')
    obtain ⟨Z,Q,χ,F,hne,_hlen,hcQ,hp,hs,_hv,_haQ,_hmQ,hE⟩ :=
      empty_free_compression_preserves_boundary (Nat.succ_pos n) (n+1) M hM T hc ⊥ (avoids_empty T)
    have hseg' := isCanonicalSegment_of_actual_nonempty_centres M
      ((invFamily (Nat.succ_pos n) (n+1)).inv M) Q' hcQ' hne'
    have hseg := isCanonicalSegment_of_actual_nonempty_centres M
      ((invFamily (Nat.succ_pos n) (n+1)).inv M) Q hcQ hne
    have htQ' := (invFamily (Nat.succ_pos n) (n+1)).isInvValue.isGeoTestTower_of_isCanonical hM Q' hcQ'
    have htQ := (invFamily (Nat.succ_pos n) (n+1)).isInvValue.isGeoTestTower_of_isCanonical hM Q hcQ
    have hrQ' : IsGeoResolution M Q' := by
      refine ⟨htQ',eq_empty_iff_forall_notMem.mpr fun z hz => ?_⟩
      have hy : χ' z ∈ (geoTransformAlong M T').cosupp := by
        rw [hs']
        simpa only [mem_preimage,χ'.symm_apply_apply] using hz
      rw [hr'.2] at hy
      exact hy
    have hrQ : IsGeoResolution M Q := by
      refine ⟨htQ,eq_empty_iff_forall_notMem.mpr fun z hz => ?_⟩
      have hy : χ z ∈ (geoTransformAlong M T).cosupp := by
        rw [hs]
        simpa only [mem_preimage,χ.symm_apply_apply] using hz
      rw [hr.2] at hy
      exact hy
    let Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel (n+1)) X ∞
    have hpull : MarkedIdeal.pullback Φ M = M := ContactCanonicalAlong.pullback_id M hM.isWellFormed.isCoherent
    obtain ⟨ψ,hi⟩ := CanonicalResolution.exists_isTowerIso_of_isGeoResolution
      (invFamily (Nat.succ_pos n) (n+1)) hM Φ Q' Q
      (by rw [hpull]; exact hseg') hseg (by rw [hpull]; exact hrQ') hrQ
    let η₀ := (χ'.symm.trans ψ).trans χ
    have hη₀ : ∀ y, T.proj (η₀ y) = T'.proj y := by
      intro y
      change T.proj (χ (ψ (χ'.symm y))) = T'.proj y
      rw [hp]
      have hpi := hi.proj_comm (χ'.symm y)
      have hps := hp' (χ'.symm y)
      rw [χ'.apply_symm_apply] at hps
      exact hpi.symm.trans hps.symm
    have heq : η = η₀ := biholomorphisms_eq_of_actual_proj_eq T η η₀
      (fun y => (hη y).trans (hη₀ y).symm)
    rw [heq]
    have hinj : Injective (fun H : Set Y' => χ' ⁻¹' H) := by
      intro H K hHK
      ext z
      have hh := Set.ext_iff.mp hHK (χ'.symm z)
      simpa only [mem_preimage,χ'.apply_symm_apply] using hh
    apply List.map_injective_iff.mpr hinj
    have hIsoE := boundary_of_isTowerIso_id M hM.isWellFormed hi htQ
    calc
      ((geoTransformAlong M T').E.filter (fun H => decide H.Nonempty)).map (χ' ⁻¹' ·) =
          (geoTransformAlong M Q').E.filter (fun H => decide H.Nonempty) := by
        rw [← filter_nonempty_map_preimage χ' χ'.surjective]
        exact hE'
      _ = ((geoTransformAlong M Q).E.filter (fun H => decide H.Nonempty)).map (ψ ⁻¹' ·) := by
        rw [hIsoE,filter_nonempty_map_preimage ψ ψ.surjective]
      _ = (((geoTransformAlong M T).E.filter (fun H => decide H.Nonempty)).map (χ ⁻¹' ·)).map
          (ψ ⁻¹' ·) := by
        rw [← filter_nonempty_map_preimage χ χ.surjective,hE]
      _ = (((geoTransformAlong M T).E.filter (fun H => decide H.Nonempty)).map (η₀ ⁻¹' ·)).map
          (χ' ⁻¹' ·) := by
        simp only [List.map_map]
        congr 1
        funext H
        ext z
        change χ (ψ z) ∈ H ↔ χ (ψ (χ'.symm (χ' z))) ∈ H
        rw [χ'.symm_apply_apply]

private theorem common_filtered_record (M M' : MarkedIdeal n X)
    (hN : M'.N = M.N) (hI : M'.ideal = M.ideal) (hd : M'.d = M.d)
    (hE : M'.E.filter (fun H => decide H.Nonempty) = M.E.filter (fun H => decide H.Nonempty)) :
    nonemptyBoundary M' = nonemptyBoundary M :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN hE hI hd

/-- No insertion history or stage map is input: actual terminal choices for
original records differing only by empty positions have one over-base map,
and this SAME map transports the whole ordered filtered final boundary. -/
theorem terminal_choice_across_empty_boundaries
    (M M' : MarkedIdeal n X) (hM : IsInvDomain n M)
    (hN : M'.N = M.N) (hI : M'.ideal = M.ideal) (hd : M'.d = M.d)
    (hE : M'.E.filter (fun H => decide H.Nonempty) = M.E.filter (fun H => decide H.Nonempty))
    (T' : BlowupTower X Y') (T : BlowupTower X Y)
    (hc' : IsCanonical M' ((canonicalInvariant n).inv M') T')
    (hc : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hr' : IsGeoResolution M' T') (hr : IsGeoResolution M T) :
    ∃! η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      (∀ z, T.proj (η z) = T'.proj z) ∧
      (geoTransformAlong M' T').E.filter (fun H => decide H.Nonempty) =
        ((geoTransformAlong M T).E.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  have heq := common_filtered_record M M' hN hI hd hE
  have hMf := isInvDomain_nonemptyBoundary M hM
  have hcf' := (isCanonical_nonemptyBoundary_iff M' T').mpr hc'
  have hrf' := (isGeoResolution_nonemptyBoundary_iff M' T').mpr hr'
  rw [heq] at hcf' hrf'
  have hcf := (isCanonical_nonemptyBoundary_iff M T).mpr hc
  have hrf := (isGeoResolution_nonemptyBoundary_iff M T).mpr hr
  obtain ⟨η,hη,hu⟩ := original_ambient_terminal_choice_existsUnique
    (nonemptyBoundary M) hMf T' T hcf' hcf hrf' hrf
  refine ⟨η,⟨hη,?_⟩,fun η' hh => hu η' hh.1⟩
  have hh := terminal_filtered_boundary_transport (nonemptyBoundary M) hMf T' T hcf' hcf hrf' hrf η hη
  have hs' : (geoTransformAlong (nonemptyBoundary M) T').E.filter (fun H => decide H.Nonempty) =
      (geoTransformAlong M' T').E.filter (fun H => decide H.Nonempty) := by
    rw [← heq]
    exact filtered_boundary_nonemptyBoundary_along M' T'
  rw [hs',filtered_boundary_nonemptyBoundary_along M T] at hh
  exact hh

/-- Actual first-meeting prefixes compare across the same literal empty-only
initial-boundary change, with no common stopping index or terminality input. -/
theorem first_meeting_choice_across_empty_boundaries
    (M M' : MarkedIdeal n X) (hM : IsInvDomain n M)
    (hN : M'.N = M.N) (hI : M'.ideal = M.ideal) (hd : M'.d = M.d)
    (hE : M'.E.filter (fun H => decide H.Nonempty) = M.E.filter (fun H => decide H.Nonempty))
    (T' : BlowupTower X Y') (T : BlowupTower X Y)
    (hc' : IsCanonical M' ((canonicalInvariant n).inv M') T')
    (hc : IsCanonical M ((canonicalInvariant n).inv M) T)
    (O : Opens X) (ha' : CentresAvoid O T') (ha : CentresAvoid O T)
    (hm' : ∃ c ∈ maxLocus ((canonicalInvariant n).inv M' T') (geoTransformAlong M' T').cosupp,
      T'.proj c ∈ O)
    (hm : ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp,
      T.proj c ∈ O) :
    ∃! η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      (∀ z, T.proj (η z) = T'.proj z) ∧
      (geoTransformAlong M' T').E.filter (fun H => decide H.Nonempty) =
        ((geoTransformAlong M T).E.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  have heq := common_filtered_record M M' hN hI hd hE
  have hMf := isInvDomain_nonemptyBoundary M hM
  have hcf' := (isCanonical_nonemptyBoundary_iff M' T').mpr hc'
  rw [heq] at hcf'
  have hcf := (isCanonical_nonemptyBoundary_iff M T).mpr hc
  have hmf' : ∃ c ∈ maxLocus ((canonicalInvariant n).inv (nonemptyBoundary M) T')
      (geoTransformAlong (nonemptyBoundary M) T').cosupp, T'.proj c ∈ O := by
    rw [← heq]
    simpa only [cosupp_nonemptyBoundary_along,maxLocus_nonemptyBoundary] using hm'
  have hmf : ∃ c ∈ maxLocus ((canonicalInvariant n).inv (nonemptyBoundary M) T)
      (geoTransformAlong (nonemptyBoundary M) T).cosupp, T.proj c ∈ O := by
    simpa only [cosupp_nonemptyBoundary_along,maxLocus_nonemptyBoundary] using hm
  obtain ⟨η,hη,hu⟩ := first_meeting_prefixes_existsUnique_biholomorphism
    (nonemptyBoundary M) hMf T' T hcf' hcf O ha' ha hmf' hmf
  refine ⟨η,⟨hη,?_⟩,fun η' hh => hu η' hh.1⟩
  have hh := first_meeting_boundary_transport (nonemptyBoundary M) hMf T' T hcf' hcf O ha' ha hmf' hmf η hη
  rw [filter_nonempty_map_preimage η η.surjective] at hh
  have hs' : (geoTransformAlong (nonemptyBoundary M) T').E.filter (fun H => decide H.Nonempty) =
      (geoTransformAlong M' T').E.filter (fun H => decide H.Nonempty) := by
    rw [← heq]
    exact filtered_boundary_nonemptyBoundary_along M' T'
  rw [hs',filtered_boundary_nonemptyBoundary_along M T] at hh
  exact hh

end
end Hironaka.HironakaOriginalBoundaryEmptyFilterComparison
