/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCanonicalOrderedResolution
import Hironaka.Resolution.HironakaOriginalEmptySumStage

/-!
# Literal boundary bookkeeping and genuine empty-input resolution trees

The same entire chronological boundary depends only on its original list,
not on auxiliary ideals selected by the recursion. Empty filtered input
internally forces an actual all-empty tree with its genuine unique projection.
Blueprint: `hironaka-original-canonical-empty-parts-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCanonicalEmptyParts
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaOriginalCanonicalPartListResolution HironakaOriginalCanonicalOrderedResolution
  HironakaOriginalEmptySumStage HironakaOriginalIndependentStoppedSource
  HironakaOriginalBoundaryCanonicalPrincipalization
open ResolutionInvariantExt (IsEmptyTower)
variable {n : ℕ} {X D : CMfd.{u} n}

/-- The entire geometric boundary of an actual history depends only on its initial boundary. -/
theorem geoTransformAlong_boundary_eq (M N : MarkedIdeal n X) (hE : M.E=N.E)
    (T : BlowupTower X D) : (geoTransformAlong M T).E=(geoTransformAlong N T).E := by
  induction T with
  | refl => exact hE
  | step T C π hπ ih => simp only [geoTransformAlong_step,geoTransform_E,ih]

/-- Every actual auxiliary separator passes exactly the same chronological boundary. -/
theorem separation_chain_boundary {E₀ : List (Set X)} {A : Set X}
    {L : List (Set X × ℕ)} {T : BlowupTower X D} {Ef : List (Set D)}
    (h : CanonicalSeparationChain E₀ A L T Ef) :
    ∀ M : MarkedIdeal n X,M.E=E₀ → (geoTransformAlong M T).E=Ef := by
  induction h with
  | nil => intro M hM;exact hM
  | cons T S hAa hBa hM hc hr hs ih =>
    intro M hE
    rw [geoTransformAlong_append]
    apply ih
    exact geoTransformAlong_boundary_eq M _ hE T

/-- The recorded boundary of the actual whole head/tail tree is the literal full tower boundary. -/
theorem ordered_resolution_boundary {E₀ : List (Set X)} {G : Set X}
    {L : List (Set X × ℕ)} {T : BlowupTower X D} {Ef : List (Set D)}
    (h : CanonicalOrderedResolution E₀ G L T Ef) :
    ∀ M : MarkedIdeal n X,M.E=E₀ → (geoTransformAlong M T).E=Ef := by
  induction h with
  | nil => intro M hM;exact hM
  | cons T₀ T₁ T hsep hhead htail ih =>
    intro M hE
    rw [geoTransformAlong_append,geoTransformAlong_append]
    apply ih
    exact geoTransformAlong_boundary_eq _ _ (separation_chain_boundary hsep M hE) T₁

/-- An empty original head forces ALL centres of the SAME actual sum chain empty. -/
theorem separation_chain_empty_of_head_empty {E₀ : List (Set X)} {A : Set X}
    {L : List (Set X × ℕ)} {T : BlowupTower X D} {Ef : List (Set D)}
    (h : CanonicalSeparationChain E₀ A L T Ef) : A=∅ → IsEmptyTower T := by
  induction h with
  | nil => intro _hA;trivial
  | @cons X E₀ A B e L D Z T S hAa hBa hM hc hr E₁ hs ih =>
    intro hA
    have hint : interior A=∅ := by rw [hA];exact interior_empty
    have hdis : Disjoint A B := by rw [hA];simp
    have heT := (canonical_sum_stage_empty_of_disjoint hAa hBa hint _
      hM.isWellFormed.isSNCDivisor hdis T hc).2.1
    apply (BlowupTowerSplit.isEmptyTower_append_iff T S).mpr
    exact ⟨heT,ih (by rw [hA];simp [strictTransform])⟩

/-- Every empty input carrier forces the genuine ordered tree to contain only actual empty blowups. -/
theorem ordered_resolution_empty_of_all_parts_empty {E₀ : List (Set X)} {G : Set X}
    {L : List (Set X × ℕ)} {T : BlowupTower X D} {Ef : List (Set D)}
    (h : CanonicalOrderedResolution E₀ G L T Ef) :
    (∀ p∈L,p.1=∅) → IsEmptyTower T := by
  induction h with
  | nil => intro _hL;trivial
  | @cons X D₀ D₁ D E₀ G A d L E₁ E₂ T₀ T₁ T hsep hhead htail ih =>
    intro hL
    have hA : A=∅ := hL (A,d) (List.mem_cons_self ..)
    have he₀ := separation_chain_empty_of_head_empty hsep hA
    have hA₁ : strictTransform n T₀.proj A=∅ := by rw [hA];simp [strictTransform]
    have hcos : (partMarkedIdeal E₁ (strictTransform n T₀.proj A)).cosupp=∅ :=
      (HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hhead.analytic.isClosed E₁).trans hA₁
    have he₁ := (canonical_histories_empty_of_original_cosupp_empty _ hhead.domain hcos T₁ hhead.canonical).1
    have he : IsEmptyTower T := by
      apply ih
      intro p hp
      obtain ⟨p₁,hp₁,rfl⟩ := List.mem_map.mp hp
      obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp₁
      rw [hL p₀ (List.mem_cons_of_mem _ hp₀)]
      simp [strictTransform]
    exact (BlowupTowerSplit.isEmptyTower_append_iff T₀ (T₁.append T)).mpr
      ⟨he₀,(BlowupTowerSplit.isEmptyTower_append_iff T₁ T).mpr ⟨he₁,he⟩⟩

private theorem empty_tower_projection (T : BlowupTower X D) (he : IsEmptyTower T) :
    ∃ η : D ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,∀ z,η z=T.proj z := by
  induction T with
  | refl => exact ⟨Diffeomorph.refl _ _ ∞,fun _ => rfl⟩
  | step T C π hπ ih =>
    obtain ⟨heT,rfl⟩ := he
    obtain ⟨χ,hχ⟩ := ih heT
    obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ
    exact ⟨φ.trans χ,fun z => by change χ (φ z)=T.proj (π z);rw [hχ,hφ]⟩

/-- Empty FILTERED original parts internally give the unique projection and exact whole boundary. -/
theorem existsUnique_empty_parts_projection {E₀ : List (Set X)} {G : Set X}
    {L : List (Set X × ℕ)} {T : BlowupTower X D} {Ef : List (Set D)}
    (h : CanonicalOrderedResolution E₀ G L T Ef)
    (hE₀ : ∀ H∈E₀,IsClosed H)
    (hL : L.filter (fun p => decide p.1.Nonempty)=[]) :
    IsEmptyTower T ∧ ∃! η : D ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,
      (∀ z,η z=T.proj z) ∧
      (∀ P : Set X,IsClosed P → strictTransform n T.proj P=η ⁻¹' P) ∧
      Ef=E₀.map (η ⁻¹' ·)++List.replicate T.length ∅ ∧
      Ef.filter (fun H => decide H.Nonempty)=(E₀.map (η ⁻¹' ·)).filter (fun H => decide H.Nonempty) := by
  have he : IsEmptyTower T := by
    apply ordered_resolution_empty_of_all_parts_empty h
    intro p hp
    have hx := (List.filter_eq_nil_iff.mp hL) p hp
    apply Set.not_nonempty_iff_eq_empty.mp
    simpa only [decide_eq_true_eq] using hx
  obtain ⟨η,hη⟩ := empty_tower_projection T he
  have hfun : (η : D → X)=T.proj := funext hη
  let M : MarkedIdeal n X := ⟨univ,E₀,IdealWeightPowers.unitIdeal n X,1⟩
  have hE : Ef=E₀.map (η ⁻¹' ·)++List.replicate T.length ∅ := by
    rw [← ordered_resolution_boundary h M rfl,boundary_of_all_empty_tower M hE₀ T he,← hfun]
  refine ⟨he,η,⟨hη,?_,hE,?_⟩,?_⟩
  · intro P hP
    rw [← hfun]
    have hexc : exceptionalLocus n η=∅ := by
      ext x
      simp only [mem_empty_iff_false,iff_false]
      exact MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
        η.contMDiff η.symm.contMDiff η.apply_symm_apply η.symm_apply_apply x
    simp only [strictTransform,hexc,sdiff_empty,(hP.preimage η.contMDiff.continuous).closure_eq]
  · rw [hE,List.filter_append]
    simp only [List.filter_replicate,Set.not_nonempty_empty,decide_false,Bool.false_eq_true,reduceIte,List.append_nil]
  · intro η' hh
    apply Diffeomorph.ext
    intro z
    exact (hh.1 z).trans (hη z).symm

end
end Hironaka.HironakaOriginalCanonicalEmptyParts
