/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCanonicalEmptyParts
import Hironaka.Resolution.HironakaOriginalPureHeadChoice

/-!
# The actual empty-head separator and pure-head prefix

No raw-tail closedness hypothesis is needed: every subset transforms
by actual inverse image of its closure under the genuine whole projection.
Blueprint: `hironaka-original-empty-head-prefix-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalEmptyHeadPrefix
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaOriginalCanonicalPartListResolution HironakaOriginalCanonicalOrderedResolution
  HironakaOriginalCanonicalEmptyParts HironakaOriginalIndependentStoppedSource
  HironakaOriginalBoundaryCanonicalPrincipalization
open ResolutionInvariantExt (IsEmptyTower)
variable {n : ℕ} {X D D₁ : CMfd.{u} n}

/-- A real all-empty tower has its entire projection as a genuine biholomorphism. -/
theorem exists_empty_tower_projection (T : BlowupTower X D) (he : IsEmptyTower T) :
    ∃ β : D ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,∀ z,β z=T.proj z := by
  induction T with
  | refl => exact ⟨Diffeomorph.refl _ _ ∞,fun _ => rfl⟩
  | step T C π hπ ih =>
    obtain ⟨heT,rfl⟩ := he
    obtain ⟨χ,hχ⟩ := ih heT
    obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ
    exact ⟨φ.trans χ,fun z => by change χ (φ z)=T.proj (π z);rw [hχ,hφ]⟩

/-- A real empty head forces its SAME separator/head prefix projection neutral,
retaining every chronological empty entry and the closures of arbitrary raw tails. -/
theorem exists_empty_head_prefix_projection
    {E : List (Set X)} {A : Set X} {L : List (Set X × ℕ)}
    {E₁ : List (Set D)} {d : ℕ} {T₀ : BlowupTower X D} {T₁ : BlowupTower D D₁}
    (hsep : CanonicalSeparationChain E A L T₀ E₁)
    (hhead : PureCanonicalHeadStage E₁ (strictTransform n T₀.proj A) d T₁)
    (hA : A=∅) :
    let Ef := (geoTransformAlong (partMarkedIdeal E₁ (strictTransform n T₀.proj A)) T₁).E
    IsEmptyTower (T₀.append T₁) ∧
      ∃ β : D₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,
        (∀ z,β z=(T₀.append T₁).proj z) ∧
        Ef=E.map (β ⁻¹' ·)++List.replicate (T₀.append T₁).length ∅ ∧
        Ef.filter (fun H => decide H.Nonempty)=(E.map (β ⁻¹' ·)).filter (fun H => decide H.Nonempty) ∧
        ∀ P : Set X,strictTransform n (T₀.append T₁).proj P=β ⁻¹' closure P := by
  dsimp only
  have he₀ := separation_chain_empty_of_head_empty hsep hA
  have hA₁ : strictTransform n T₀.proj A=∅ := by rw [hA];simp [strictTransform]
  have hcos : (partMarkedIdeal E₁ (strictTransform n T₀.proj A)).cosupp=∅ :=
    (HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hhead.analytic.isClosed E₁).trans hA₁
  have he₁ := (canonical_histories_empty_of_original_cosupp_empty _ hhead.domain hcos T₁ hhead.canonical).1
  have he := (BlowupTowerSplit.isEmptyTower_append_iff T₀ T₁).mpr ⟨he₀,he₁⟩
  have hEc : ∀ H∈E,IsClosed H := by
    cases hsep with
    | nil => exact hhead.snc.1
    | cons T S hAa hBa hM hc hr hs => exact hM.isWellFormed.isSNCDivisor.1
  obtain ⟨β,hβ⟩ := exists_empty_tower_projection (T₀.append T₁) he
  have hfun : (β : D₁ → X)=(T₀.append T₁).proj := funext hβ
  let M : MarkedIdeal n X := ⟨univ,E,IdealWeightPowers.unitIdeal n X,1⟩
  have hwhole : (geoTransformAlong M (T₀.append T₁)).E=
      (geoTransformAlong (partMarkedIdeal E₁ (strictTransform n T₀.proj A)) T₁).E := by
    rw [geoTransformAlong_append]
    exact geoTransformAlong_boundary_eq _ _ (separation_chain_boundary hsep M rfl) T₁
  have hE : (geoTransformAlong (partMarkedIdeal E₁ (strictTransform n T₀.proj A)) T₁).E=
      E.map (β ⁻¹' ·)++List.replicate (T₀.append T₁).length ∅ := by
    rw [← hwhole,boundary_of_all_empty_tower M hEc (T₀.append T₁) he,← hfun]
  refine ⟨he,β,hβ,hE,?_,?_⟩
  · rw [hE,List.filter_append]
    simp only [List.filter_replicate,Set.not_nonempty_empty,decide_false,Bool.false_eq_true,reduceIte,List.append_nil]
  · intro P
    rw [← hfun]
    have hexc : exceptionalLocus n β=∅ := by
      ext x
      simp only [mem_empty_iff_false,iff_false]
      exact MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
        β.contMDiff β.symm.contMDiff β.apply_symm_apply β.symm_apply_apply x
    simp only [strictTransform,hexc,sdiff_empty]
    exact (β.toHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage β.continuous P).symm

end
end Hironaka.HironakaOriginalEmptyHeadPrefix
