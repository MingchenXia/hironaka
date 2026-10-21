/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCanonicalPartListResolution
import Hironaka.Resolution.HironakaOriginalCanonicalOrderedResolution
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyBaseComparison
import Hironaka.Resolution.HironakaOriginalEmptySumStage
/-!
# Independent canonical separation chains across empty labelled parts

The actual chains, whole boundaries and original projections are retained.
Internally true carrier closures make the finite comparison induction valid
even for deeper raw carriers not certified analytic until their actual stage.
Blueprint: `hironaka-original-canonical-separation-chain-choice-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCanonicalSeparationChainChoice
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowers BlowupTowerTransforms
  CanonicalCentres HironakaOriginalCanonicalSumSeparation HironakaOriginalCanonicalPartListResolution
  HironakaOriginalBoundaryEmptyBaseComparison HironakaOriginalTerminalProjectionUniqueness
  HironakaOriginalIndependentStoppedSource HironakaOriginalBoundaryCanonicalPrincipalization
  HironakaNormalCrossingsSeparationChoiceComparison HironakaOriginalCanonicalOrderedResolution
  HironakaAdmissibleSequence
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower)
variable {n : ℕ} {X X' D D' : CMfd.{u} n}

/-- The ordinary whole strict transform depends only on the actual carrier closure. -/
theorem strictTransform_closure_eq {f : D → X}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f) (P : Set X) :
    strictTransform n f (closure P) = strictTransform n f P := by
  have hid : strictTransform n (id : X → X) P = closure P := by
    simp only [strictTransform,exceptionalLocus_id,preimage_id,sdiff_empty]
  have h := StrictTransformComposition.strictTransform_comp (f := id) (g := f) contMDiff_id hf P
  simpa only [id_comp,hid] using h.symm

/-- Actual biholomorphic projection squares transport whole strict sets for
ANY original carrier, by the genuine closure/composition dictionary. -/
theorem strictTransform_preimage_of_projection_square
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D)
    {f' : D' → X'} {f : D → X}
    (hf' : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f')
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hc : ∀ z, f (η z) = Φ (f' z)) (P : Set X) :
    strictTransform n f' (Φ ⁻¹' P) = η ⁻¹' strictTransform n f P := by
  have hpre : Φ ⁻¹' closure P = closure (Φ ⁻¹' P) :=
    Φ.toHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage Φ.continuous P
  rw [← strictTransform_closure_eq hf' (Φ ⁻¹' P),
    ← hpre,
    strictTransform_preimage_of_square Φ η hf' hf (closure P) isClosed_closure hc,
    strictTransform_closure_eq hf P]

/-- Actual finite labelled carrier closure, without deletion or relabelling. -/
def closedParts {Z : Type u} [TopologicalSpace Z] (L : List (Set Z × ℕ)) : List (Set Z × ℕ) :=
  L.map (fun p => (closure p.1,p.2))

def nonemptyParts {Z : Type u} (L : List (Set Z × ℕ)) : List (Set Z × ℕ) :=
  L.filter (fun p => decide p.1.Nonempty)

def pulledParts (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (L : List (Set X × ℕ)) : List (Set X' × ℕ) := L.map (fun p => (Φ ⁻¹' p.1,p.2))

private theorem closedParts_pulled (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (L : List (Set X × ℕ)) : closedParts (pulledParts Φ L) = pulledParts Φ (closedParts L) := by
  simp only [closedParts,pulledParts,List.map_map]
  congr 1
  funext p
  exact Prod.ext (Φ.toHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage Φ.continuous p.1).symm rfl

private theorem nonemptyParts_closedParts {Z : Type u} [TopologicalSpace Z]
    (L : List (Set Z × ℕ)) : nonemptyParts (closedParts L) = closedParts (nonemptyParts L) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    have hc : (closure p.1).Nonempty ↔ p.1.Nonempty := closure_nonempty_iff
    by_cases hp : p.1.Nonempty <;> simp [closedParts,nonemptyParts,hc,hp] at ih ⊢ <;> exact ih

private theorem closedParts_strictParts (T : BlowupTower X D) (L : List (Set X × ℕ)) :
    closedParts (strictParts T L) = strictParts T (closedParts L) := by
  simp only [closedParts,strictParts,List.map_map]
  congr 1
  funext p
  apply Prod.ext
  · change closure (strictTransform n T.proj p.1) = strictTransform n T.proj (closure p.1)
    have hs : IsClosed (strictTransform n T.proj p.1) := isClosed_closure
    rw [hs.closure_eq,strictTransform_closure_eq T.contMDiff_proj]
  · rfl

private theorem nonemptyParts_pulled (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (L : List (Set X × ℕ)) : nonemptyParts (pulledParts Φ L) = pulledParts Φ (nonemptyParts L) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    have hp : (Φ ⁻¹' p.1).Nonempty ↔ p.1.Nonempty :=
      ⟨fun ⟨x,hx⟩ => ⟨Φ x,hx⟩,fun h => h.preimage Φ.surjective⟩
    by_cases hne : p.1.Nonempty <;> simp [nonemptyParts,pulledParts,hp,hne] at ih ⊢ <;> exact ih

private theorem nonemptyParts_strictParts_filter (T : BlowupTower X D) (L : List (Set X × ℕ)) :
    nonemptyParts (strictParts T L) = nonemptyParts (strictParts T (nonemptyParts L)) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    by_cases hp : p.1.Nonempty
    · by_cases hs : (strictTransform n T.proj p.1).Nonempty <;>
        simp [strictParts,nonemptyParts,hp,hs] at ih ⊢ <;> exact ih
    · have he : p.1 = ∅ := Set.not_nonempty_iff_eq_empty.mp hp
      simp [strictParts,nonemptyParts,he] at ih ⊢
      exact ih

private theorem strictParts_pulled_of_square
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D)
    (S : BlowupTower X' D') (T : BlowupTower X D)
    (hc : ∀ z, T.proj (η z) = Φ (S.proj z)) (L : List (Set X × ℕ)) :
    strictParts S (pulledParts Φ L) = pulledParts η (strictParts T L) := by
  simp only [strictParts,pulledParts,List.map_map]
  congr 1
  funext p
  exact Prod.ext (strictTransform_preimage_of_projection_square Φ η
    S.contMDiff_proj T.contMDiff_proj hc p.1) rfl

private theorem normal_parts_strict_square
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D)
    (S : BlowupTower X' D') (T : BlowupTower X D)
    (hc : ∀ z, T.proj (η z) = Φ (S.proj z))
    (L' : List (Set X' × ℕ)) (L : List (Set X × ℕ))
    (hL : nonemptyParts (closedParts L') = pulledParts Φ (nonemptyParts (closedParts L))) :
    nonemptyParts (closedParts (strictParts S L')) =
      pulledParts η (nonemptyParts (closedParts (strictParts T L))) := by
  rw [closedParts_strictParts,nonemptyParts_strictParts_filter,hL,
    strictParts_pulled_of_square Φ η S T hc,nonemptyParts_pulled,
    ← nonemptyParts_strictParts_filter,← closedParts_strictParts]

private theorem closedParts_refl (L : List (Set X × ℕ)) :
    closedParts (strictParts (BlowupTower.refl : BlowupTower X X) L) = closedParts L := by
  simp only [closedParts,strictParts,List.map_map]
  congr 1
  funext p
  apply Prod.ext
  · change closure (strictTransform n (id : X → X) p.1) = closure p.1
    simp only [strictTransform,exceptionalLocus_id,preimage_id,sdiff_empty,closure_closure]
  · rfl

private theorem pulledParts_comp {Z : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (Ψ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X') (L : List (Set X × ℕ)) :
    pulledParts Ψ (pulledParts Φ L) = pulledParts (Ψ.trans Φ) L := by
  simp only [pulledParts,List.map_map]
  rfl

private theorem pulledParts_inverse
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (L : List (Set X × ℕ)) : pulledParts Φ.symm (pulledParts Φ L) = L := by
  simp only [pulledParts,List.map_map]
  have hf : (fun p : Set X × ℕ => (Φ.symm ⁻¹' (Φ ⁻¹' p.1),p.2)) = id := by
    funext p
    apply Prod.ext
    · ext x
      simp
    · rfl
  simp only [Function.comp_def] at *
  rw [hf,List.map_id]

private theorem filtered_map (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (E : List (Set X)) :
    (E.map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty) =
      (E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·) := by
  induction E with
  | nil => rfl
  | cons H E ih =>
    have hp : (Φ ⁻¹' H).Nonempty ↔ H.Nonempty :=
      ⟨fun ⟨x,hx⟩ => ⟨Φ x,hx⟩,fun h => h.preimage Φ.surjective⟩
    by_cases hh : H.Nonempty <;> simp [hp,hh,ih]

private theorem boundary_inverse
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (E : List (Set X)) (E' : List (Set X'))
    (hE : E' = E.map (Φ ⁻¹' ·)) : E = E'.map (Φ.symm ⁻¹' ·) := by
  rw [hE,List.map_map]
  have hf : (fun H : Set X => Φ.symm ⁻¹' (Φ ⁻¹' H)) = id := by
    funext H
    ext x
    simp
  simp only [Function.comp_def] at *
  rw [hf,List.map_id]

/-- A given genuine canonical SUM domain with an empty second part forces
the SAME stage to be projection neutral; no additional domain constructor is assumed. -/
theorem empty_sum_stage_projection {A B : Set X}
    (hA : IsComplexAnalyticSubset (n := n) A) (hB : IsComplexAnalyticSubset (n := n) B)
    (hBe : B = ∅) (E : List (Set X))
    (hM : IsInvDomain n (sumMarkedIdeal A B E)) (T : BlowupTower X D)
    (hc : IsCanonical (sumMarkedIdeal A B E)
      ((canonicalInvariant n).inv (sumMarkedIdeal A B E)) T) :
    IsEmptyTower T ∧ ∃! β : D ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,
      (∀ z, β z = T.proj z) ∧
      (∀ P : Set X, IsClosed P → strictTransform n T.proj P = β ⁻¹' P) ∧
      (geoTransformAlong (sumMarkedIdeal A B E) T).E =
        E.map (β ⁻¹' ·) ++ List.replicate T.length ∅ ∧
      (geoTransformAlong (sumMarkedIdeal A B E) T).E.filter (fun H => decide H.Nonempty) =
        (E.filter (fun H => decide H.Nonempty)).map (β ⁻¹' ·) := by
  let M := sumMarkedIdeal A B E
  have hcos : M.cosupp = ∅ := by
    calc
      _ = M.ideal.zeroLocus := cosupp_univ_one hM.isWellFormed.isCoherent
      _ = A ∩ B := HironakaSeparation.zeroLocus_sumIdeal_vanishingIdeal hA.isClosed hB.isClosed
      _ = ∅ := by rw [hBe,Set.inter_empty]
  obtain ⟨he,hr⟩ := canonical_histories_empty_of_original_cosupp_empty M hM hcos T hc
  obtain ⟨β,hβ,_⟩ := original_ambient_terminal_choice_existsUnique M hM T .refl hc
    True.intro hr ⟨True.intro,hcos⟩
  have hf : (β : D → X) = T.proj := funext hβ
  have hwhole : (geoTransformAlong M T).E = E.map (β ⁻¹' ·) ++ List.replicate T.length ∅ := by
    rw [boundary_of_all_empty_tower M hM.isWellFormed.isSNCDivisor.1 T he,← hf]
    rfl
  refine ⟨he,β,⟨hβ,?_,hwhole,?_⟩,?_⟩
  · intro P hP
    have hs := strictTransform_preimage_of_projection_square
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) β T.contMDiff_proj contMDiff_id
      (fun z => hβ z) P
    simpa only [Diffeomorph.coe_refl,preimage_id,strictTransform,exceptionalLocus_id,
      sdiff_empty,hP.closure_eq] using hs
  · rw [hwhole,List.filter_append]
    simp only [List.filter_replicate,Set.not_nonempty_empty,decide_false,
      Bool.false_eq_true,reduceIte,List.append_nil]
    exact filtered_map β E
  · intro β' hh
    apply Diffeomorph.ext
    intro z
    exact (hh.1 z).trans (hβ z).symm

private def ChainChoice (n k : ℕ) : Prop :=
  ∀ {X X' D D' : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')} {A : Set X}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)}
    {T : BlowupTower X D} {S : BlowupTower X' D'} {Ef : List (Set D)} {Ef' : List (Set D')},
    L.length + L'.length = k →
    E'.filter (fun H => decide H.Nonempty) = (E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·) →
    nonemptyParts (closedParts L') = pulledParts Φ (nonemptyParts (closedParts L)) →
    CanonicalSeparationChain E A L T Ef → CanonicalSeparationChain E' (Φ ⁻¹' A) L' S Ef' →
    ∃ η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z, T.proj (η z) = Φ (S.proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty) = (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·)

private theorem empty_source_step (k : ℕ) (ih : ∀ j < k, ChainChoice.{u} n j)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')} {A : Set X}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)} {B' : Set X'} {e' : ℕ}
    {T : BlowupTower X D} {Ef : List (Set D)} {Ef' : List (Set D')}
    {C' : CMfd.{u} n} (S₀ : BlowupTower X' C') (S₁ : BlowupTower C' D')
    (hAa' : IsComplexAnalyticSubset (n := n) (Φ ⁻¹' A))
    (hBa' : IsComplexAnalyticSubset (n := n) B') (hBe : B' = ∅)
    (hM' : IsInvDomain n (sumMarkedIdeal (Φ ⁻¹' A) B' E'))
    (hcS : IsCanonical (sumMarkedIdeal (Φ ⁻¹' A) B' E')
      ((canonicalInvariant n).inv (sumMarkedIdeal (Φ ⁻¹' A) B' E')) S₀)
    (hsS : CanonicalSeparationChain (geoTransformAlong (sumMarkedIdeal (Φ ⁻¹' A) B' E') S₀).E
      (strictTransform n S₀.proj (Φ ⁻¹' A)) (strictParts S₀ L') S₁ Ef')
    (hlen : L.length + ((B',e')::L').length = k)
    (hE : E'.filter (fun H => decide H.Nonempty) = (E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (hL : nonemptyParts (closedParts ((B',e')::L')) = pulledParts Φ (nonemptyParts (closedParts L)))
    (hT : CanonicalSeparationChain E A L T Ef) :
    ∃ η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z, T.proj (η z) = Φ ((S₀.append S₁).proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty) = (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  obtain ⟨_he,β,⟨hp,hstrict,_hwhole,hfilter⟩,_hu⟩ :=
    empty_sum_stage_projection hAa' hBa' hBe E' hM' S₀ hcS
  let Ψ := β.trans Φ
  have hhead : strictTransform n S₀.proj (Φ ⁻¹' A) = Ψ ⁻¹' A := hstrict _ hAa'.isClosed
  have htail : nonemptyParts (closedParts L') = pulledParts Φ (nonemptyParts (closedParts L)) := by
    simpa [closedParts,nonemptyParts,hBe] using hL
  have hsq : ∀ z, (BlowupTower.refl : BlowupTower X X).proj (Ψ z) = Φ (S₀.proj z) :=
    fun z => congrArg Φ (hp z)
  have htail' := normal_parts_strict_square Φ Ψ S₀ .refl hsq L' L htail
  rw [closedParts_refl] at htail'
  have hfilter' : (geoTransformAlong (sumMarkedIdeal (Φ ⁻¹' A) B' E') S₀).E.filter
      (fun H => decide H.Nonempty) = (E.filter (fun H => decide H.Nonempty)).map (Ψ ⁻¹' ·) := by
    rw [hfilter,hE,List.map_map]
    rfl
  have hsS' : CanonicalSeparationChain (geoTransformAlong (sumMarkedIdeal (Φ ⁻¹' A) B' E') S₀).E
      (Ψ ⁻¹' A) (strictParts S₀ L') S₁ Ef' := by rw [← hhead]; exact hsS
  have hlt : L.length + (strictParts S₀ L').length < k := by
    simp only [strictParts,List.length_map,List.length_cons] at *
    omega
  obtain ⟨η,hη,hηE⟩ := ih _ hlt Ψ rfl hfilter' htail' hT hsS'
  refine ⟨η,?_,hηE⟩
  intro z
  simpa only [BlowupTower.proj_append,Function.comp_apply] using
    (hη z).trans (congrArg Φ (hp (S₁.proj z)))

private theorem empty_target_step (k : ℕ) (ih : ∀ j < k, ChainChoice.{u} n j)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')} {A B : Set X} {e : ℕ}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)}
    {S : BlowupTower X' D'} {Ef : List (Set D)} {Ef' : List (Set D')}
    {C : CMfd.{u} n} (T₀ : BlowupTower X C) (T₁ : BlowupTower C D)
    (hAa : IsComplexAnalyticSubset (n := n) A) (hBa : IsComplexAnalyticSubset (n := n) B)
    (hBe : B = ∅) (hM : IsInvDomain n (sumMarkedIdeal A B E))
    (hcT : IsCanonical (sumMarkedIdeal A B E) ((canonicalInvariant n).inv (sumMarkedIdeal A B E)) T₀)
    (hsT : CanonicalSeparationChain (geoTransformAlong (sumMarkedIdeal A B E) T₀).E
      (strictTransform n T₀.proj A) (strictParts T₀ L) T₁ Ef)
    (hlen : ((B,e)::L).length + L'.length = k)
    (hE : E'.filter (fun H => decide H.Nonempty) = (E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (hL : nonemptyParts (closedParts L') = pulledParts Φ (nonemptyParts (closedParts ((B,e)::L))))
    (hS : CanonicalSeparationChain E' (Φ ⁻¹' A) L' S Ef') :
    ∃ η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z, (T₀.append T₁).proj (η z) = Φ (S.proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty) = (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  have hEs := boundary_inverse Φ _ _ hE
  have hLs : nonemptyParts (closedParts ((B,e)::L)) =
      pulledParts Φ.symm (nonemptyParts (closedParts L')) := by
    rw [hL,pulledParts_inverse]
  have hhead : Φ.symm ⁻¹' (Φ ⁻¹' A) = A := by ext z; simp
  have hAa' : IsComplexAnalyticSubset (n := n) (Φ.symm ⁻¹' (Φ ⁻¹' A)) := by rw [hhead]; exact hAa
  have hM' : IsInvDomain n (sumMarkedIdeal (Φ.symm ⁻¹' (Φ ⁻¹' A)) B E) := by rw [hhead]; exact hM
  have hcT' : IsCanonical (sumMarkedIdeal (Φ.symm ⁻¹' (Φ ⁻¹' A)) B E)
      ((canonicalInvariant n).inv (sumMarkedIdeal (Φ.symm ⁻¹' (Φ ⁻¹' A)) B E)) T₀ := by
    rw [hhead]; exact hcT
  have hsT' : CanonicalSeparationChain (geoTransformAlong (sumMarkedIdeal (Φ.symm ⁻¹' (Φ ⁻¹' A)) B E) T₀).E
      (strictTransform n T₀.proj (Φ.symm ⁻¹' (Φ ⁻¹' A))) (strictParts T₀ L) T₁ Ef := by
    rw [hhead]; exact hsT
  obtain ⟨κ,hκ,hκE⟩ := empty_source_step k ih Φ.symm T₀ T₁ hAa' hBa hBe hM' hcT' hsT'
    (by omega) hEs hLs hS
  refine ⟨κ.symm,?_,?_⟩
  · intro z
    have hz := congrArg Φ (hκ (κ.symm z))
    simpa using hz.symm
  · exact boundary_inverse κ _ _ hκE

private theorem matched_steps (k : ℕ) (ih : ∀ j < k, ChainChoice.{u} n j)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')} {A B : Set X} {B' : Set X'} {e e' : ℕ}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)}
    {Ef : List (Set D)} {Ef' : List (Set D')} {C C' : CMfd.{u} n}
    (T₀ : BlowupTower X C) (T₁ : BlowupTower C D) (S₀ : BlowupTower X' C') (S₁ : BlowupTower C' D')
    (hAa : IsComplexAnalyticSubset (n := n) A) (hBa : IsComplexAnalyticSubset (n := n) B)
    (hB : B' = Φ ⁻¹' B)
    (hM : IsInvDomain n (sumMarkedIdeal A B E))
    (hcT : IsCanonical (sumMarkedIdeal A B E) ((canonicalInvariant n).inv (sumMarkedIdeal A B E)) T₀)
    (hcS : IsCanonical (sumMarkedIdeal (Φ ⁻¹' A) B' E')
      ((canonicalInvariant n).inv (sumMarkedIdeal (Φ ⁻¹' A) B' E')) S₀)
    (hrT : IsGeoResolution (sumMarkedIdeal A B E) T₀)
    (hrS : IsGeoResolution (sumMarkedIdeal (Φ ⁻¹' A) B' E') S₀)
    (hsT : CanonicalSeparationChain (geoTransformAlong (sumMarkedIdeal A B E) T₀).E
      (strictTransform n T₀.proj A) (strictParts T₀ L) T₁ Ef)
    (hsS : CanonicalSeparationChain (geoTransformAlong (sumMarkedIdeal (Φ ⁻¹' A) B' E') S₀).E
      (strictTransform n S₀.proj (Φ ⁻¹' A)) (strictParts S₀ L') S₁ Ef')
    (hlen : ((B,e)::L).length + ((B',e')::L').length = k)
    (hE : E'.filter (fun H => decide H.Nonempty) = (E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (hL : nonemptyParts (closedParts L') = pulledParts Φ (nonemptyParts (closedParts L))) :
    ∃ η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z, (T₀.append T₁).proj (η z) = Φ ((S₀.append S₁).proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty) = (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  subst B'
  have hpull := pullback_sumMarkedIdeal_eq hAa hBa E
    (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism Φ)
  have hI : (sumMarkedIdeal (Φ ⁻¹' A) (Φ ⁻¹' B) E').ideal =
      GermIdeal.pullback (m := n) Φ (sumMarkedIdeal A B E).ideal :=
    (congrArg MarkedIdeal.ideal hpull).symm
  have hEb : (sumMarkedIdeal (Φ ⁻¹' A) (Φ ⁻¹' B) E').E.filter (fun H => decide H.Nonempty) =
      ((sumMarkedIdeal A B E).E.map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty) := by
    rw [filtered_map]; exact hE
  obtain ⟨χ,⟨hχ,hχE⟩,_⟩ := terminal_choice_over_base_across_empty_boundaries
    (sumMarkedIdeal A B E) (sumMarkedIdeal (Φ ⁻¹' A) (Φ ⁻¹' B) E') hM Φ
    (by simp [sumMarkedIdeal]) hI rfl hEb S₀ T₀ hcS hcT hrS hrT
  have hhead := strictTransform_preimage_of_projection_square Φ χ S₀.contMDiff_proj T₀.contMDiff_proj hχ A
  have htail := normal_parts_strict_square Φ χ S₀ T₀ hχ L' L hL
  have hsS' : CanonicalSeparationChain (geoTransformAlong (sumMarkedIdeal (Φ ⁻¹' A) (Φ ⁻¹' B) E') S₀).E
      (χ ⁻¹' strictTransform n T₀.proj A) (strictParts S₀ L') S₁ Ef' := by
    rw [← hhead]; exact hsS
  have hlt : (strictParts T₀ L).length + (strictParts S₀ L').length < k := by
    simp only [strictParts,List.length_map,List.length_cons] at *
    omega
  obtain ⟨η,hη,hηE⟩ := ih _ hlt χ rfl hχE htail hsT hsS'
  refine ⟨η,?_,hηE⟩
  intro z
  simp only [BlowupTower.proj_append,Function.comp_apply]
  rw [hη z]
  exact hχ (S₁.proj z)

private theorem chain_choice (k : ℕ) : ChainChoice.{u} n k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro X X' D D' Φ E E' A L L' T S Ef Ef' hlen hE hL hT hS
    cases hS with
    | nil =>
      cases hT with
      | nil => exact ⟨Φ,(fun _ => rfl),hE⟩
      | @cons _ _ _ B e L C _ T₀ T₁ hAa hBa hM hcT hrT _ hsT =>
        have hBe : B = ∅ := by
          by_contra hn
          have hne : B.Nonempty := Set.nonempty_iff_ne_empty.mpr hn
          have hcne : (closure B).Nonempty := hne.mono subset_closure
          simp [closedParts,nonemptyParts,pulledParts,hcne] at hL
        exact empty_target_step k ih Φ T₀ T₁ hAa hBa hBe hM hcT hsT hlen hE hL .nil
    | @cons _ _ _ B' e' L' C' _ S₀ S₁ hAa' hBa' hM' hcS hrS _ hsS =>
      by_cases hBe' : B' = ∅
      · exact empty_source_step k ih Φ S₀ S₁ hAa' hBa' hBe' hM' hcS hsS hlen hE hL hT
      · have hne' : B'.Nonempty := Set.nonempty_iff_ne_empty.mpr hBe'
        have hcne' : (closure B').Nonempty := hne'.mono subset_closure
        cases hT with
        | nil => simp [closedParts,nonemptyParts,pulledParts,hcne'] at hL
        | @cons _ _ _ B e L C _ T₀ T₁ hAa hBa hM hcT hrT _ hsT =>
          by_cases hBe : B = ∅
          · exact empty_target_step k ih Φ T₀ T₁ hAa hBa hBe hM hcT hsT hlen hE hL
              (.cons S₀ S₁ hAa' hBa' hM' hcS hrS hsS)
          · have hne : B.Nonempty := Set.nonempty_iff_ne_empty.mpr hBe
            have hcne : (closure B).Nonempty := hne.mono subset_closure
            have hcons : (closure B',e') :: nonemptyParts (closedParts L') =
                (Φ ⁻¹' closure B,e) :: pulledParts Φ (nonemptyParts (closedParts L)) := by
              simpa [closedParts,nonemptyParts,pulledParts,hcne,hcne'] using hL
            have hB : B' = Φ ⁻¹' B := by
              have hh := congrArg Prod.fst (List.cons.inj hcons).1
              simpa only [hBa'.isClosed.closure_eq,hBa.isClosed.closure_eq] using hh
            exact matched_steps k ih Φ T₀ T₁ S₀ S₁ hAa hBa hB hM hcT hcS hrT hrS hsT hsS hlen hE
              (List.cons.inj hcons).2

/-- Independent real chains on closure-matched ordered labelled parts have
ONE unique whole comparison, including the actual filtered final boundary. -/
theorem separation_chain_choice_over_base_closedParts
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (E : List (Set X)) (E' : List (Set X')) (A : Set X)
    (L : List (Set X × ℕ)) (L' : List (Set X' × ℕ))
    (hE : E'.filter (fun H => decide H.Nonempty) = (E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (hL : nonemptyParts (closedParts L') = pulledParts Φ (nonemptyParts (closedParts L)))
    (T : BlowupTower X D) (S : BlowupTower X' D')
    {Ef : List (Set D)} {Ef' : List (Set D')}
    (hT : CanonicalSeparationChain E A L T Ef)
    (hS : CanonicalSeparationChain E' (Φ ⁻¹' A) L' S Ef') :
    ∃! η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z, T.proj (η z) = Φ (S.proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty) = (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) ∧
      ∀ P : Set X, IsClosed P → strictTransform n S.proj (Φ ⁻¹' P) = η ⁻¹' strictTransform n T.proj P := by
  obtain ⟨η,hη,hηE⟩ := chain_choice (L.length + L'.length) Φ rfl hE hL hT hS
  refine ⟨η,⟨hη,hηE,?_⟩,?_⟩
  · intro P _hP
    exact strictTransform_preimage_of_projection_square Φ η S.contMDiff_proj T.contMDiff_proj hη P
  · intro η' hh
    exact biholomorphisms_eq_of_actual_proj_eq T η' η (fun z => (hh.1 z).trans (hη z).symm)

/-- Literal ordered nonempty-part equality is sufficient; no incoming
closed-carrier normal form or skipped-stage comparison is required. -/
theorem separation_chain_choice_over_base
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (E : List (Set X)) (E' : List (Set X')) (A : Set X)
    (L : List (Set X × ℕ)) (L' : List (Set X' × ℕ))
    (hE : E'.filter (fun H => decide H.Nonempty) = (E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (hL : nonemptyParts L' = pulledParts Φ (nonemptyParts L))
    (T : BlowupTower X D) (S : BlowupTower X' D')
    {Ef : List (Set D)} {Ef' : List (Set D')}
    (hT : CanonicalSeparationChain E A L T Ef)
    (hS : CanonicalSeparationChain E' (Φ ⁻¹' A) L' S Ef') :
    ∃! η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z, T.proj (η z) = Φ (S.proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty) = (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) ∧
      ∀ P : Set X, IsClosed P → strictTransform n S.proj (Φ ⁻¹' P) = η ⁻¹' strictTransform n T.proj P := by
  apply separation_chain_choice_over_base_closedParts Φ E E' A L L' hE ?_ T S hT hS
  rw [nonemptyParts_closedParts,hL,closedParts_pulled,← nonemptyParts_closedParts]

end
end Hironaka.HironakaOriginalCanonicalSeparationChainChoice
