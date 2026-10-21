/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCanonicalSeparationChainChoice
import Hironaka.Resolution.HironakaOriginalCanonicalEmptyParts
import Hironaka.Resolution.HironakaOriginalPureHeadChoice
import Hironaka.Resolution.HironakaOriginalEmptyHeadPrefix

/-!
# Independent actual ordered-tree choices with empty labelled slots

Whole actual trees are compared over a prescribed base biholomorphism,
retaining their literal positions and entire filtered final boundaries.
Blueprint: `hironaka-original-canonical-ordered-choice-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCanonicalOrderedChoice
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaOriginalCanonicalOrderedResolution HironakaOriginalCanonicalPartListResolution
  HironakaOriginalCanonicalSeparationChainChoice HironakaOriginalCanonicalEmptyParts
  HironakaOriginalPureHeadChoice HironakaOriginalTerminalProjectionUniqueness
  HironakaOriginalBoundaryCanonicalPrincipalization
open ResolutionInvariantExt (IsEmptyTower)
variable {n : ℕ} {X X' D D' : CMfd.{u} n}

private theorem closedParts_pulled
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (L : List (Set X × ℕ)) : closedParts (pulledParts Φ L)=pulledParts Φ (closedParts L) := by
  simp only [closedParts,pulledParts,List.map_map]
  congr 1
  funext p
  exact Prod.ext (Φ.toHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage Φ.continuous p.1).symm rfl

private theorem nonemptyParts_closedParts {Z : Type u} [TopologicalSpace Z]
    (L : List (Set Z × ℕ)) : nonemptyParts (closedParts L)=closedParts (nonemptyParts L) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    have hc : (closure p.1).Nonempty ↔ p.1.Nonempty := closure_nonempty_iff
    by_cases hp : p.1.Nonempty <;> simp [closedParts,nonemptyParts,hc,hp] at ih ⊢ <;> exact ih

private theorem nonemptyParts_pulled
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (L : List (Set X × ℕ)) : nonemptyParts (pulledParts Φ L)=pulledParts Φ (nonemptyParts L) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    have hp : (Φ ⁻¹' p.1).Nonempty ↔ p.1.Nonempty :=
      ⟨fun ⟨x,hx⟩ => ⟨Φ x,hx⟩,fun h => h.preimage Φ.surjective⟩
    by_cases hne : p.1.Nonempty <;> simp [nonemptyParts,pulledParts,hp,hne] at ih ⊢ <;> exact ih

private theorem normalized_strictParts (T : BlowupTower X D) (L : List (Set X × ℕ)) :
    nonemptyParts (closedParts (strictParts T L))=
      nonemptyParts (strictParts T (nonemptyParts (closedParts L))) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    have hc : (closure p.1).Nonempty ↔ p.1.Nonempty := closure_nonempty_iff
    have ht : closure (strictTransform n T.proj p.1)=strictTransform n T.proj p.1 := isClosed_closure.closure_eq
    by_cases hp : p.1.Nonempty
    · by_cases hs : (strictTransform n T.proj p.1).Nonempty <;>
        simpa [strictParts,closedParts,nonemptyParts,hc,hp,hs,
          strictTransform_closure_eq T.contMDiff_proj,ht] using ih
    · have he : p.1=∅ := Set.not_nonempty_iff_eq_empty.mp hp
      simpa [strictParts,closedParts,nonemptyParts,he] using ih

private theorem strictParts_pulled
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D)
    (S : BlowupTower X' D') (T : BlowupTower X D)
    (hc : ∀ z,T.proj (η z)=Φ (S.proj z)) (L : List (Set X × ℕ)) :
    strictParts S (pulledParts Φ L)=pulledParts η (strictParts T L) := by
  simp only [strictParts,pulledParts,List.map_map]
  congr 1
  funext p
  exact Prod.ext (strictTransform_preimage_of_projection_square Φ η S.contMDiff_proj T.contMDiff_proj hc p.1) rfl

private theorem normalized_strictParts_match
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D)
    (S : BlowupTower X' D') (T : BlowupTower X D)
    (hc : ∀ z,T.proj (η z)=Φ (S.proj z))
    (L : List (Set X × ℕ)) (L' : List (Set X' × ℕ))
    (hL : nonemptyParts (closedParts L')=pulledParts Φ (nonemptyParts (closedParts L))) :
    nonemptyParts (closedParts (strictParts S L'))=
      pulledParts η (nonemptyParts (closedParts (strictParts T L))) := by
  rw [normalized_strictParts,normalized_strictParts,hL,strictParts_pulled Φ η S T hc,nonemptyParts_pulled]

private theorem separation_chain_closure_head
    {E : List (Set X)} {A : Set X} {L : List (Set X × ℕ)}
    {T : BlowupTower X D} {Ef : List (Set D)}
    (h : CanonicalSeparationChain E A L T Ef) : CanonicalSeparationChain E (closure A) L T Ef := by
  cases h with
  | nil => exact .nil
  | cons T S hA hB hM hc hr hs =>
    rw [hA.isClosed.closure_eq]
    exact .cons T S hA hB hM hc hr hs

private theorem empty_parts_projection
    {E : List (Set X)} {G : Set X} {L : List (Set X × ℕ)}
    {T : BlowupTower X D} {Ef : List (Set D)}
    (h : CanonicalOrderedResolution E G L T Ef)
    (hL : nonemptyParts (closedParts L)=[]) :
    ∃ β : D ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,
      (∀ z,β z=T.proj z) ∧
      Ef.filter (fun H => decide H.Nonempty)=(E.map (β ⁻¹' ·)).filter (fun H => decide H.Nonempty) := by
  have hn : nonemptyParts L=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro p hp
    have hm : (closure p.1,p.2)∈closedParts (nonemptyParts L) := List.mem_map_of_mem hp
    rw [← nonemptyParts_closedParts L,hL] at hm
    exact List.not_mem_nil hm
  cases h with
  | nil =>
    refine ⟨Diffeomorph.refl _ _ ∞,fun _ => rfl,?_⟩
    change E.filter (fun H => decide H.Nonempty)=(E.map id).filter (fun H => decide H.Nonempty)
    rw [List.map_id]
  | cons T₀ T₁ T hsep hhead htail =>
    have hE : ∀ H∈E,IsClosed H := by
      cases hsep with
      | nil => exact hhead.snc.1
      | cons T S hA hB hM hc hr hs => exact hM.isWellFormed.isSNCDivisor.1
    obtain ⟨_he,β,⟨hβ,_hs,_hE,hf⟩,_hu⟩ := existsUnique_empty_parts_projection
      (.cons T₀ T₁ T hsep hhead htail) hE hn
    exact ⟨β,hβ,hf⟩

private theorem filter_preimage {P Q : Type*} (f : P → Q) (hf : Surjective f)
    (E : List (Set Q)) :
    (E.map (f ⁻¹' ·)).filter (fun H => decide H.Nonempty)=
      (E.filter (fun H => decide H.Nonempty)).map (f ⁻¹' ·) := by
  induction E with
  | nil => rfl
  | cons H E ih =>
    have hh : (f ⁻¹' H).Nonempty ↔ H.Nonempty :=
      ⟨fun ⟨x,hx⟩ => ⟨f x,hx⟩,fun h => h.preimage hf⟩
    by_cases hne : H.Nonempty <;> simp [hh,hne,ih]

private theorem empty_parts_choice
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')} {G : Set X} {G' : Set X'}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)}
    {T : BlowupTower X D} {S : BlowupTower X' D'}
    {Ef : List (Set D)} {Ef' : List (Set D')}
    (hT : CanonicalOrderedResolution E G L T Ef)
    (hS : CanonicalOrderedResolution E' G' L' S Ef')
    (hLt : nonemptyParts (closedParts L)=[]) (hLs : nonemptyParts (closedParts L')=[])
    (hE : E'.filter (fun H => decide H.Nonempty)=
      (E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·)) :
    ∃ η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z,T.proj (η z)=Φ (S.proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty)=
        (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  obtain ⟨β,hpβ,hβ⟩ := empty_parts_projection hT hLt
  obtain ⟨γ,hpγ,hγ⟩ := empty_parts_projection hS hLs
  let η := (γ.trans Φ).trans β.symm
  refine ⟨η,?_,?_⟩
  · intro z
    change T.proj (β.symm (Φ (γ z)))=Φ (S.proj z)
    rw [← hpβ,β.apply_symm_apply,hpγ]
  · rw [hγ,filter_preimage γ γ.surjective,hE,List.map_map,
      hβ,filter_preimage β β.surjective,List.map_map]
    congr 1
    funext H
    ext z
    change Φ (γ z)∈H ↔ β (η z)∈H
    change Φ (γ z)∈H ↔ β (β.symm (Φ (γ z)))∈H
    rw [β.apply_symm_apply]

private theorem pulledParts_inverse
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (L : List (Set X × ℕ)) : pulledParts Φ.symm (pulledParts Φ L)=L := by
  simp only [pulledParts,List.map_map,Function.comp_def]
  have hf : (fun p : Set X × ℕ => (Φ.symm ⁻¹' (Φ ⁻¹' p.1),p.2))=id := by
    funext p
    apply Prod.ext
    · ext x
      simp
    · rfl
  rw [hf,List.map_id]

private theorem boundary_inverse
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (E : List (Set X)) (E' : List (Set X')) (hE : E'=E.map (Φ ⁻¹' ·)) :
    E=E'.map (Φ.symm ⁻¹' ·) := by
  rw [hE,List.map_map]
  have hf : (fun H : Set X => Φ.symm ⁻¹' (Φ ⁻¹' H))=id := by
    funext H
    ext x
    simp
  simp only [Function.comp_def] at *
  rw [hf,List.map_id]

private theorem comparison_inverse
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (T : BlowupTower X D) (S : BlowupTower X' D')
    (Ef : List (Set D)) (Ef' : List (Set D'))
    (h : ∃ η : D ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D',
      (∀ z,S.proj (η z)=Φ.symm (T.proj z)) ∧
      Ef.filter (fun H => decide H.Nonempty)=
        (Ef'.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·)) :
    ∃ η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z,T.proj (η z)=Φ (S.proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty)=
        (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  obtain ⟨η,hp,hb⟩ := h
  refine ⟨η.symm,?_,boundary_inverse η _ _ hb⟩
  intro z
  apply Φ.symm.injective
  change Φ.symm (T.proj (η.symm z))=Φ.symm (Φ (S.proj z))
  rw [Φ.symm_apply_apply]
  simpa only [η.apply_symm_apply] using (hp (η.symm z)).symm

private theorem strictParts_append {Z : CMfd.{u} n}
    (T : BlowupTower X D) (R : BlowupTower D Z) (L : List (Set X × ℕ)) :
    strictParts R (strictParts T L)=strictParts (T.append R) L := by
  simp only [strictParts,List.map_map]
  congr 1
  funext p
  apply Prod.ext
  · change strictTransform n R.proj (strictTransform n T.proj p.1)=
      strictTransform n (T.append R).proj p.1
    rw [BlowupTower.proj_append]
    exact (StrictTransformComposition.strictTransform_comp T.contMDiff_proj R.contMDiff_proj p.1).symm
  · rfl

private theorem closedParts_refl (L : List (Set X × ℕ)) :
    closedParts (strictParts (BlowupTower.refl : BlowupTower X X) L)=closedParts L := by
  simp only [closedParts,strictParts,List.map_map]
  congr 1
  funext p
  apply Prod.ext
  · change closure (strictTransform n (id : X → X) p.1)=closure p.1
    simp only [strictTransform,exceptionalLocus_id,preimage_id,sdiff_empty,closure_closure]
  · rfl

private def TreeChoice (n k : ℕ) : Prop :=
  ∀ {X X' D D' : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')} {G : Set X} {G' : Set X'}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)}
    {T : BlowupTower X D} {S : BlowupTower X' D'}
    {Ef : List (Set D)} {Ef' : List (Set D')},
    L.length+L'.length=k →
    E'.filter (fun H => decide H.Nonempty)=(E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·) →
    nonemptyParts (closedParts L')=pulledParts Φ (nonemptyParts (closedParts L)) →
    CanonicalOrderedResolution E G L T Ef → CanonicalOrderedResolution E' G' L' S Ef' →
    ∃ η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z,T.proj (η z)=Φ (S.proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty)=
        (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·)

private theorem empty_source_head (k : ℕ) (ih : ∀ j<k,TreeChoice.{u} n j)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')} {G : Set X} {G' : Set X'}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)} {A' : Set X'} {d' : ℕ}
    {Ef : List (Set D)} {Ef' : List (Set D')} {C₀' C₁' : CMfd.{u} n}
    {E₁' : List (Set C₀')} (S₀ : BlowupTower X' C₀') (S₁ : BlowupTower C₀' C₁')
    (S : BlowupTower C₁' D') (T : BlowupTower X D)
    (hsep : CanonicalSeparationChain E' A' L' S₀ E₁')
    (hhead : PureCanonicalHeadStage E₁' (strictTransform n S₀.proj A') d' S₁)
    (htail : CanonicalOrderedResolution
      (geoTransformAlong (partMarkedIdeal E₁' (strictTransform n S₀.proj A')) S₁).E
      (S₁.proj ⁻¹' (S₀.proj ⁻¹' G') ∩ partsUnion (strictParts S₁ (strictParts S₀ L')))
      (strictParts S₁ (strictParts S₀ L')) S Ef')
    (hA : A'=∅) (hlen : L.length+((A',d')::L').length=k)
    (hE : E'.filter (fun H => decide H.Nonempty)=(E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (hL : nonemptyParts (closedParts ((A',d')::L'))=pulledParts Φ (nonemptyParts (closedParts L)))
    (hT : CanonicalOrderedResolution E G L T Ef) :
    ∃ η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z,T.proj (η z)=Φ ((S₀.append (S₁.append S)).proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty)=
        (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  obtain ⟨_he,β,hβ,_hwhole,hfilter,_hstrict⟩ :=
    HironakaOriginalEmptyHeadPrefix.exists_empty_head_prefix_projection hsep hhead hA
  let Ψ := β.trans Φ
  have htailL : nonemptyParts (closedParts L')=pulledParts Φ (nonemptyParts (closedParts L)) := by
    simpa [closedParts,nonemptyParts,hA] using hL
  have hsq : ∀ z,(BlowupTower.refl : BlowupTower X X).proj (Ψ z)=Φ ((S₀.append S₁).proj z) :=
    fun z => congrArg Φ (hβ z)
  have htailL' := normalized_strictParts_match Φ Ψ (S₀.append S₁) .refl hsq L L' htailL
  rw [closedParts_refl,← strictParts_append] at htailL'
  have htailE : (geoTransformAlong (partMarkedIdeal E₁' (strictTransform n S₀.proj A')) S₁).E.filter
      (fun H => decide H.Nonempty)=(E.filter (fun H => decide H.Nonempty)).map (Ψ ⁻¹' ·) := by
    rw [hfilter,filter_preimage β β.surjective,hE,List.map_map]
    rfl
  have hlt : L.length+(strictParts S₁ (strictParts S₀ L')).length<k := by
    simp only [strictParts,List.length_map,List.length_cons] at *
    omega
  obtain ⟨η,hη,hηE⟩ := ih _ hlt Ψ rfl htailE htailL' hT htail
  refine ⟨η,?_,hηE⟩
  intro z
  simpa only [BlowupTower.proj_append,Function.comp_apply] using
    (hη z).trans (congrArg Φ (hβ (S.proj z)))

private theorem empty_target_head (k : ℕ) (ih : ∀ j<k,TreeChoice.{u} n j)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')} {G : Set X} {G' : Set X'}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)} {A : Set X} {d : ℕ}
    {Ef : List (Set D)} {Ef' : List (Set D')} {C₀ C₁ : CMfd.{u} n}
    {E₁ : List (Set C₀)} (T₀ : BlowupTower X C₀) (T₁ : BlowupTower C₀ C₁)
    (T : BlowupTower C₁ D) (S : BlowupTower X' D')
    (hsep : CanonicalSeparationChain E A L T₀ E₁)
    (hhead : PureCanonicalHeadStage E₁ (strictTransform n T₀.proj A) d T₁)
    (htail : CanonicalOrderedResolution
      (geoTransformAlong (partMarkedIdeal E₁ (strictTransform n T₀.proj A)) T₁).E
      (T₁.proj ⁻¹' (T₀.proj ⁻¹' G) ∩ partsUnion (strictParts T₁ (strictParts T₀ L)))
      (strictParts T₁ (strictParts T₀ L)) T Ef)
    (hA : A=∅) (hlen : ((A,d)::L).length+L'.length=k)
    (hE : E'.filter (fun H => decide H.Nonempty)=(E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (hL : nonemptyParts (closedParts L')=pulledParts Φ (nonemptyParts (closedParts ((A,d)::L))))
    (hS : CanonicalOrderedResolution E' G' L' S Ef') :
    ∃ η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z,(T₀.append (T₁.append T)).proj (η z)=Φ (S.proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty)=
        (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  have hEs := boundary_inverse Φ _ _ hE
  have hLs : nonemptyParts (closedParts ((A,d)::L))=pulledParts Φ.symm (nonemptyParts (closedParts L')) := by
    rw [hL,pulledParts_inverse]
  apply comparison_inverse Φ (T₀.append (T₁.append T)) S Ef Ef'
  exact empty_source_head k ih Φ.symm T₀ T₁ T S hsep hhead htail hA (by omega) hEs hLs hS

private theorem matched_heads (k : ℕ) (ih : ∀ j<k,TreeChoice.{u} n j)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')} {G : Set X} {G' : Set X'}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)} {A : Set X} {A' : Set X'} {d d' : ℕ}
    {Ef : List (Set D)} {Ef' : List (Set D')} {C₀ C₁ C₀' C₁' : CMfd.{u} n}
    {E₁ : List (Set C₀)} {E₁' : List (Set C₀')}
    (T₀ : BlowupTower X C₀) (T₁ : BlowupTower C₀ C₁) (T : BlowupTower C₁ D)
    (S₀ : BlowupTower X' C₀') (S₁ : BlowupTower C₀' C₁') (S : BlowupTower C₁' D')
    (hsepT : CanonicalSeparationChain E A L T₀ E₁)
    (hheadT : PureCanonicalHeadStage E₁ (strictTransform n T₀.proj A) d T₁)
    (htailT : CanonicalOrderedResolution
      (geoTransformAlong (partMarkedIdeal E₁ (strictTransform n T₀.proj A)) T₁).E
      (T₁.proj ⁻¹' (T₀.proj ⁻¹' G) ∩ partsUnion (strictParts T₁ (strictParts T₀ L)))
      (strictParts T₁ (strictParts T₀ L)) T Ef)
    (hsepS : CanonicalSeparationChain E' A' L' S₀ E₁')
    (hheadS : PureCanonicalHeadStage E₁' (strictTransform n S₀.proj A') d' S₁)
    (htailS : CanonicalOrderedResolution
      (geoTransformAlong (partMarkedIdeal E₁' (strictTransform n S₀.proj A')) S₁).E
      (S₁.proj ⁻¹' (S₀.proj ⁻¹' G') ∩ partsUnion (strictParts S₁ (strictParts S₀ L')))
      (strictParts S₁ (strictParts S₀ L')) S Ef')
    (hA : closure A'=Φ ⁻¹' closure A) (hd : d'=d)
    (hlen : ((A,d)::L).length+((A',d')::L').length=k)
    (hE : E'.filter (fun H => decide H.Nonempty)=(E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (hL : nonemptyParts (closedParts L')=pulledParts Φ (nonemptyParts (closedParts L))) :
    ∃ η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z,(T₀.append (T₁.append T)).proj (η z)=Φ ((S₀.append (S₁.append S)).proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty)=
        (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  subst d'
  have hsS : CanonicalSeparationChain E' (Φ ⁻¹' closure A) L' S₀ E₁' := by
    rw [← hA]
    exact separation_chain_closure_head hsepS
  obtain ⟨χ,⟨hχ,hχE,_hχstrict⟩,_huχ⟩ := separation_chain_choice_over_base_closedParts
    Φ E E' (closure A) L L' hE hL T₀ S₀ (separation_chain_closure_head hsepT) hsS
  have hhead : strictTransform n S₀.proj A'=χ ⁻¹' strictTransform n T₀.proj A := by
    rw [← strictTransform_closure_eq S₀.contMDiff_proj A',hA,
      strictTransform_preimage_of_projection_square Φ χ S₀.contMDiff_proj T₀.contMDiff_proj hχ,
      strictTransform_closure_eq T₀.contMDiff_proj A]
  have hhS : PureCanonicalHeadStage E₁' (χ ⁻¹' strictTransform n T₀.proj A) d S₁ := by
    rw [← hhead]
    exact hheadS
  have hχEb : E₁'.filter (fun H => decide H.Nonempty)=
      (E₁.map (χ ⁻¹' ·)).filter (fun H => decide H.Nonempty) := by
    rw [filter_preimage χ χ.surjective]
    exact hχE
  obtain ⟨ψ,⟨hψ,hψE,_hψstrict⟩,_huψ⟩ :=
    existsUnique_pure_head_choice_over_base χ hheadT hhS hχEb
  rw [← hhead] at hψE
  have hp₀ := normalized_strictParts_match Φ χ S₀ T₀ hχ L L' hL
  have hp₁ := normalized_strictParts_match χ ψ S₁ T₁ hψ
    (strictParts T₀ L) (strictParts S₀ L') hp₀
  have hlt : (strictParts T₁ (strictParts T₀ L)).length+
      (strictParts S₁ (strictParts S₀ L')).length<k := by
    simp only [strictParts,List.length_map,List.length_cons] at *
    omega
  obtain ⟨η,hη,hηE⟩ := ih _ hlt ψ rfl hψE hp₁ htailT htailS
  refine ⟨η,?_,hηE⟩
  intro z
  simp only [BlowupTower.proj_append,Function.comp_apply]
  rw [hη z,hψ (S.proj z)]
  exact hχ (S₁.proj (S.proj z))

private theorem tree_choice (k : ℕ) : TreeChoice.{u} n k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro X X' D D' Φ E E' G G' L L' T S Ef Ef' hlen hE hL hT hS
    by_cases hLt : nonemptyParts (closedParts L)=[]
    · have hLs : nonemptyParts (closedParts L')=[] := by
        simpa only [hLt,pulledParts,List.map_nil] using hL
      exact empty_parts_choice Φ hT hS hLt hLs hE
    · cases hT with
      | nil => simp [closedParts,nonemptyParts] at hLt
      | @cons _ C₀ C₁ _ _ _ A d L E₁ _ T₀ T₁ T hsepT hheadT htailT =>
        cases hS with
        | nil =>
          have hp : pulledParts Φ (nonemptyParts (closedParts ((A,d)::L)))=[] := hL.symm
          simp only [pulledParts,List.map_eq_nil_iff] at hp
          exact (hLt hp).elim
        | @cons _ C₀' C₁' _ _ _ A' d' L' E₁' _ S₀ S₁ S hsepS hheadS htailS =>
          by_cases hA' : A'=∅
          · exact empty_source_head k ih Φ S₀ S₁ S (T₀.append (T₁.append T))
              hsepS hheadS htailS hA' hlen hE hL (.cons T₀ T₁ T hsepT hheadT htailT)
          · by_cases hA : A=∅
            · exact empty_target_head k ih Φ T₀ T₁ T (S₀.append (S₁.append S))
                hsepT hheadT htailT hA hlen hE hL (.cons S₀ S₁ S hsepS hheadS htailS)
            · have hnA : (closure A).Nonempty := (Set.nonempty_iff_ne_empty.mpr hA).mono subset_closure
              have hnA' : (closure A').Nonempty := (Set.nonempty_iff_ne_empty.mpr hA').mono subset_closure
              have hcons : (closure A',d')::nonemptyParts (closedParts L')=
                  (Φ ⁻¹' closure A,d)::pulledParts Φ (nonemptyParts (closedParts L)) := by
                simpa [closedParts,nonemptyParts,pulledParts,hnA,hnA'] using hL
              exact matched_heads k ih Φ T₀ T₁ T S₀ S₁ S hsepT hheadT htailT hsepS hheadS htailS
                (congrArg Prod.fst (List.cons.inj hcons).1)
                (congrArg Prod.snd (List.cons.inj hcons).1) hlen hE (List.cons.inj hcons).2

/-- Any two actual closure-matched ordered trees internally have one unique
whole geometric comparison, retaining their actual filtered final boundary. -/
theorem ordered_choice_over_base_closedParts
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')} {G : Set X} {G' : Set X'}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)}
    {T : BlowupTower X D} {S : BlowupTower X' D'}
    {Ef : List (Set D)} {Ef' : List (Set D')}
    (hT : CanonicalOrderedResolution E G L T Ef)
    (hS : CanonicalOrderedResolution E' G' L' S Ef')
    (hE : E'.filter (fun H => decide H.Nonempty)=(E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (hL : nonemptyParts (closedParts L')=pulledParts Φ (nonemptyParts (closedParts L))) :
    ∃! η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z,T.proj (η z)=Φ (S.proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty)=
        (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) ∧
      ∀ P : Set X,strictTransform n S.proj (Φ ⁻¹' P)=η ⁻¹' strictTransform n T.proj P := by
  obtain ⟨η,hη,hηE⟩ := tree_choice (L.length+L'.length) Φ rfl hE hL hT hS
  refine ⟨η,⟨hη,hηE,?_⟩,?_⟩
  · intro P
    exact strictTransform_preimage_of_projection_square Φ η S.contMDiff_proj T.contMDiff_proj hη P
  · intro η' hh
    exact biholomorphisms_eq_of_actual_proj_eq T η' η (fun z => (hh.1 z).trans (hη z).symm)

/-- Literal matching of ordered nonempty inputs suffices, including genuinely
different empty labelled slots and empty chronological boundary positions. -/
theorem ordered_choice_over_base
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')} {G : Set X} {G' : Set X'}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)}
    {T : BlowupTower X D} {S : BlowupTower X' D'}
    {Ef : List (Set D)} {Ef' : List (Set D')}
    (hT : CanonicalOrderedResolution E G L T Ef)
    (hS : CanonicalOrderedResolution E' G' L' S Ef')
    (hE : E'.filter (fun H => decide H.Nonempty)=(E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (hL : nonemptyParts L'=pulledParts Φ (nonemptyParts L)) :
    ∃! η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z,T.proj (η z)=Φ (S.proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty)=
        (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) ∧
      ∀ P : Set X,strictTransform n S.proj (Φ ⁻¹' P)=η ⁻¹' strictTransform n T.proj P := by
  apply ordered_choice_over_base_closedParts Φ hT hS hE
  rw [nonemptyParts_closedParts,hL,closedParts_pulled,← nonemptyParts_closedParts]

end
end Hironaka.HironakaOriginalCanonicalOrderedChoice
