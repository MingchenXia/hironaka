import Hironaka.Resolution.HironakaG3MixedOrderedComparison
import Hironaka.Resolution.HironakaOriginalEmptyHeadPrefix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3MixedFilteredComparison
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HironakaOriginalCanonicalOrderedResolution HironakaOriginalCanonicalPartListResolution
  HironakaOriginalCanonicalSeparationChainChoice HironakaOriginalCanonicalEmptyParts
  HironakaOriginalTerminalProjectionUniqueness HironakaOriginalEmptyHeadPrefix
  HironakaOriginalBoundaryCanonicalPrincipalization HironakaOriginalNCOldStratumStrictEquality
  HironakaG3MixedOrderedSeparation
open ResolutionInvariantExt (IsEmptyTower)
variable {n : ℕ} {X X' D D' : CMfd.{0} n}
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

private theorem closedParts_refl (L : List (Set X × ℕ)) :
    closedParts (strictParts (BlowupTower.refl : BlowupTower X X) L)=closedParts L := by
  simp only [closedParts,strictParts,List.map_map]
  congr 1
  funext p
  apply Prod.ext
  · change closure (strictTransform n (id : X → X) p.1)=closure p.1
    simp only [strictTransform,exceptionalLocus_id,preimage_id,sdiff_empty,closure_closure]
  · rfl

/-- An empty head's actual separator chain is projection-neutral, retaining
every empty boundary slot and all original strict transforms. -/
theorem empty_head_chain_projection {n : ℕ} {X Y : CMfd.{0} n}
    {E : List (Set X)} {A : Set X} {L : List (Set X × ℕ)}
    {T : BlowupTower X Y} {Ef : List (Set Y)}
    (h : CanonicalSeparationChain E A L T Ef) (hA : A = ∅)
    (hEc : ∀ H ∈ E, IsClosed H) :
    IsEmptyTower T ∧ ∃ β : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,
      (∀ z, β z = T.proj z) ∧
      Ef = E.map (β ⁻¹' ·) ++ List.replicate T.length ∅ ∧
      Ef.filter (fun H => decide H.Nonempty) = (E.map (β ⁻¹' ·)).filter (fun H => decide H.Nonempty) ∧
      ∀ P : Set X, strictTransform n T.proj P = β ⁻¹' closure P := by
  have he := separation_chain_empty_of_head_empty h hA
  obtain ⟨β,hβ⟩ := exists_empty_tower_projection T he
  have hfun : (β : Y → X) = T.proj := funext hβ
  let M := boundaryGeometry E
  have hwhole : (geoTransformAlong M T).E = Ef := separation_chain_boundary h M rfl
  have hE : Ef = E.map (β ⁻¹' ·) ++ List.replicate T.length ∅ := by
    rw [← hwhole,boundary_of_all_empty_tower M hEc T he,← hfun]
    rfl
  refine ⟨he,β,hβ,hE,?_,?_⟩
  · rw [hE,List.filter_append]
    simp only [List.filter_replicate,Set.not_nonempty_empty,decide_false,Bool.false_eq_true,reduceIte,List.append_nil]
  · intro P
    rw [← hfun]
    have hexc : exceptionalLocus n β = ∅ := by
      ext x
      simp only [mem_empty_iff_false,iff_false]
      exact MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
        β.contMDiff β.symm.contMDiff β.apply_symm_apply β.symm_apply_apply x
    simp only [strictTransform,hexc,sdiff_empty]
    exact (β.toHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage β.continuous P).symm
private theorem empty_head_neutral
    {E : List (Set X)} {A : Set X} {L : List (Set X × ℕ)}
    {T : BlowupTower X D} {Ef : List (Set D)}
    (h : CanonicalSeparationChain E A L T Ef) (hA : A = ∅) :
    ∃ β : D ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,
      (∀ z, β z = T.proj z) ∧
      Ef.filter (fun H => decide H.Nonempty) =
        (E.map (β ⁻¹' ·)).filter (fun H => decide H.Nonempty) := by
  have hcopy := h
  cases h with
  | nil =>
    refine ⟨Diffeomorph.refl _ _ ∞,fun _ => rfl,?_⟩
    change E.filter (fun H => decide H.Nonempty) = (E.map id).filter (fun H => decide H.Nonempty)
    rw [List.map_id]
  | cons T S hA' hB hM hc hr hs =>
    obtain ⟨_,β,hβ,_,hf,_⟩ := empty_head_chain_projection
      hcopy hA hM.isWellFormed.isSNCDivisor.1
    exact ⟨β,hβ,hf⟩
private def TreeChoice (n k : ℕ) : Prop :=
  ∀ {X X' D D' : CMfd.{0} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)}
    {T : BlowupTower X D} {S : BlowupTower X' D'}
    {Ef : List (Set D)} {Ef' : List (Set D')},
    L.length+L'.length=k →
    E'.filter (fun H => decide H.Nonempty)=(E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·) →
    nonemptyParts (closedParts L')=pulledParts Φ (nonemptyParts (closedParts L)) →
    CanonicalMixedSeparation E L T Ef → CanonicalMixedSeparation E' L' S Ef' →
    ∃ η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z,T.proj (η z)=Φ (S.proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty)=
        (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·)

private theorem empty_source_head (k : ℕ) (ih : ∀ j<k,TreeChoice n j)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)} {A' : Set X'} {d' : ℕ}
    {Ef : List (Set D)} {Ef' : List (Set D')} {C' : CMfd.{0} n}
    {E₁' : List (Set C')} (S₀ : BlowupTower X' C')
    (S : BlowupTower C' D') (T : BlowupTower X D)
    (hsep : CanonicalSeparationChain E' A' L' S₀ E₁')
    (htail : CanonicalMixedSeparation E₁' (strictParts S₀ L') S Ef')
    (hA : A'=∅) (hlen : L.length+((A',d')::L').length=k)
    (hE : E'.filter (fun H => decide H.Nonempty)=(E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (hL : nonemptyParts (closedParts ((A',d')::L'))=pulledParts Φ (nonemptyParts (closedParts L)))
    (hT : CanonicalMixedSeparation E L T Ef) :
    ∃ η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z,T.proj (η z)=Φ ((S₀.append S).proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty)=
        (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  obtain ⟨β,hβ,hfilter⟩ := empty_head_neutral hsep hA
  let Ψ := β.trans Φ
  have htailL : nonemptyParts (closedParts L')=pulledParts Φ (nonemptyParts (closedParts L)) := by
    simpa [closedParts,nonemptyParts,hA] using hL
  have hsq : ∀ z,(BlowupTower.refl : BlowupTower X X).proj (Ψ z)=Φ (S₀.proj z) :=
    fun z => congrArg Φ (hβ z)
  have htailL' := normalized_strictParts_match Φ Ψ S₀ .refl hsq L L' htailL
  rw [closedParts_refl] at htailL'
  have htailE : E₁'.filter (fun H => decide H.Nonempty)=
      (E.filter (fun H => decide H.Nonempty)).map (Ψ ⁻¹' ·) := by
    rw [hfilter,filter_preimage β β.surjective,hE,List.map_map]
    rfl
  have hlt : L.length+(strictParts S₀ L').length<k := by
    simp only [strictParts,List.length_map,List.length_cons] at *
    omega
  obtain ⟨η,hη,hηE⟩ := ih _ hlt Ψ rfl htailE htailL' hT htail
  refine ⟨η,?_,hηE⟩
  intro z
  simpa only [BlowupTower.proj_append,Function.comp_apply] using
    (hη z).trans (congrArg Φ (hβ (S.proj z)))

private theorem empty_target_head (k : ℕ) (ih : ∀ j<k,TreeChoice n j)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)} {A : Set X} {d : ℕ}
    {Ef : List (Set D)} {Ef' : List (Set D')} {C : CMfd.{0} n}
    {E₁ : List (Set C)} (T₀ : BlowupTower X C)
    (T : BlowupTower C D) (S : BlowupTower X' D')
    (hsep : CanonicalSeparationChain E A L T₀ E₁)
    (htail : CanonicalMixedSeparation E₁ (strictParts T₀ L) T Ef)
    (hA : A=∅) (hlen : ((A,d)::L).length+L'.length=k)
    (hE : E'.filter (fun H => decide H.Nonempty)=(E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (hL : nonemptyParts (closedParts L')=pulledParts Φ (nonemptyParts (closedParts ((A,d)::L))))
    (hS : CanonicalMixedSeparation E' L' S Ef') :
    ∃ η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z,(T₀.append T).proj (η z)=Φ (S.proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty)=
        (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  have hEs := boundary_inverse Φ _ _ hE
  have hLs : nonemptyParts (closedParts ((A,d)::L))=pulledParts Φ.symm (nonemptyParts (closedParts L')) := by
    rw [hL,pulledParts_inverse]
  apply comparison_inverse Φ (T₀.append T) S Ef Ef'
  exact empty_source_head k ih Φ.symm T₀ T S hsep htail hA (by omega) hEs hLs hS
private theorem matched_heads (k : ℕ) (ih : ∀ j<k,TreeChoice n j)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)} {A : Set X} {A' : Set X'} {d d' : ℕ}
    {Ef : List (Set D)} {Ef' : List (Set D')} {C C' : CMfd.{0} n}
    {E₁ : List (Set C)} {E₁' : List (Set C')}
    (T₀ : BlowupTower X C) (T : BlowupTower C D)
    (S₀ : BlowupTower X' C') (S : BlowupTower C' D')
    (hsepT : CanonicalSeparationChain E A L T₀ E₁)
    (htailT : CanonicalMixedSeparation E₁ (strictParts T₀ L) T Ef)
    (hsepS : CanonicalSeparationChain E' A' L' S₀ E₁')
    (htailS : CanonicalMixedSeparation E₁' (strictParts S₀ L') S Ef')
    (hA : closure A'=Φ ⁻¹' closure A) (_hd : d'=d)
    (hlen : ((A,d)::L).length+((A',d')::L').length=k)
    (hE : E'.filter (fun H => decide H.Nonempty)=(E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (hL : nonemptyParts (closedParts L')=pulledParts Φ (nonemptyParts (closedParts L))) :
    ∃ η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z,(T₀.append T).proj (η z)=Φ ((S₀.append S).proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty)=
        (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  have hsS : CanonicalSeparationChain E' (Φ ⁻¹' closure A) L' S₀ E₁' := by
    rw [← hA]
    exact separation_chain_closure_head hsepS
  obtain ⟨χ,⟨hχ,hχE,_⟩,_⟩ := separation_chain_choice_over_base_closedParts
    Φ E E' (closure A) L L' hE hL T₀ S₀ (separation_chain_closure_head hsepT) hsS
  have hp := normalized_strictParts_match Φ χ S₀ T₀ hχ L L' hL
  have hlt : (strictParts T₀ L).length+(strictParts S₀ L').length<k := by
    simp only [strictParts,List.length_map,List.length_cons] at *
    omega
  obtain ⟨η,hη,hηE⟩ := ih _ hlt χ rfl hχE hp htailT htailS
  refine ⟨η,?_,hηE⟩
  intro z
  simp only [BlowupTower.proj_append,Function.comp_apply]
  rw [hη z,hχ (S.proj z)]

private theorem tree_choice (k : ℕ) : TreeChoice n k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro X X' D D' Φ E E' L L' T S Ef Ef' hlen hE hL hT hS
    cases hT with
    | nil =>
      cases hS with
      | nil => exact ⟨Φ,fun _ => rfl,hE⟩
      | @cons _ C' _ _ A' d' L' E₁' _ S₀ S hsepS htailS =>
        have hA' : A'=∅ := by
          by_contra hne
          have hn : (closure A').Nonempty := (Set.nonempty_iff_ne_empty.mpr hne).mono subset_closure
          simp [closedParts,nonemptyParts,pulledParts,hn] at hL
        exact empty_source_head k ih Φ S₀ S .refl hsepS htailS hA' hlen hE hL .nil
    | @cons _ C _ _ A d L E₁ _ T₀ T hsepT htailT =>
      cases hS with
      | nil =>
        have hA : A=∅ := by
          by_contra hne
          have hn : (closure A).Nonempty := (Set.nonempty_iff_ne_empty.mpr hne).mono subset_closure
          simp [closedParts,nonemptyParts,pulledParts,hn] at hL
        exact empty_target_head k ih Φ T₀ T .refl hsepT htailT hA hlen hE hL .nil
      | @cons _ C' _ _ A' d' L' E₁' _ S₀ S hsepS htailS =>
        by_cases hA' : A'=∅
        · exact empty_source_head k ih Φ S₀ S (T₀.append T)
            hsepS htailS hA' hlen hE hL (.cons T₀ T hsepT htailT)
        · by_cases hA : A=∅
          · exact empty_target_head k ih Φ T₀ T (S₀.append S)
              hsepT htailT hA hlen hE hL (.cons S₀ S hsepS htailS)
          · have hnA : (closure A).Nonempty := (Set.nonempty_iff_ne_empty.mpr hA).mono subset_closure
            have hnA' : (closure A').Nonempty := (Set.nonempty_iff_ne_empty.mpr hA').mono subset_closure
            have hcons : (closure A',d')::nonemptyParts (closedParts L')=
                (Φ ⁻¹' closure A,d)::pulledParts Φ (nonemptyParts (closedParts L)) := by
              simpa [closedParts,nonemptyParts,pulledParts,hnA,hnA'] using hL
            exact matched_heads k ih Φ T₀ T S₀ S hsepT htailT hsepS htailS
              (congrArg Prod.fst (List.cons.inj hcons).1)
              (congrArg Prod.snd (List.cons.inj hcons).1) hlen hE (List.cons.inj hcons).2

theorem mixed_choice_over_base_closedParts
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {E : List (Set X)} {E' : List (Set X')}
    {L : List (Set X × ℕ)} {L' : List (Set X' × ℕ)}
    {T : BlowupTower X D} {S : BlowupTower X' D'}
    {Ef : List (Set D)} {Ef' : List (Set D')}
    (hT : CanonicalMixedSeparation E L T Ef)
    (hS : CanonicalMixedSeparation E' L' S Ef')
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
end
end Hironaka.HironakaG3MixedFilteredComparison
