import Hironaka.Resolution.HironakaG3MixedOrderedSeparation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3MixedOrderedComparison
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers
  HironakaOriginalCanonicalPartListResolution HironakaOriginalCanonicalOrderedResolution
  HironakaOriginalCanonicalSeparationChainChoice HironakaOriginalTerminalProjectionUniqueness
  HironakaG3MixedOrderedSeparation

private theorem nonemptyParts_pulled {n : ℕ} {X X' : CMfd.{0} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (L : List (Set X × ℕ)) : nonemptyParts (pulledParts Φ L) = pulledParts Φ (nonemptyParts L) := by
  classical
  induction L with
  | nil => rfl
  | cons p L ih =>
    have hp : (Φ ⁻¹' p.1).Nonempty ↔ p.1.Nonempty :=
      ⟨fun ⟨x,hx⟩ => ⟨Φ x,hx⟩,fun h => h.preimage Φ.surjective⟩
    by_cases hne : p.1.Nonempty <;> simp [nonemptyParts,pulledParts,hp,hne] at ih ⊢ <;> exact ih

private theorem strictParts_pulled_of_square {n : ℕ} {X X' Y Y' : CMfd.{0} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (S : BlowupTower X' Y') (T : BlowupTower X Y)
    (hc : ∀ z, T.proj (η z) = Φ (S.proj z)) (L : List (Set X × ℕ)) :
    strictParts S (pulledParts Φ L) = pulledParts η (strictParts T L) := by
  simp only [strictParts,pulledParts,List.map_map]
  congr 1
  funext p
  exact Prod.ext (strictTransform_preimage_of_projection_square Φ η
    S.contMDiff_proj T.contMDiff_proj hc p.1) rfl

/-- Two actual ordered separator trees with the same literal labelled inputs
have a unique comparison, retaining the final whole boundary and all strict
transforms, even when the individual sum stages contain empty blowups. -/
theorem ordered_mixed_tree_choice {n : ℕ} {X Y : CMfd.{0} n}
    {E : List (Set X)} {L : List (Set X × ℕ)} {T : BlowupTower X Y} {Ef : List (Set Y)}
    (hT : CanonicalMixedSeparation E L T Ef) :
    ∀ {X' Y' : CMfd.{0} n}
      (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
      (E' : List (Set X')) (S : BlowupTower X' Y') {Ef' : List (Set Y')},
      E'.filter (fun H => decide H.Nonempty) = (E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·) →
      CanonicalMixedSeparation E' (pulledParts Φ L) S Ef' →
      ∃! η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
        (∀ z, T.proj (η z) = Φ (S.proj z)) ∧
        Ef'.filter (fun H => decide H.Nonempty) = (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) ∧
        ∀ P : Set X, IsClosed P → strictTransform n S.proj (Φ ⁻¹' P) = η ⁻¹' strictTransform n T.proj P := by
  classical
  induction hT with
  | nil =>
    intro X' Y' Φ E' S Ef' hE hS
    simp only [pulledParts,List.map_nil] at hS
    cases hS
    refine ⟨Φ,⟨fun _ => rfl,hE,?_⟩,?_⟩
    · intro P hP
      simp [strictTransform,exceptionalLocus_id,(hP.preimage Φ.continuous).closure_eq]
    · intro η' hh
      apply Diffeomorph.ext
      intro z
      exact hh.1 z
  | @cons X Y Z E A d L E₁ E₂ T Q hHead hTail ih =>
    intro X' Z' Φ E' S Ef' hE hS
    change CanonicalMixedSeparation E' ((Φ ⁻¹' A,d)::pulledParts Φ L) S Ef' at hS
    cases hS with
    | @cons _ Y' _ _ _ _ _ E₁' _ T' Q' hHead' hTail' =>
      obtain ⟨η₁,⟨hproj₁,hboundary₁,_hstrict₁⟩,_huniq₁⟩ :=
        separation_chain_choice_over_base Φ E E' A L (pulledParts Φ L) hE
          (nonemptyParts_pulled Φ L) T T' hHead hHead'
      have hparts := strictParts_pulled_of_square Φ η₁ T' T hproj₁ L
      rw [hparts] at hTail'
      obtain ⟨η₂,⟨hproj₂,hboundary₂,_hstrict₂⟩,_huniq₂⟩ :=
        ih η₁ E₁' Q' hboundary₁ hTail'
      have hproj : ∀ z, (T.append Q).proj (η₂ z) = Φ ((T'.append Q').proj z) := by
        intro z
        simp only [BlowupTower.proj_append,Function.comp_apply]
        rw [hproj₂,hproj₁]
      refine ⟨η₂,⟨hproj,hboundary₂,?_⟩,?_⟩
      · intro P _hP
        exact strictTransform_preimage_of_projection_square Φ η₂
          (T'.append Q').contMDiff_proj (T.append Q).contMDiff_proj hproj P
      · intro η' hh
        exact biholomorphisms_eq_of_actual_proj_eq (T.append Q) η' η₂ (fun z => (hh.1 z).trans (hproj z).symm)
end
end Hironaka.HironakaG3MixedOrderedComparison
