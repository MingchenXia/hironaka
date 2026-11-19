import Hironaka.Resolution.HironakaG8FiniteSpatialRealization

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8NestedVisibleReordering

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaStageCenters HironakaEmbeddedAnalytic
  HironakaG8OccupiedSlotComparison G3UniverseEmptyAwareCore
  HironakaG8FiniteSpatialRealization

variable {n : ℕ} {A B Y Z : CMfd.{0} n}

/-- A nested chart comparison survives a reorder of the larger chart
that preserves the order visible on their common open. -/
theorem nested_visible_reordering
    (U : Opens B) (S : BlowupTower A Y) (T : BlowupTower B Z)
    (φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
    (ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U))
    (hNested : EmptyAwareTowerIso φ S (restrict U T) ψ)
    (target : List ℕ) (hPerm : (List.range T.length).Perm target)
    (hOcc : ∀ i < T.length, (slotFootprint T i).Nonempty)
    (hPreserve : ∀ i j : ℕ, i < j → j < T.length →
      ((slotFootprint T i ∩ slotFootprint T j).Nonempty ∨
        ((U : Set B) ∩ slotFootprint T i).Nonempty ∧
          ((U : Set B) ∩ slotFootprint T j).Nonempty) → target.idxOf i < target.idxOf j)
    (W : Set B) (M : MarkedIdeal n B) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : IsGeoTestTower M T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    ∃ (G : CMfd.{0} n) (R : BlowupTower B G)
      (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G),
      IsGeoTestTower M R ∧ R.proj ∘ e = T.proj ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) R ∧
      (∀ j a, target[j]? = some a → slotFootprint R j = slotFootprint T a) ∧
      ∃ β : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage R U),
        (∀ y, (β y).val = e (ψ y).val) ∧
        EmptyAwareTowerIso φ S (restrict U R) β := by
  obtain ⟨G,R,e,hR,hProj,hStages,hFoot,χ,hχ,hIso⟩ :=
    realize_target_visible_order T U target hPerm hOcc hPreserve W M hM hN hTest hStage
  refine ⟨G,R,e,hR,hProj,hStages,hFoot,ψ.trans χ,fun y => hχ (ψ y),?_⟩
  have h := G3UniverseEmptyAwareCore.trans hNested hIso
  have hφ : φ.trans (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞) = φ := by
    ext x
    rfl
  rwa [hφ] at h

end Hironaka.HironakaG8NestedVisibleReordering

#print axioms Hironaka.HironakaG8NestedVisibleReordering.nested_visible_reordering
