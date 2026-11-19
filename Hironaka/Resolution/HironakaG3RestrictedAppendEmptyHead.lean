import Hironaka.Resolution.HironakaG3InteriorEmptyComparison
import Hironaka.Resolution.HironakaG3AllEmptyComparison
import Hironaka.Resolution.HironakaG3EmptyAwareComposition
import Hironaka.Blowup.BlowupTowerIsoTail
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3RestrictedAppendEmptyHead
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  BlowupTowerIsoTail HironakaG3EmptyAwareHistory HironakaG3EmptyAwareComposition
  HironakaG3InteriorEmptyComparison HironakaG3AllEmptyComparison
open ResolutionInvariantExt (IsEmptyTower)

theorem restricted_append_comparison_of_empty_head {n : ℕ} {X Y Z Z₂ : CMfd.{0} n}
    (T : BlowupTower X Y) (Q : BlowupTower Y Z) (U : Opens X)
    (S : BlowupTower (CMfd.of (n := n) U) Z₂)
    (hEmpty : IsEmptyTower (restrict U T))
    (β : (CMfd.of (n := n) (openPreimage T U)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) U))
    (hβ : ∀ y, β y = (restrict U T).proj y)
    (ξ : (CMfd.of (n := n) (openPreimage Q (openPreimage T U))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z₂)
    (hTail : IsTowerIso β (restrict (openPreimage T U) Q) S ξ) :
    ∃ ψ : (CMfd.of (n := n) (openPreimage (T.append Q) U)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z₂,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞)
        (restrict U (T.append Q)) S ψ := by
  obtain ⟨γ,hγ⟩ := exists_comparison (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞)
    (restrict U T) (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) hEmpty trivial
  have hγβ : γ = β := by
    apply Diffeomorph.ext
    intro y
    have h := emptyAware_proj_comm hγ y
    change γ y = (restrict U T).proj y at h
    exact h.trans (hβ y).symm
  subst γ
  have hAppend := emptyAware_append_isTowerIso hγ hTail
  have hIso := isTowerIso_restrict_append U T Q
  refine ⟨(opensCongr (openPreimage_append T Q U).symm).trans ξ, ?_⟩
  simpa only [Diffeomorph.refl_trans, BlowupTower.refl_append] using
    trans (emptyAware_of_isTowerIso hIso) hAppend
end
end Hironaka.HironakaG3RestrictedAppendEmptyHead
