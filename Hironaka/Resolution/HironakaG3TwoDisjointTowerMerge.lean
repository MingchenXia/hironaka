import Hironaka.Resolution.HironakaG3DisjointTowerSecondExtension
import Hironaka.Resolution.HironakaG3AppendEmptyTailComparison
import Hironaka.Resolution.HironakaG3RestrictedAppendEmptyHead
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3TwoDisjointTowerMerge
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  BlowupTowerIsoTail RestrictEmptyTower MarkedIdealTowerTransport HironakaG3EmptyAwareHistory
  HironakaG3DisjointTowerSecondExtension HironakaG3AppendEmptyTailComparison
  HironakaG3RestrictedAppendEmptyHead

theorem two_disjoint_towers_with_actual_comparisons {n : ℕ} {X Y₁ Y₂ : CMfd.{0} n}
    (F₁ F₂ : Set X) (hF₁ : IsClosed F₁) (hF₂ : IsClosed F₂) (hDis : Disjoint F₁ F₂)
    (T₁ : BlowupTower X Y₁) (hT₁ : CentresOver F₁ T₁)
    (T₂ : BlowupTower X Y₂) (hT₂ : CentresOver F₂ T₂) :
    let R : Opens X := ⟨F₁ᶜ,hF₁.isOpen_compl⟩
    ∃ (Z : CMfd.{0} n) (Q : BlowupTower Y₁ Z), CentresOver (T₁.proj ⁻¹' F₂) Q ∧
      (∀ (U : Opens X), Disjoint (U : Set X) F₂ →
        ∃ ψ : (CMfd.of (n := n) (openPreimage (T₁.append Q) U)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage T₁ U)),
          EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) (restrict U (T₁.append Q)) (restrict U T₁) ψ) ∧
      ∃ ψ : (CMfd.of (n := n) (openPreimage (T₁.append Q) R)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage T₂ R)),
        EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) R ∞) (restrict R (T₁.append Q)) (restrict R T₂) ψ := by
  dsimp only
  let R : Opens X := ⟨F₁ᶜ,hF₁.isOpen_compl⟩
  let V : Opens Y₁ := openPreimage T₁ R
  obtain ⟨β,hβ,Z,Q,hQ,e,he⟩ := second_tower_extension_of_disjoint_closed_supports F₁ F₂ hF₁ hF₂ hDis T₁ hT₁ T₂ hT₂
  refine ⟨Z,Q,hQ,?_,?_⟩
  · intro U hUF
    exact restricted_append_comparison_off_tail_support T₁ Q F₂ hQ U hUF
  · have hR : Disjoint (R : Set X) F₁ := disjoint_compl_left
    have hEmpty := isEmptyTower_restrict_of_centresOver R hR T₁ hT₁
    have hTail : IsTowerIso β (restrict V Q) (restrict R T₂)
        (e.symm.trans (transport β (restrict R T₂)).back) := by
      have hh := he.symm.trans (transport_isTowerIso β (restrict R T₂))
      have hBase : (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) V ∞).symm.trans β = β := by
        ext x
        rfl
      rw [hBase] at hh
      exact hh
    exact restricted_append_comparison_of_empty_head T₁ Q R (restrict R T₂) hEmpty β hβ _ hTail
end
end Hironaka.HironakaG3TwoDisjointTowerMerge
