import Hironaka.Resolution.HironakaG8MatchedVisibleSwap

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8MatchedSwapFullHistory

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail HironakaG8MatchedVisibleSwap

variable {n : ℕ} {A B X Y Z X' Y' Z' : CMfd.{0} n}

/-- Use the matched prefix's endpoint as the base map of the swapped
pair, and compose the original suffix comparison with both transports. -/
theorem matched_full_history_after_swap
    {P₁ : BlowupTower A X} {P₂ : BlowupTower B Y}
    {φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {α : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hPrefix : IsTowerIso φ P₁ P₂ α)
    {Z₁ Z₂ Q₁ Q₂ F₁ F₂ G₁ G₂ : CMfd.{0} n}
    {L₁ : BlowupTower X Q₁} {L₂ : BlowupTower Y Q₂}
    {ψ : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z₂}
    {e₁ : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q₁}
    {e₂ : Z₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q₂}
    (hPair : IsTowerIso α L₁ L₂ ((e₁.symm.trans ψ).trans e₂))
    {S₁ : BlowupTower Z₁ F₁} {S₂ : BlowupTower Z₂ F₂}
    {T₁ : BlowupTower Q₁ G₁} {T₂ : BlowupTower Q₂ G₂}
    {ζ : F₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ F₂}
    {f₁ : F₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G₁}
    {f₂ : F₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G₂}
    (hS : IsTowerIso ψ S₁ S₂ ζ)
    (h₁ : IsTowerIso e₁ S₁ T₁ f₁) (h₂ : IsTowerIso e₂ S₂ T₂ f₂) :
    IsTowerIso φ ((P₁.append L₁).append T₁) ((P₂.append L₂).append T₂)
      ((f₁.symm.trans ζ).trans f₂) :=
  append_matched_carried_suffix (hPrefix.append hPair) hS h₁ h₂

/-- Putting the literal restriction of the appended tower back together
takes the same terminal points. The prefix remains strictly matched. -/
theorem matched_literal_restriction_after_swap
    (U : Opens B) (P : BlowupTower B X) (L : BlowupTower X Y) (T : BlowupTower Y Z)
    (P' : BlowupTower A X') (L' : BlowupTower X' Y') (T' : BlowupTower Y' Z')
    (φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
    (α : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage P U))
    (hPrefix : IsTowerIso φ P' (restrict U P) α)
    (β : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage L (openPreimage P U)))
    (hPair : IsTowerIso α L' (restrict (openPreimage P U) L) β)
    (γ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T (openPreimage L (openPreimage P U))))
    (hTail : IsTowerIso β T' (restrict (openPreimage L (openPreimage P U)) T) γ) :
    ∃ δ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (P.append (L.append T)) U),
      IsTowerIso φ (P'.append (L'.append T')) (restrict U (P.append (L.append T))) δ ∧
      ∀ z, (δ z).val = (γ z).val := by
  let hL := isTowerIso_restrict_append (openPreimage P U) L T
  let hP := isTowerIso_restrict_append U P (L.append T)
  have hLT := (hPair.append hTail).trans hL.symm
  have hα : α.trans (Diffeomorph.refl 𝓘(ℂ,ComplexModel n)
      (CMfd.of (n := n) (openPreimage P U)) ∞).symm = α := by ext x; rfl
  rw [hα] at hLT
  have hAll := (hPrefix.append hLT).trans hP.symm
  let eL := opensCongr (n := n) (openPreimage_append L T (openPreimage P U))
  let eP := opensCongr (n := n) (openPreimage_append P (L.append T) U)
  refine ⟨(γ.trans eL).trans eP,?_,fun _ => rfl⟩
  have hφ : φ.trans (Diffeomorph.refl 𝓘(ℂ,ComplexModel n)
      (CMfd.of (n := n) U) ∞).symm = φ := by ext x; rfl
  -- Normalize the base map at the intermediate append before composing.
  rw [hφ] at hAll
  apply BlowupTowerSplitIso.IsTowerIso.congr_last hAll
  intro z
  rfl

/-- Restricting a strict whole comparison to a given decomposition
retains the supplied terminal map on the exact two suffixes. -/
theorem split_strict_append
    {P₁ : BlowupTower A X} {P₂ : BlowupTower B Y}
    {φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {F₁ F₂ : CMfd.{0} n} (S₁ : BlowupTower X F₁) (S₂ : BlowupTower Y F₂)
    {ζ : F₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ F₂}
    (hLen : S₁.length = S₂.length)
    (h : IsTowerIso φ (P₁.append S₁) (P₂.append S₂) ζ) :
    ∃ α : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      IsTowerIso φ P₁ P₂ α ∧ IsTowerIso α S₁ S₂ ζ := by
  induction S₁ generalizing F₂ with
  | refl =>
    cases S₂ with
    | refl => exact ⟨ζ,h,.refl⟩
    | step => simp at hLen
  | @step F₁ G₁ S₁ C₁ π₁ hπ₁ ih =>
    cases S₂ with
    | refl => simp at hLen
    | @step F₂ G₂ S₂ C₂ π₂ hπ₂ =>
      cases h with
      | step hPrev _ _ _ hComm hCenter =>
        have hLen' : S₁.length = S₂.length := by
          simpa only [BlowupTower.length_step, Nat.add_right_cancel_iff] using hLen
        obtain ⟨α,hα,hTail⟩ := ih S₂ hLen' hPrev
        exact ⟨α,hα,.step hTail hπ₁ hπ₂ _ hComm hCenter⟩

/-- A strict whole original nested comparison determines the three
literal prefix, pair, and suffix comparisons at the matched cuts. -/
theorem split_strict_literal_restriction
    (U : Opens B) (P : BlowupTower B X) (L : BlowupTower X Y) (T : BlowupTower Y Z)
    (P' : BlowupTower A X') (L' : BlowupTower X' Y') (T' : BlowupTower Y' Z')
    (φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
    (ζ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage (P.append (L.append T)) U))
    (hL : L'.length = L.length) (hT : T'.length = T.length)
    (h : IsTowerIso φ (P'.append (L'.append T')) (restrict U (P.append (L.append T))) ζ) :
    ∃ (α : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage P U))
      (β : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage L (openPreimage P U)))
      (γ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T (openPreimage L (openPreimage P U)))),
      IsTowerIso φ P' (restrict U P) α ∧
      IsTowerIso α L' (restrict (openPreimage P U) L) β ∧
      IsTowerIso β T' (restrict (openPreimage L (openPreimage P U)) T) γ ∧
      ∀ z, (γ z).val = (ζ z).val := by
  have pFlat := isTowerIso_restrict_append U P (L.append T)
  have hp := h.trans pFlat
  have hφ : φ.trans (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞) = φ := by ext x; rfl
  rw [hφ] at hp
  have hLen : (L'.append T').length = (restrict (openPreimage P U) (L.append T)).length := by
    rw [length_restrict,BlowupTower.length_append,BlowupTower.length_append,hL,hT]
  obtain ⟨α,hPrefix,hRest⟩ := split_strict_append _ _ hLen hp
  have lFlat := isTowerIso_restrict_append (openPreimage P U) L T
  have hlt := hRest.trans lFlat
  have hα : α.trans (Diffeomorph.refl 𝓘(ℂ,ComplexModel n)
      (CMfd.of (n := n) (openPreimage P U)) ∞) = α := by ext x; rfl
  rw [hα] at hlt
  obtain ⟨β,hPair,hTail⟩ := split_strict_append _ _ (hT.trans (length_restrict _ T).symm) hlt
  exact ⟨α,β,_,hPrefix,hPair,hTail,fun _ => rfl⟩

/-- A matched nested swapped pair and the two real suffix transports
give the exact whole literal restriction with the original base map. -/
theorem matched_nested_swap_with_carried_suffix
    (U : Opens B) (P : BlowupTower B X) (L : BlowupTower X Y) (T : BlowupTower Y Z)
    (P' : BlowupTower A X') (L' : BlowupTower X' Y') (T' : BlowupTower Y' Z')
    (φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
    {α : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage P U)}
    (hPrefix : IsTowerIso φ P' (restrict U P) α)
    {V₁ V₂ F₁ F₂ : CMfd.{0} n}
    {ψ : V₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V₂}
    {e₁ : V₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y'}
    {e₂ : V₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage L (openPreimage P U))}
    (hPair : IsTowerIso α L' (restrict (openPreimage P U) L) ((e₁.symm.trans ψ).trans e₂))
    {S₁ : BlowupTower V₁ F₁} {S₂ : BlowupTower V₂ F₂}
    {ζ : F₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ F₂}
    {f₁ : F₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z'}
    {f₂ : F₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T (openPreimage L (openPreimage P U)))}
    (hS : IsTowerIso ψ S₁ S₂ ζ) (h₁ : IsTowerIso e₁ S₁ T' f₁)
    (h₂ : IsTowerIso e₂ S₂ (restrict (openPreimage L (openPreimage P U)) T) f₂) :
    ∃ δ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (P.append (L.append T)) U),
      IsTowerIso φ (P'.append (L'.append T')) (restrict U (P.append (L.append T))) δ ∧
      ∀ z, (δ z).val = (f₂ (ζ (f₁.symm z))).val :=
  matched_literal_restriction_after_swap U P L T P' L' T' φ α hPrefix _ hPair _
    ((h₁.symm.trans hS).trans h₂)

end Hironaka.HironakaG8MatchedSwapFullHistory

#print axioms Hironaka.HironakaG8MatchedSwapFullHistory.matched_full_history_after_swap
#print axioms Hironaka.HironakaG8MatchedSwapFullHistory.matched_literal_restriction_after_swap

#print axioms Hironaka.HironakaG8MatchedSwapFullHistory.split_strict_append

#print axioms Hironaka.HironakaG8MatchedSwapFullHistory.split_strict_literal_restriction

#print axioms Hironaka.HironakaG8MatchedSwapFullHistory.matched_nested_swap_with_carried_suffix
