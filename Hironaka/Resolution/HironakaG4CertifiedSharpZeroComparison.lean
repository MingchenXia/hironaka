import Hironaka.Resolution.HironakaG4CertifiedSharpHistory
import Hironaka.Resolution.HironakaG3EmptyAwareHistory

/-! A certified dimension-zero history is the actual empty history after every source change. -/

set_option autoImplicit false
open scoped Manifold ContDiff
universe u

namespace Hironaka.HironakaG4CertifiedSharpZeroComparison
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdealTowerTransport HironakaG4CertifiedSharpHistory HironakaG3EmptyAwareHistory

variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

/-- Every physical restriction or rebase of the dimension-zero witness
still has zero actual blowup positions. -/
theorem sharpHistoryZero_eq_refl {W : Set X} {E : List (Set X)} {T : BlowupTower X Y}
    (h : SharpHistoryZero n W E T) :
    ∃ e : Y = X, e ▸ T = (.refl : BlowupTower X X) := by
  induction h with
  | refl A W E => exact ⟨rfl,rfl⟩
  | restrictOpen O _ ih =>
      obtain ⟨rfl,rfl⟩ := ih
      exact ⟨rfl,rfl⟩
  | rebase φ _ ih =>
      obtain ⟨rfl,rfl⟩ := ih
      exact ⟨rfl,rfl⟩

/-- Two dimension-zero certified charts align physically over the exact
given biholomorphic base map. -/
theorem sharpHistory_zero_compare {hn : 0 < n} {W : Set X} {E : List (Set X)}
    {W' : Set X'} {E' : List (Set X')} {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (hT' : SharpHistory hn 0 W' E' T') (hT : SharpHistory hn 0 W E T) :
    ∃ χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      EmptyAwareTowerIso φ T' T χ := by
  obtain ⟨rfl,rfl⟩ := sharpHistoryZero_eq_refl (sharpHistory_zero hT')
  obtain ⟨rfl,rfl⟩ := sharpHistoryZero_eq_refl (sharpHistory_zero hT)
  exact ⟨φ,.refl⟩

end
end Hironaka.HironakaG4CertifiedSharpZeroComparison
