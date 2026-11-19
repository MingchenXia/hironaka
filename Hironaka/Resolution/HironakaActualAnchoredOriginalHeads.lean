import Hironaka.Resolution.HironakaActualAnchoredCurrentHistories
import Hironaka.Blowup.BlowupTowerSplit

/-! Every actual chronological cut retains the SAME original initial
anchor and internally produces an actual anchor for the literal real
tails, with the unchanged final current comparison. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualAnchoredOriginalHeads
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HironakaActualGeneratedCurrentHistories HironakaActualAnchoredCurrentHistories
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

theorem anchored_original_head_tails {V₀ : Opens X} {V₀' : Opens X'} {φ}
    {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
    (H : Anchored V₀ V₀' φ S T U U' η) (j : ℕ) :
    ∃(W : Opens (split S j).1)(W' : Opens (split T j).1)
      (χ : CMfd.of (n := n) W ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) W'),
      Anchored V₀ V₀' φ (head S j) (head T j) W W' χ ∧
      Anchored W W' χ (tail S j) (tail T j) U U' η := by
  induction H generalizing j with
  | initial =>
    cases j with
    | zero => exact ⟨V₀,V₀',φ,Anchored.initial,Anchored.initial⟩
    | succ j => exact ⟨V₀,V₀',φ,Anchored.initial,Anchored.initial⟩
  | @shrink Y Y' S T U U' η H V V' hV hV' htr ih =>
    obtain ⟨W,W',χ,hHead,hTail⟩:=ih j
    exact ⟨W,W',χ,hHead,Anchored.shrink hTail V V' hV hV' htr⟩
  | @step Y Y' Z Z' S T U U' η H C C' π π' hπ hπ' hC ih =>
    cases j with
    | zero =>
      exact ⟨_,_,_,Anchored.step H hπ hπ' hC,Anchored.initial⟩
    | succ j =>
      obtain ⟨W,W',χ,hHead,hTail⟩:=ih j
      exact ⟨W,W',χ,hHead,Anchored.step hTail hπ hπ' hC⟩

end
end Hironaka.HironakaActualAnchoredOriginalHeads
