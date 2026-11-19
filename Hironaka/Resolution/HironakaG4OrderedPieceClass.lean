import Hironaka.Resolution.HironakaG4OrderedPieceRestriction
import Hironaka.Resolution.HironakaG3UniversePhysicalClassComparisons

/-! A fixed order turns the physical comparisons of the component classes
into whole-overlap comparisons of their merged class. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
universe u v

namespace Hironaka.HironakaG4OrderedPieceClass

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MaxLocusLocal
  HironakaG3RTowerClass G3UniversePhysicalClassComparisons HironakaOriginalTerminalOverlapComparison
  HironakaSharpActualCurveComparisonRestriction G3UniverseEmptyAwareOpenRestriction
  HironakaG4OrderedPieceMerge HironakaG4OrderedPieceRestriction

/-- One member carries the piece charts and the entire ordered physical merge
on the same source open. -/
def orderedPieceClass {n : ℕ} {X : CMfd.{u} n} {ι : Type v}
    (F : ι → Set X) (V : ι → Opens X) (C : ι → LocalTowerClass X) (order : List ι) :
    LocalTowerClass X :=
  fun U _Y T =>
    ∃ (Yi : ι → CMfd.{u} n) (S : ∀ i, BlowupTower (CMfd.of (n := n) U) (Yi i)),
      (∀ i, C i U (Yi i) (S i)) ∧
        OrderedPieceMerge (fun i => (Subtype.val : U → X) ⁻¹' F i) (fun i => nestedOpens U (V i))
          Yi S order.reverse T

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- Compatible charts for the individual pieces give comparisons of the
actual assembled towers on each whole overlap. -/
theorem orderedPieceClass_physical {n : ℕ} {X : CMfd.{u} n} {ι : Type v}
    (F : ι → Set X) (V : ι → Opens X) (hFV : ∀ i, F i ⊆ V i)
    (C : ι → LocalTowerClass X) (hCmp : ∀ i, HasPhysicalComparisons (C i)) (order : List ι) :
    HasPhysicalComparisons (orderedPieceClass F V C order) := by
  intro U₁ U₂ Z₁ Z₂ T₁ T₂ hT₁ hT₂
  obtain ⟨Y₁, S₁, hS₁, hM₁⟩ := hT₁
  obtain ⟨Y₂, S₂, hS₂, hM₂⟩ := hT₂
  let J := U₁ ⊓ U₂
  let D₁ := nestedOpens U₁ J
  let D₂ := nestedOpens U₂ J
  let e := overlapBaseEquiv (n := n) (show J ≤ U₁ from inf_le_left) (show J ≤ U₂ from inf_le_right)
  let F₁ : ι → Set D₁ := fun i => (fun z : D₁ => z.val.val) ⁻¹' F i
  let F₂ : ι → Set D₂ := fun i => (fun z : D₂ => z.val.val) ⁻¹' F i
  let V₁ : ι → Opens D₁ := fun i => nestedOpens D₁ (nestedOpens U₁ (V i))
  let V₂ : ι → Opens D₂ := fun i => nestedOpens D₂ (nestedOpens U₂ (V i))
  have hFV₂ (i : ι) : F₂ i ⊆ V₂ i := fun _ hz => hFV i hz
  have hPoint (z : D₁) : (e z).val.val = z.val.val := overlapBaseEquiv_point _ _ z
  have hF : F₁ = fun i => e ⁻¹' F₂ i := by
    funext i
    ext z
    change z.val.val ∈ F i ↔ (e z).val.val ∈ F i
    rw [hPoint]
  have hV : V₁ = fun i => preimageOpen e (V₂ i) := by
    funext i
    apply SetLike.coe_injective
    ext z
    change z.val.val ∈ V i ↔ (e z).val.val ∈ V i
    rw [hPoint]
  let S₁' := fun i => restrict D₁ (S₁ i)
  let S₂' := fun i => restrict D₂ (S₂ i)
  have hRM₁ : OrderedPieceMerge F₁ V₁ _ S₁' order.reverse (restrict D₁ T₁) :=
    orderedPieceMerge_restrict hM₁ D₁
  have hRM₂ : OrderedPieceMerge F₂ V₂ _ S₂' order.reverse (restrict D₂ T₂) :=
    orderedPieceMerge_restrict hM₂ D₂
  rw [hF, hV] at hRM₁
  apply orderedPieceMerge_emptyAware e F₂ V₂ hFV₂ ?_ hRM₁ hRM₂
  intro i
  obtain ⟨ψ, hψ⟩ := hCmp i U₁ U₂ (Y₁ i) (Y₂ i) (S₁ i) (S₂ i) (hS₁ i) (hS₂ i)
  exact ⟨_, emptyAware_open_restriction hψ (V₂ i)⟩

end
end Hironaka.HironakaG4OrderedPieceClass
