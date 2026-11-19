import Hironaka.Resolution.HironakaG3ResidualWindowTraces
import Hironaka.Resolution.HironakaG3StoppedDifferentBoundaries
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ResidualOverlapBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  HironakaOriginalTerminalOverlapComparison HironakaG3ResidualWindowTraces HironakaG3RTowerClass MaxLocusLocal
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)

/-- Two visible residual windows give identical ordered nonempty marked
boundary traces under the canonical overlap equivalence. -/
theorem residual_overlap_marked_boundary {n : ℕ} {X : CMfd.{0} n}
    {ι : Type*} [LinearOrder ι] (D : ι → Set X) (S R₁ R₂ : Finset ι)
    (hD₁ : Disjoint S R₁) (hD₂ : Disjoint S R₂) (U₁ U₂ : Opens X)
    (hVis₁ : ∀ i, i ∉ S → (D i ∩ (U₁ : Set X)).Nonempty → i ∈ R₁)
    (hVis₂ : ∀ i, i ∉ S → (D i ∩ (U₂ : Set X)).Nonempty → i ∈ R₂)
    (J : GermIdeal n X) :
    let M₁ : MarkedIdeal n X := ⟨univ,(R₁.sort (· ≤ ·)).map D,J,1⟩
    let M₂ : MarkedIdeal n X := ⟨univ,(R₂.sort (· ≤ ·)).map D,J,1⟩
    let Φ := overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right
    ((pullback (Subtype.val : nestedOpens U₁ (U₁ ⊓ U₂) → U₁)
      (pullback (Subtype.val : U₁ → X) M₁)).E).filter (fun H => decide H.Nonempty) =
    (((pullback (Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂)
      (pullback (Subtype.val : U₂ → X) M₂)).E).map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty) := by
  let W₁ := nestedOpens U₁ (U₁ ⊓ U₂)
  let Φ := overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right
  let F (i : ι) : Set W₁ := (fun q : W₁ => ((q.val : U₁) : X)) ⁻¹' D i
  have hs₁ : ∀ i, i ∉ S → (F i).Nonempty → i ∈ R₁ := by
    intro i hi ⟨q,hq⟩
    exact hVis₁ i hi ⟨_,hq,q.val.property⟩
  have hs₂ : ∀ i, i ∉ S → (F i).Nonempty → i ∈ R₂ := by
    intro i hi ⟨q,hq⟩
    exact hVis₂ i hi ⟨_,hq,q.property.2⟩
  have h := residual_window_traces_agree F S R₁ R₂ hD₁ hD₂ hs₁ hs₂
  have heq₁ (i : ι) : (Subtype.val : W₁ → U₁) ⁻¹' ((Subtype.val : U₁ → X) ⁻¹' D i) = F i := rfl
  have heq₂ (i : ι) : Φ ⁻¹' ((Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) ⁻¹'
      ((Subtype.val : U₂ → X) ⁻¹' D i)) = F i := by
    ext q
    rfl
  have hm₁ : (R₁.sort (· ≤ ·)).map (fun i => (Subtype.val : W₁ → U₁) ⁻¹'
      ((Subtype.val : U₁ → X) ⁻¹' D i)) = (R₁.sort (· ≤ ·)).map F := by
    apply List.map_congr_left
    intro i hi
    exact heq₁ i
  have hm₂ : (R₂.sort (· ≤ ·)).map (fun i => Φ ⁻¹'
      ((Subtype.val : nestedOpens U₂ (U₁ ⊓ U₂) → U₂) ⁻¹'
        ((Subtype.val : U₂ → X) ⁻¹' D i))) = (R₂.sort (· ≤ ·)).map F := by
    apply List.map_congr_left
    intro i hi
    exact heq₂ i
  simp only [pullback,List.map_map,Function.comp_def]
  rw [hm₁,hm₂]
  exact h
end
end Hironaka.HironakaG3ResidualOverlapBoundary
