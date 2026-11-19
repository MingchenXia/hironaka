import Hironaka.Resolution.HironakaEmbeddedReducible
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3GoodSmoothBoundarySupport
noncomputable section
open Hironaka.BlowupSequences BlowupTowers

theorem good_smooth_boundary_support {n d : ℕ} {X Y : CMfd.{0} n} (W D : Set X)
    (hW : IsClosed W) {P : Y → X}
    (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (hGood : IsIsomorphismOver n P (W \ regularLocus (n := n) W d ∪ W ∩ D)ᶜ)
    (hRegular : ∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d) :
    P ⁻¹' D ∪ exceptionalLocus n P = P ⁻¹' (D ∪ W \ regularLocus (n := n) W d) := by
  have hSing : P ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n P :=
    HironakaEmbeddedReducible.preimage_diff_regularLocus_subset_exceptionalLocus hP hW hRegular
  have hExc : exceptionalLocus n P ⊆ P ⁻¹' (D ∪ W \ regularLocus (n := n) W d) := by
    intro z hz
    by_contra hnot
    have hD : P z ∉ D := fun h => hnot (Or.inl h)
    have hS : P z ∉ W \ regularLocus (n := n) W d := fun h => hnot (Or.inr h)
    have hG : z ∈ P ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ D)ᶜ := by
      change P z ∉ W \ regularLocus (n := n) W d ∪ W ∩ D
      intro h
      exact h.elim hS (fun h => hD h.2)
    exact Set.disjoint_left.mp hGood.2 hG hz
  ext z
  constructor
  · rintro (hz | hz)
    · exact Or.inl hz
    · exact hExc hz
  · rintro (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (hSing hz)
end
end Hironaka.HironakaG3GoodSmoothBoundarySupport
