import Hironaka.Resolution.HironakaG3BoundaryContainedAnalyticTrace
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ContactDimensionBound
noncomputable section
open Hironaka.BlowupSequences BlowupTowers SubmanifoldChartedSpace
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionRegularity
  HironakaG3BoundaryContainedAnalyticTrace

/-- A nonempty pure target contained in a closed smooth contact has dimension
at most the contact dimension. No nonempty regular point is supplied: purity
produces one on the actual native trace. -/
theorem target_dimension_le_contact {d t r : ℕ} {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (W : Set X) (hW : W.Nonempty) (hWN : W ⊆ N)
    (hpure : W ⊆ closure (regularLocus (n := d+t) W r)) : r ≤ d := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  let V : Set (nativeManifold (Nat.le_add_right d t) N hN) := (Subtype.val : N → X) ⁻¹' W
  have himage : (Subtype.val : N → X) '' V = W := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact hp
    · intro hx
      exact ⟨⟨x,hWN hx⟩,hx,rfl⟩
  have hVp : V ⊆ closure (regularLocus (n := d) V r) := by
    apply native_pure_of_ambient_image N hNc hN V r
    simpa only [himage] using hpure
  obtain ⟨x,hx⟩ := hW
  let p : N := ⟨x,hWN hx⟩
  have hp : p ∈ V := hx
  have hnonempty : (regularLocus (n := d) V r).Nonempty := by
    by_contra h
    have hp' := hVp hp
    rw [not_nonempty_iff_eq_empty.mp h, closure_empty] at hp'
    exact hp'
  obtain ⟨q,hq⟩ := hnonempty
  exact hq.1

/-- The branch choice depends only on the two fixed dimensions. -/
theorem target_contact_dimension_cases {d t r : ℕ} {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (W : Set X) (hW : W.Nonempty) (hWN : W ⊆ N)
    (hpure : W ⊆ closure (regularLocus (n := d+t) W r)) : r < d ∨ r = d := by
  exact lt_or_eq_of_le (target_dimension_le_contact N hNc hN W hW hWN hpure)
end
end Hironaka.HironakaG3ContactDimensionBound
