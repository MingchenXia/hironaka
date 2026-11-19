import Hironaka.Resolution.HironakaG3IsomorphismOverComposition
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ComposedBoundarySupport
noncomputable section
open Hironaka.BlowupSequences BlowupTowers

/-- Extra intermediate support over a bad set disappears into the composite
exceptional locus when the composite is exceptional over that bad set. -/
theorem composed_boundary_exact_support {n : ℕ} {X Z Y : CMfd.{0} n}
    {P : Z → X} {Q : Y → Z}
    (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (hQ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ Q)
    (D Bad : Set X) (B₀ : Set Z)
    (hLower : P ⁻¹' D ∪ exceptionalLocus n P ⊆ B₀)
    (hUpper : B₀ ⊆ P ⁻¹' (D ∪ Bad))
    (hBadExc : (P ∘ Q) ⁻¹' Bad ⊆ exceptionalLocus n (P ∘ Q)) :
    Q ⁻¹' B₀ ∪ exceptionalLocus n Q =
      (P ∘ Q) ⁻¹' D ∪ exceptionalLocus n (P ∘ Q) := by
  have hExc : exceptionalLocus n (P ∘ Q) =
      exceptionalLocus n Q ∪ Q ⁻¹' exceptionalLocus n P :=
    exceptionalLocus_comp (hP.mdifferentiable (by simp)) (hQ.mdifferentiable (by simp))
  ext y
  constructor
  · intro hy
    rcases hy with hyB | hyQ
    · rcases hUpper hyB with hyD | hyBad
      · exact Or.inl hyD
      · exact Or.inr (hBadExc hyBad)
    · exact Or.inr (hExc.symm ▸ Or.inl hyQ)
  · intro hy
    rcases hy with hyD | hyExc
    · exact Or.inl (hLower (Or.inl hyD))
    · rw [hExc] at hyExc
      rcases hyExc with hyQ | hyP
      · exact Or.inr hyQ
      · exact Or.inl (hLower (Or.inr hyP))
end
end Hironaka.HironakaG3ComposedBoundarySupport
