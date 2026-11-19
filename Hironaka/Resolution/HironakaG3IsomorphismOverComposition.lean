import Hironaka.Blowup.BlowupTowers
import Hironaka.Resolution.HironakaStageCenters
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IsomorphismOverComposition
noncomputable section
open Hironaka.BlowupSequences BlowupTowers

theorem isomorphism_over_comp {n : ℕ} {X Y Z : CMfd.{0} n}
    {f : Y → X} {g : Z → Y} (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ g) (G : Set X)
    (hF : IsIsomorphismOver n f G) (hG : IsIsomorphismOver n g (f ⁻¹' G)) :
    IsIsomorphismOver n (f ∘ g) G := by
  constructor
  · simpa only [preimage_comp] using hF.1.comp hG.1
  · apply Set.disjoint_left.mpr
    intro z hz hExc
    rw [exceptionalLocus_comp (hf.mdifferentiable (by simp)) (hg.mdifferentiable (by simp))] at hExc
    rcases hExc with hExcG | hExcF
    · exact Set.disjoint_left.mp hG.2 hz hExcG
    · exact Set.disjoint_left.mp hF.2 hz hExcF
end
end Hironaka.HironakaG3IsomorphismOverComposition
