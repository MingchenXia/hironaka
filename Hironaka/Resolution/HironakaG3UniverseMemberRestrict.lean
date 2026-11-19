import Hironaka.Resolution.HironakaG3UniverseHomCoeff
import Hironaka.Invariant.InvDomainRebase
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3UniverseMemberRestrict
set_option linter.unusedSectionVars false
open Set Function Filter
open scoped Topology Manifold ContDiff
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal HomogenizedIdealAlong
  InvDomainMemberRestriction InvDomainRebase HironakaSmoothSubmersionCoefficientIdeals
noncomputable section
variable {n : ℕ} {M : Type u} {M' : Type v} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- A set whose preimage under a biholomorphism is the preimage of a member of `E₀` is that member. -/
theorem mem_of_preimage_mem_map_diffeo (χ : M' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M)
    {E₀ : List (Set M)} {H : Set M} (h : χ ⁻¹' H ∈ E₀.map (χ ⁻¹' ·)) : H ∈ E₀ := by
  obtain ⟨H₀, hH₀, hpre⟩ := List.mem_map.mp h
  have hH : H₀ = H := by
    ext x
    have := congrArg (fun s : Set M' => χ.symm x ∈ s) hpre
    simpa using this
  rw [← hH]
  exact hH₀

/-- **Step 1ab's restricted marked ideal commutes with biholomorphisms**: for `𝔪` well formed with `d ≥ 1`, a list `E₀` of
sets and a point `p`, the pullback along `χ` of the restricted marked ideal at `χ p` is the restricted marked ideal of `χ^*𝔪`
at `p`, with the preimages of the members of `E₀`. -/
theorem pullback_diffeo_memberRestrict_membersThrough (χ : M' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M)
    {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed) (hd : 1 ≤ 𝔪.d) (E₀ : List (Set M)) (p : M') :
    markedPullback (m := n) χ (memberRestrict 𝔪 (membersThrough 𝔪.E E₀ (χ p))) =
      memberRestrict (markedPullback (m := n) χ 𝔪)
        (membersThrough (markedPullback (m := n) χ 𝔪).E (E₀.map (χ ⁻¹' ·)) p) := by
  have _ := hd
  have hcoeff := G3UniverseBarMarked.coeffMarked_pullback_diffeo χ 𝔪 h𝔪.isCoherent h𝔪.isClosedSubmanifold_N
  have hI := congrArg MarkedIdeal.ideal hcoeff
  have hD := congrArg MarkedIdeal.d hcoeff
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ hI hD
  · show χ ⁻¹' (memberRestrict 𝔪 (membersThrough 𝔪.E E₀ (χ p))).N = _
    rw [memberRestrict_membersThrough_N, memberRestrict_membersThrough_N]
    ext q
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq]
    refine and_congr_right fun _ => ⟨fun hw H' hH' hH'₀ hpH' => ?_, fun hw H hH hH₀ hpH => ?_⟩
    · obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
      exact hw H hH (mem_of_preimage_mem_map_diffeo χ hH'₀) hpH'
    · exact hw _ (List.mem_map_of_mem hH) (List.mem_map_of_mem hH₀) hpH
  · show (memberRestrict 𝔪 (membersThrough 𝔪.E E₀ (χ p))).E.map (χ ⁻¹' ·) = _
    rw [memberRestrict_membersThrough_E, memberRestrict_membersThrough_E]
    exact (filter_map_members (f := (χ ⁻¹' ·)) (y := χ p) (y' := p) (fun H _ => Iff.rfl)
      fun H _ _ h => mem_of_preimage_mem_map_diffeo χ h).symm

end
end Hironaka.G3UniverseMemberRestrict

