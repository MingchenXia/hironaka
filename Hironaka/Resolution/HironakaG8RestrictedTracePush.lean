import Hironaka.Resolution.HironakaG8RetainedSourcesOpen
import Hironaka.Invariant.StepOneUSC

/-! # Push the restricted suffix trace back to the original endpoint -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8RestrictedTracePush
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupRestrictOpen HomogenizedGlueingTower

/-- An all-member trace condition on a literal restricted test suffix holds
at the original endpoint after forgetting the open restriction. -/
theorem all_member_trace_of_restrict
    {n : ℕ} {Y Z : CMfd.{0} n} (U : Opens Y) (T : BlowupTower Y Z)
    {z : Z} (hzU : z ∈ openPreimage T U) (P D : Set Y) (S : List (Set Z)) :
    let W := openPreimage T U
    let z' : W := ⟨z,hzU⟩
    (∀ᶠ q in 𝓝 z', q ∈ strictAlong (restrict U T) ((Subtype.val : U → Y) ⁻¹' P) →
      q ∈ strictAlong (restrict U T) ((Subtype.val : U → Y) ⁻¹' D) →
      ∀ K ∈ S.map ((Subtype.val : W → Z) ⁻¹' ·), q ∈ K) →
    (∀ᶠ w in 𝓝 z, w ∈ strictAlong T P → w ∈ strictAlong T D → ∀ K ∈ S, w ∈ K) := by
  let W := openPreimage T U
  let z' : W := ⟨z,hzU⟩
  change (∀ᶠ q in 𝓝 z', q ∈ strictAlong (restrict U T) ((Subtype.val : U → Y) ⁻¹' P) →
      q ∈ strictAlong (restrict U T) ((Subtype.val : U → Y) ⁻¹' D) →
      ∀ K ∈ S.map ((Subtype.val : W → Z) ⁻¹' ·), q ∈ K) →
    (∀ᶠ w in 𝓝 z, w ∈ strictAlong T P → w ∈ strictAlong T D → ∀ K ∈ S, w ∈ K)
  intro h
  have h' : ∀ᶠ q in 𝓝 z', q.val ∈ strictAlong T P → q.val ∈ strictAlong T D →
      ∀ K ∈ S, q.val ∈ K := by
    filter_upwards [h] with q hq hP hD K hK
    have hP' : q ∈ strictAlong (restrict U T) ((Subtype.val : U → Y) ⁻¹' P) := by
      rw [strictAlong_restrict U T P]
      exact hP
    have hD' : q ∈ strictAlong (restrict U T) ((Subtype.val : U → Y) ⁻¹' D) := by
      rw [strictAlong_restrict U T D]
      exact hD
    exact hq hP' hD' ((Subtype.val : W → Z) ⁻¹' K) (List.mem_map.mpr ⟨K,hK,rfl⟩)
  have hpush := StepOneUSC.eventually_forall_mem_of_eventually W hzU h'
  filter_upwards [hpush,W.isOpen.mem_nhds hzU] with w hw hwW
  exact hw hwW

end
end Hironaka.HironakaG8RestrictedTracePush
