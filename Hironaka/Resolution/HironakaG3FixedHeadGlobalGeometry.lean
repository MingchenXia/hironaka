import Hironaka.Resolution.HironakaG3GluedClassFootprint
import Hironaka.Resolution.HironakaG3FixedHeadTargetFootprint
import Hironaka.Resolution.HironakaG3FixedHeadNonerasure
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3FixedHeadGlobalGeometry
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings SubmanifoldChartedSpace
  HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3GluedClassFootprint
  HironakaG3FixedContactHeadClass HironakaG3FixedHeadTargetFootprint HironakaG3FixedHeadNonerasure

/-- Any map glued from the actual fixed-contact head class is an isomorphism
outside the original target. -/
theorem glued_fixed_head_isomorphism_off_target {d t : ℕ} {X Z : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (W : Set X) (hWa : IsComplexAnalyticSubset (n := d+t) W)
    (r : ℕ) {P : Z → X} (h : IsGluedFrom (fixedContactHead N hNc hN B W r) Z P) :
    IsIsomorphismOver (d+t) P Wᶜ := by
  apply glued_isomorphism_over_compl W hWa.isClosed ?_ h
  intro U Y A hHead
  exact fixed_head_centres_over_target N hNc hN B W hWa r U Y A hHead

/-- The same glued map does not erase the original target: its conventional
strict transform projects onto the whole of that target. -/
theorem glued_fixed_head_nonerasure {d t : ℕ} (hd : 0 < d) (ht : 0 < t)
    {X Z : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (hB : IsSNCDivisor (d+t) B) (hTrans : IsTransverse (d+t) N B)
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := d+t) W) (hWN : W ⊆ N)
    {r : ℕ} (hr : r < d) (hpure : W ⊆ closure (regularLocus (n := d+t) W r))
    (hAvoid : W ⊆ closure (W \ ⋃ H ∈ B, H))
    {P : Z → X} (h : IsGluedFrom (fixedContactHead N hNc hN B W r) Z P) :
    P '' strictTransform (d+t) P W = W := by
  apply Set.Subset.antisymm
  · rintro x ⟨z,hz,rfl⟩
    exact HironakaAdmissibleCalculus.strictTransform_subset_preimage h.1.continuous hWa.isClosed hz
  · intro x hx
    obtain ⟨c,hxU⟩ := h.2.2.2 x
    let xU : c.U := ⟨x,hxU⟩
    have hp : xU ∈ (Subtype.val : c.U → X) ⁻¹' W := hx
    have hProjection := fixed_head_nonerasure hd ht N hNc hN B hB hTrans W hWa hWN
      hr hpure hAvoid c.U c.Y c.T c.mem
    have hm : xU ∈ c.T.proj '' strictTransform (d+t) c.T.proj ((Subtype.val : c.U → X) ⁻¹' W) := by
      rw [hProjection]
      exact hp
    obtain ⟨y,hy,hyProj⟩ := hm
    refine ⟨chartIncl c y,?_,?_⟩
    · rw [strictTransform_chart c h.1 W] at hy
      exact hy
    · have hh := proj_chartIncl c y
      rw [hyProj] at hh
      exact hh
end
end Hironaka.HironakaG3FixedHeadGlobalGeometry
