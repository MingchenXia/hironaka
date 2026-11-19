import Hironaka.Resolution.HironakaG11UnrestrictedDenseEscape

set_option autoImplicit false

/-! Local density escapes through a literal, unrestricted blowup suffix. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11LocalTraceTransport
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HomogenizedGlueingTower HironakaG11UnrestrictedDenseEscape

/-- If an initial trace is locally dense away from a closed obstacle, its
literal strict transform has the same property at all points over that open,
without any avoidance assumption on the intervening centres. -/
theorem strictAlong_dense_off_over_open
    {n : ℕ} {X Y : CMfd.{0} n} (A H : Set X) (hH : IsClosed H)
    (U : Opens X)
    (hDense : ((Subtype.val : U → X) ⁻¹' A) ⊆
      closure (((Subtype.val : U → X) ⁻¹' A) \ ((Subtype.val : U → X) ⁻¹' H)))
    (T : BlowupTower X Y) {y : Y} (hyU : T.proj y ∈ U) (hyA : y ∈ strictAlong T A) :
    y ∈ closure (strictAlong T A \ strictAlong T H) := by
  let y' : openPreimage T U := ⟨y,hyU⟩
  have hdense := strictAlong_dense_off ((Subtype.val : U → X) ⁻¹' A)
    ((Subtype.val : U → X) ⁻¹' H) (hH.preimage continuous_subtype_val) hDense (restrict U T)
  rw [strictAlong_restrict U T A,strictAlong_restrict U T H] at hdense
  have hy' : y' ∈ (Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T A := hyA
  have hcl := hdense hy'
  rw [mem_closure_iff_nhds] at hcl ⊢
  intro V hV
  have hV' : (Subtype.val : openPreimage T U → Y) ⁻¹' V ∈ 𝓝 y' :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hV
  obtain ⟨q,hqV,hqA,hqH⟩ := hcl _ hV'
  exact ⟨q.val,hqV,hqA,hqH⟩

end Hironaka.HironakaG11LocalTraceTransport
