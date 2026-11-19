import Hironaka.Resolution.HironakaG11TraceUniformTangency
import Hironaka.Resolution.HironakaG8BirthTraceContainment

set_option autoImplicit false

/-! Local birth-trace containment transfers between two contact carriers
once their tangent inclusions into the old member transfer on the centre. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11BirthTraceTransfer
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold BlowupSpaceTangent BlowupRestrictOpen
  HironakaG11TraceUniformTangency HironakaG8BirthTraceContainment

/-- The local birth trace of P contained in the old strict member transfers
to the birth trace of Q if tangent containment transfers near the centre. -/
theorem birth_trace_germ_transfer
    {n : ℕ} {X Y : CMfd.{0} n} {C P Q H : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hP : IsClosedSubmanifold n P)
    (hQ : IsClosedSubmanifold n Q) (hH : IsClosedSubmanifold n H)
    (hCP : C ⊆ P) (hCQ : C ⊆ Q)
    {p : Y} (hp : p ∈ geoStrictTransform π C P) (hpC : π p ∈ C)
    (hCH : ∀ᶠ x in 𝓝 (π p), x ∈ C → x ∈ H)
    (htrace : ∀ᶠ q in 𝓝 p, q ∈ geoStrictTransform π C P → π q ∈ C →
      q ∈ geoStrictTransform π C H)
    (htransfer : ∀ᶠ x in 𝓝 (π p), x ∈ C →
      (tangentSpace n P x ≤ tangentSpace n H x → tangentSpace n Q x ≤ tangentSpace n H x)) :
    ∀ᶠ q in 𝓝 p, q ∈ geoStrictTransform π C Q → π q ∈ C →
      q ∈ geoStrictTransform π C H := by
  have htan := actual_uniform_tangent_of_trace_containment hπ hP hCP hp hpC hCH htrace
  have hnear := (hCH.and htan).and htransfer
  obtain ⟨U,hUsub,hUopen,hpU⟩ := mem_nhds_iff.mp hnear
  let W : Opens X := ⟨U,hUopen⟩
  have hQW := isClosedSubmanifold_preimage_val hQ W
  have hHW := isClosedSubmanifold_preimage_val hH W
  have hCQW : ((Subtype.val : W → X) ⁻¹' C) ⊆ ((Subtype.val : W → X) ⁻¹' Q) :=
    fun _ hx => hCQ hx
  have hCHW : ((Subtype.val : W → X) ⁻¹' C) ⊆ ((Subtype.val : W → X) ⁻¹' H) :=
    fun x hx => (hUsub x.property).1.1 hx
  have htanW : ∀ x ∈ C, x ∈ W → tangentSpace n Q x ≤ tangentSpace n H x := by
    intro x hxC hxW
    have hx := hUsub hxW
    exact hx.2 hxC (hx.1.2 hxC)
  have hcontain := exceptional_trace_subset_of_tangent_on_open hπ W hQW hHW hCQW hCHW htanW
  filter_upwards [(hUopen.preimage hπ.contMDiff.continuous).mem_nhds hpU] with q hqW hqQ hqC
  exact hcontain q hqW hqC hqQ

end Hironaka.HironakaG11BirthTraceTransfer
