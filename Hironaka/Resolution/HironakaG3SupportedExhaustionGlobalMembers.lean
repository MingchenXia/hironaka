import Hironaka.Resolution.HironakaG3REmbeddedGlobalSNC
import Hironaka.Resolution.HironakaG3LocallyFiniteSupportedFamilies
import Hironaka.Resolution.HironakaG3ClosedSupportedWindowExtension
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SupportedExhaustionGlobalMembers
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers HironakaG3REmbeddedGlobalSNC
  HironakaG3LocallyFiniteSupportedFamilies HironakaG3ClosedSupportedWindowExtension

/-- Canonical members of local SNC exhaustions extend as a locally finite
sigma-family of closed nonempty sets when their slots have closed LF support
inside the respective windows. -/
theorem supported_exhaustion_global_members {n : ℕ} {Z : CMfd.{0} n} {ι : Type*}
    (Q : ι → Opens Z) (F : ι → Set Z) (hF : ∀ i, IsClosed (F i))
    (hFLF : LocallyFinite F) (hFQ : ∀ i, F i ⊆ Q i)
    (Ex : ∀ i, SNCExhaustion (CMfd.of (n := n) (Q i)))
    (hSlots : ∀ i k H, H ∈ (Ex i).B k → H ⊆ (Subtype.val : Q i → Z) ⁻¹' F i) :
    let B : (Σ i, {H : Set (Q i) // (Ex i).IsGlobalMember H}) → Set Z :=
      fun p => (Subtype.val : Q p.1 → Z) '' p.2.1
    LocallyFinite B ∧ ∀ p, IsClosed (B p) ∧ (B p).Nonempty ∧ B p ⊆ F p.1 := by
  let L : ∀ i, {H : Set (Q i) // (Ex i).IsGlobalMember H} → Set (Q i) := fun _ b => b.1
  have hL : ∀ i, LocallyFinite (L i) := fun i => (Ex i).locallyFinite_globalMember
  have hLF : ∀ i b, L i b ⊆ (Subtype.val : Q i → Z) ⁻¹' F i := by
    intro i b x hx
    have hxU : x ∈ ⋃ b : {H : Set (Q i) // (Ex i).IsGlobalMember H}, (b : Set (Q i)) := mem_iUnion.mpr ⟨b,hx⟩
    rw [(Ex i).iUnion_globalMember] at hxU
    obtain ⟨k,hxk⟩ := mem_iUnion.mp hxU
    obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hxk
    exact hSlots i k H hH hxH
  have hB := locallyFinite_sigma_images_of_closed_support Q F hF hFLF hFQ L hL hLF
  refine ⟨hB,?_⟩
  intro p
  refine ⟨isClosed_image_of_closed_support (Q p.1) (F p.1) (hF p.1) (hFQ p.1) p.2.1
    ((Ex p.1).isClosed_globalMember p.2.2) (hLF p.1 p.2),p.2.2.1.image _,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  exact hLF p.1 p.2 hx
end
end Hironaka.HironakaG3SupportedExhaustionGlobalMembers
