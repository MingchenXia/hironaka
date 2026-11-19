import Hironaka.Resolution.HironakaG3RestrictPartialSNCChain
import Hironaka.Resolution.HironakaActualLocallyFiniteBoundary
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SupportedPartialSNCChain
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3REmbeddedGlobalSNC
  HironakaG3RestrictPartialSNCChain MaxLocusLocal

/-- A compatible nested SNC chain supported over a set gives its actual canonical
local global-member family, still supported over that set. -/
theorem supported_partial_snc_chain {n : ℕ} {Z : CMfd.{0} n} (Q : Opens Z)
    (V : ℕ → Opens Z) (L : ℕ → List (Set Z)) (F : Set Z)
    (hVQ : ∀ k, V k ≤ Q)
    (hMono : ∀ {j k : ℕ}, j ≤ k → (V j : Set Z) ⊆ V k)
    (hCover : (⋃ k, (V k : Set Z)) = (Q : Set Z))
    (hSub : ∀ {k : ℕ} {H : Set Z}, H ∈ L k → H ⊆ V k)
    (hSNC : ∀ k, IsSNCDivisor n ((L k).map ((Subtype.val : V k → Z) ⁻¹' ·)))
    (hNested : ∀ {j k : ℕ}, j ≤ k →
      ((L k).map (· ∩ (V j : Set Z))).filter (fun H => decide H.Nonempty) =
        (L j).filter (fun H => decide H.Nonempty))
    (hFoot : ∀ {k : ℕ} {H : Set Z}, H ∈ L k → H ⊆ F) :
    ∃ (Ex : SNCExhaustion (CMfd.of (n := n) Q)),
      (∀ k, Ex.W k = nestedOpens Q (V k)) ∧
      (∀ k, Ex.B k = (L k).map ((Subtype.val : Q → Z) ⁻¹' ·)) ∧
      ∃ (ρ : Type) (B : ρ → Set Q), IsLocallyFiniteSNCDivisor n (Q := CMfd.of (n := n) Q) B ∧
        (∀ j, (B j).Nonempty ∧ B j ⊆ (Subtype.val : Q → Z) ⁻¹' F) ∧
        (⋃ j, B j) = ⋃ k, ⋃ H ∈ Ex.B k, H := by
  obtain ⟨Ex,hExW,hExB⟩ := restrict_partial_snc_chain Q V L hVQ (fun {j k} => hMono) hCover hSub hSNC hNested
  refine ⟨Ex,hExW,hExB,{B : Set Q // Ex.IsGlobalMember B},fun j => j.1,
    ⟨Ex.locallyFinite_globalMember,fun j => Ex.isClosed_globalMember j.2,Ex.coordinates_globalMember⟩,?_,Ex.iUnion_globalMember⟩
  intro j
  refine ⟨j.2.1,?_⟩
  intro x hx
  have hxU : x ∈ ⋃ j : {B : Set Q // Ex.IsGlobalMember B}, (j : Set Q) := mem_iUnion.mpr ⟨j,hx⟩
  rw [Ex.iUnion_globalMember] at hxU
  obtain ⟨k,hxk⟩ := mem_iUnion.mp hxU
  rw [hExB] at hxk
  obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hxk
  obtain ⟨H',hH',rfl⟩ := List.mem_map.mp hH
  exact hFoot hH' hxH
end
end Hironaka.HironakaG3SupportedPartialSNCChain
