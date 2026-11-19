import Hironaka.Resolution.HironakaG3GlobalMemberTrace
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3GlobalMemberSafeTrace
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers HironakaG3REmbeddedGlobalSNC
  HironakaG3GlobalMemberTrace MaxLocusLocal

/-- The safe intersection with Q retains the same exhaustion window and list traces. -/
theorem safe_window_data {n : ℕ} {Z : CMfd.{0} n} (Q V : Opens Z)
    (Ex : SNCExhaustion (CMfd.of (n := n) Q)) (k : ℕ) (L : List (Set Z))
    (hW : Ex.W k = nestedOpens Q V)
    (hB : Ex.B k = L.map ((Subtype.val : Q → Z) ⁻¹' ·))
    (hSub : ∀ H ∈ L, H ⊆ V) :
    Ex.W k = nestedOpens Q (Q ⊓ V) ∧
    Ex.B k = (L.map (· ∩ (Q : Set Z))).map ((Subtype.val : Q → Z) ⁻¹' ·) ∧
    ∀ H ∈ L.map (· ∩ (Q : Set Z)), H ⊆ (Q ⊓ V : Opens Z) := by
  refine ⟨?_,?_,?_⟩
  · rw [hW]
    apply Opens.ext
    ext x
    simp [nestedOpens]
  · rw [hB,List.map_map]
    apply List.map_congr_left
    intro H _
    ext x
    simp
  · intro H hH
    obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hH
    intro x hx
    exact ⟨hx.2,hSub K hK hx.1⟩

/-- Every nonempty canonical trace on Q∩V is an actual list slot cut by Q. -/
theorem global_member_safe_trace_is_slot {n : ℕ} {Z : CMfd.{0} n} (Q V : Opens Z)
    (Ex : SNCExhaustion (CMfd.of (n := n) Q)) (k : ℕ) (L : List (Set Z))
    (hW : Ex.W k = nestedOpens Q V)
    (hB : Ex.B k = L.map ((Subtype.val : Q → Z) ⁻¹' ·))
    (hSub : ∀ H ∈ L, H ⊆ V) (b : {B : Set Q // Ex.IsGlobalMember B})
    (hNE : (((Subtype.val : Q → Z) '' b.val) ∩ (Q ⊓ V : Opens Z)).Nonempty) :
    ((Subtype.val : Q → Z) '' b.val) ∩ (Q ⊓ V : Opens Z) ∈ L.map (· ∩ (Q : Set Z)) := by
  obtain ⟨hW',hB',hSub'⟩ := safe_window_data Q V Ex k L hW hB hSub
  exact global_member_trace_is_slot Q (Q ⊓ V) inf_le_left Ex k _ hW' hB' hSub' b hNE

/-- Each nonempty actual slot trace on Q has a unique canonical global member. -/
theorem nonempty_safe_slot_exists_unique_global_member {n : ℕ} {Z : CMfd.{0} n} (Q V : Opens Z)
    (Ex : SNCExhaustion (CMfd.of (n := n) Q)) (k : ℕ) (L : List (Set Z))
    (hW : Ex.W k = nestedOpens Q V)
    (hB : Ex.B k = L.map ((Subtype.val : Q → Z) ⁻¹' ·))
    (hSub : ∀ H ∈ L, H ⊆ V) (H : Set Z) (hH : H ∈ L) (hNE : (H ∩ Q).Nonempty) :
    ∃! b : {B : Set Q // Ex.IsGlobalMember B},
      ((Subtype.val : Q → Z) '' b.val) ∩ (Q ⊓ V : Opens Z) = H ∩ Q := by
  obtain ⟨hW',hB',hSub'⟩ := safe_window_data Q V Ex k L hW hB hSub
  exact nonempty_slot_exists_unique_global_member Q (Q ⊓ V) inf_le_left Ex k _ hW' hB' hSub'
    (H ∩ Q) (List.mem_map.mpr ⟨H,hH,rfl⟩) hNE
end
end Hironaka.HironakaG3GlobalMemberSafeTrace
