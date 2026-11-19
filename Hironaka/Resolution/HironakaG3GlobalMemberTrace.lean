import Hironaka.Resolution.HironakaG3REmbeddedGlobalSNC
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3GlobalMemberTrace
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers HironakaG3REmbeddedGlobalSNC MaxLocusLocal

/-- Inclusion into the ambient commutes with taking a trace on a window. -/
theorem image_inter_window {Z : Type*} [TopologicalSpace Z] (Q V : Opens Z) (B : Set Q) :
    ((Subtype.val : Q → Z) '' B) ∩ V =
      (Subtype.val : Q → Z) '' (B ∩ (nestedOpens Q V : Set Q)) := by
  ext z
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hz⟩
    exact ⟨x,⟨hx,hz⟩,rfl⟩
  · rintro ⟨x,⟨hx,hxV⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,hxV⟩

/-- A nonempty trace of a canonical exhaustion member is an actual local slot. -/
theorem global_member_trace_is_slot {n : ℕ} {Z : CMfd.{0} n}
    (Q V : Opens Z) (hVQ : V ≤ Q) (Ex : SNCExhaustion (CMfd.of (n := n) Q))
    (k : ℕ) (L : List (Set Z)) (hW : Ex.W k = nestedOpens Q V)
    (hB : Ex.B k = L.map ((Subtype.val : Q → Z) ⁻¹' ·))
    (hSub : ∀ H ∈ L, H ⊆ V)
    (b : {B : Set Q // Ex.IsGlobalMember B})
    (hNE : (((Subtype.val : Q → Z) '' b.val) ∩ V).Nonempty) :
    ((Subtype.val : Q → Z) '' b.val) ∩ V ∈ L := by
  have hNE' : (b.val ∩ Ex.W k).Nonempty := by
    rw [hW]
    obtain ⟨z,hz⟩ := hNE
    rw [image_inter_window] at hz
    obtain ⟨x,hx,_⟩ := hz
    exact ⟨x,hx⟩
  have hmem := SNCExhaustion.IsGlobalMember.mem_of_nonempty Ex b.property k hNE'
  rw [hB] at hmem
  obtain ⟨H,hH,hEq⟩ := List.mem_map.mp hmem
  have hImg := image_inter_window Q V b.val
  have htrace : ((Subtype.val : Q → Z) '' b.val) ∩ V = H := by
    rw [hImg,← hW,← hEq,Set.image_preimage_eq_inter_range]
    rw [Subtype.range_coe_subtype]
    exact inter_eq_left.mpr (fun x hx => hVQ (hSub H hH hx))
  rw [htrace]
  exact hH

/-- Every nonempty local slot is the trace of one and only one canonical
exhaustion member; the labels are the actual global subsets of Q. -/
theorem nonempty_slot_exists_unique_global_member {n : ℕ} {Z : CMfd.{0} n}
    (Q V : Opens Z) (hVQ : V ≤ Q) (Ex : SNCExhaustion (CMfd.of (n := n) Q))
    (k : ℕ) (L : List (Set Z)) (hW : Ex.W k = nestedOpens Q V)
    (hB : Ex.B k = L.map ((Subtype.val : Q → Z) ⁻¹' ·))
    (hSub : ∀ H ∈ L, H ⊆ V)
    (H : Set Z) (hH : H ∈ L) (hNE : H.Nonempty) :
    ∃! b : {B : Set Q // Ex.IsGlobalMember B}, ((Subtype.val : Q → Z) '' b.val) ∩ V = H := by
  have hHQ : H ⊆ Q := fun x hx => hVQ (hSub H hH hx)
  have hHmem : (Subtype.val : Q → Z) ⁻¹' H ∈ Ex.B k := by
    rw [hB]
    exact List.mem_map.mpr ⟨H,hH,rfl⟩
  have hHne : ((Subtype.val : Q → Z) ⁻¹' H).Nonempty := by
    obtain ⟨x,hx⟩ := hNE
    exact ⟨⟨x,hHQ hx⟩,hx⟩
  obtain ⟨B,hGlobal,hTrace⟩ := Ex.exists_globalMember k hHmem hHne
  let b : {B : Set Q // Ex.IsGlobalMember B} := ⟨B,hGlobal⟩
  have hb : ((Subtype.val : Q → Z) '' b.val) ∩ V = H := by
    rw [image_inter_window,← hW,hTrace,Set.image_preimage_eq_inter_range,Subtype.range_coe_subtype]
    exact inter_eq_left.mpr hHQ
  refine ⟨b,hb,?_⟩
  intro b' hb'
  apply Subtype.ext
  apply Ex.globalMember_unique b'.property b.property k
  · have hEq : b'.val ∩ Ex.W k = (Subtype.val : Q → Z) ⁻¹' H := by
      have h := congrArg ((Subtype.val : Q → Z) ⁻¹' ·) hb'
      rw [Set.preimage_inter,Set.preimage_image_eq _ Subtype.val_injective] at h
      rw [hW]
      exact h
    rw [hEq]
    exact hHne
  · have hEq : b'.val ∩ Ex.W k = (Subtype.val : Q → Z) ⁻¹' H := by
      have h := congrArg ((Subtype.val : Q → Z) ⁻¹' ·) hb'
      rw [Set.preimage_inter,Set.preimage_image_eq _ Subtype.val_injective] at h
      rw [hW]
      exact h
    exact hEq.trans hTrace.symm
end
end Hironaka.HironakaG3GlobalMemberTrace
