import Hironaka.Resolution.HironakaG3GlobalMemberSafeTrace
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3BornLabelsDistinct
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3REmbeddedGlobalSNC MaxLocusLocal

/-- Equal nonempty ambient traces of canonical members supported over disjoint
component sets have the same component and the same canonical member. -/
theorem born_trace_labels_eq {n : ℕ} {X Z : CMfd.{0} n} {ι : Type*}
    (P : Z → X) (C : ι → Set X) (Q : ι → Opens Z)
    (Ex : ∀ i, SNCExhaustion (CMfd.of (n := n) (Q i)))
    (hDisj : Pairwise (Disjoint on C))
    (hSupport : ∀ i (b : {B : Set (Q i) // (Ex i).IsGlobalMember B}),
      ((Subtype.val : Q i → Z) '' b.val) ⊆ P ⁻¹' C i)
    (V : Opens Z) (i j : ι) (k : ℕ) (hW : (Ex i).W k = nestedOpens (Q i) V)
    (b : {B : Set (Q i) // (Ex i).IsGlobalMember B})
    (b' : {B : Set (Q j) // (Ex j).IsGlobalMember B})
    (hNE : (((Subtype.val : Q i → Z) '' b.val) ∩ V).Nonempty)
    (hEq : ((Subtype.val : Q i → Z) '' b.val) ∩ V =
      ((Subtype.val : Q j → Z) '' b'.val) ∩ V) :
    ∃ h : i = j, h ▸ b = b' := by
  have hij : i = j := by
    by_contra h
    obtain ⟨z,hz,hzV⟩ := hNE
    have hz' : z ∈ ((Subtype.val : Q j → Z) '' b'.val) := ((Set.ext_iff.mp hEq z).mp ⟨hz,hzV⟩).1
    exact Set.disjoint_left.mp (hDisj h) (hSupport i b hz) (hSupport j b' hz')
  subst j
  refine ⟨rfl,?_⟩
  apply Subtype.ext
  apply (Ex i).globalMember_unique b.property b'.property k
  · obtain ⟨z,hz,hzV⟩ := hNE
    obtain ⟨x,hx,rfl⟩ := hz
    exact ⟨x,hx,by rw [hW]; exact hzV⟩
  · have h := congrArg ((Subtype.val : Q i → Z) ⁻¹' ·) hEq
    simp only [Set.preimage_inter,Set.preimage_image_eq _ Subtype.val_injective] at h
    rw [hW]
    exact h
end
end Hironaka.HironakaG3BornLabelsDistinct
