import Hironaka.Invariant.MemberInterLocusAlong
/-! Original member loci commute with the unchanged inclusion of ANY
native topological subspace. All ordered members are retained. This is
not a complete IsSpecial or chronological invariant comparison. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology
namespace Hironaka.HironakaActualNativeSectionMemberLocus
noncomputable section
open MemberInterLocusAlong
variable {X : Type*} [TopologicalSpace X] {W : Set X}

theorem memberInterLocus_native_preimage (A S : Set W) (E : List (Set X)) :
    (Subtype.val : W→X) ⁻¹' memberInterLocus ((Subtype.val : W→X) '' A) E ((Subtype.val : W→X) '' S)=
      memberInterLocus A (E.map ((Subtype.val : W→X) ⁻¹' ·)) S := by
  ext p
  have hMem (q : W) : q.val∈(Subtype.val : W→X) '' S ↔ q∈S:=by
    constructor
    · rintro ⟨z,hz,he⟩
      exact (Subtype.val_injective he) ▸ hz
    · intro hq
      exact ⟨q,hq,rfl⟩
  have hThrough (q : W) : (∀H∈E,p.val∈H→q.val∈H) ↔
      ∀H∈E.map ((Subtype.val : W→X) ⁻¹' ·),p∈H→q∈H := by
    constructor
    · intro h H hH hpH
      obtain ⟨K,hK,rfl⟩:=List.mem_map.mp hH
      exact h K hK hpH
    · intro h H hH hpH
      exact h ((Subtype.val : W→X) ⁻¹' H) (List.mem_map_of_mem hH) hpH
  change p.val∈memberInterLocus ((Subtype.val : W→X) '' A) E ((Subtype.val : W→X) '' S) ↔ _
  rw [mem_memberInterLocus_iff,mem_memberInterLocus_iff]
  constructor
  · rintro ⟨hpS,h⟩
    refine ⟨(hMem p).mp hpS,?_⟩
    have hh:=continuous_subtype_val.continuousAt.eventually h
    filter_upwards [hh] with q hq hqA hqThrough
    exact (hMem q).mp (hq ⟨q,hqA,rfl⟩ ((hThrough q).mpr hqThrough))
  · rintro ⟨hpS,h⟩
    refine ⟨⟨p,hpS,rfl⟩,?_⟩
    have hnear : {q : W | q∈A →
        (∀H∈E.map ((Subtype.val : W→X) ⁻¹' ·),p∈H→q∈H) → q∈S}∈𝓝 p:=h
    obtain ⟨V,hV,hsub⟩:=(mem_nhds_subtype W p _).mp hnear
    filter_upwards [hV] with x hx hxA hxThrough
    obtain ⟨q,hqA,rfl⟩:=hxA
    exact ⟨q,hsub hx hqA ((hThrough q).mp hxThrough),rfl⟩

theorem memberInterLocus_native_image (A S : Set W) (E : List (Set X)) :
    (Subtype.val : W→X) '' memberInterLocus A (E.map ((Subtype.val : W→X) ⁻¹' ·)) S=
      memberInterLocus ((Subtype.val : W→X) '' A) E ((Subtype.val : W→X) '' S) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p,hp,rfl⟩
    have hh : p∈(Subtype.val : W→X) ⁻¹'
        memberInterLocus ((Subtype.val : W→X) '' A) E ((Subtype.val : W→X) '' S):=by
      rw [memberInterLocus_native_preimage]
      exact hp
    exact hh
  · intro x hx
    obtain ⟨p,_hpS,rfl⟩:=hx.1
    refine ⟨p,?_,rfl⟩
    have hh : p∈(Subtype.val : W→X) ⁻¹'
        memberInterLocus ((Subtype.val : W→X) '' A) E ((Subtype.val : W→X) '' S):=hx
    rwa [memberInterLocus_native_preimage] at hh

end
end Hironaka.HironakaActualNativeSectionMemberLocus
