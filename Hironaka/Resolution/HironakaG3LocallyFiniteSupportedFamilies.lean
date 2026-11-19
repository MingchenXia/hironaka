import Hironaka.Resolution.HironakaG3ClosedSupportedWindowExtension
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Sets.Opens
import Mathlib.Data.Finset.Sigma
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology
namespace Hironaka.HironakaG3LocallyFiniteSupportedFamilies
noncomputable section

/-- A locally finite family on an open window, supported in a closed subset
inside that window, remains locally finite after inclusion in the ambient. -/
theorem locallyFinite_image_of_closed_support {Z : Type*} [TopologicalSpace Z] {κ : Type*}
    (Q : Opens Z) (F : Set Z) (hF : IsClosed F) (hFQ : F ⊆ Q)
    (B : κ → Set Q) (hB : LocallyFinite B)
    (hBF : ∀ j, B j ⊆ (Subtype.val : Q → Z) ⁻¹' F) :
    LocallyFinite (fun j => (Subtype.val : Q → Z) '' B j) := by
  intro x
  by_cases hxQ : x ∈ Q
  · let xQ : Q := ⟨x,hxQ⟩
    obtain ⟨V,hV,hfin⟩ := hB xQ
    obtain ⟨V',hV'V,hVopen,hxV⟩ := mem_nhds_iff.mp hV
    let N : Set Z := (Subtype.val : Q → Z) '' V'
    have hNopen : IsOpen N := Q.isOpen.isOpenMap_subtype_val V' hVopen
    have hxN : x ∈ N := ⟨xQ,hxV,rfl⟩
    refine ⟨N,hNopen.mem_nhds hxN,hfin.subset ?_⟩
    intro j hj
    obtain ⟨z,⟨y,hyB,rfl⟩,w,hwV,hwEq⟩ := hj
    have hyw : y = w := Subtype.ext hwEq.symm
    exact ⟨y,hyB,hV'V (hyw ▸ hwV)⟩
  · have hxF : x ∉ F := fun h => hxQ (hFQ h)
    refine ⟨Fᶜ,hF.isOpen_compl.mem_nhds hxF,?_⟩
    have he : {j | (((Subtype.val : Q → Z) '' B j) ∩ Fᶜ).Nonempty} = ∅ := by
      ext j
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
      rintro ⟨z,⟨y,hy,rfl⟩,hz⟩
      exact hz (hBF j hy)
    rw [he]
    exact Set.finite_empty

/-- Locally finite families over locally finite closed supports assemble as
one locally finite sigma-indexed family. -/
theorem locallyFinite_sigma_images_of_closed_support {Z : Type*} [TopologicalSpace Z]
    {ι : Type*} {κ : ι → Type*} (Q : ι → Opens Z) (F : ι → Set Z)
    (hF : ∀ i, IsClosed (F i)) (hLF : LocallyFinite F) (hFQ : ∀ i, F i ⊆ Q i)
    (B : ∀ i, κ i → Set (Q i)) (hB : ∀ i, LocallyFinite (B i))
    (hBF : ∀ i j, B i j ⊆ (Subtype.val : Q i → Z) ⁻¹' F i) :
    LocallyFinite (fun p : Σ i, κ i => (Subtype.val : Q p.1 → Z) '' B p.1 p.2) := by
  classical
  let H : ∀ i, κ i → Set Z := fun i j => (Subtype.val : Q i → Z) '' B i j
  have hLocal : ∀ i, LocallyFinite (H i) := fun i =>
    locallyFinite_image_of_closed_support (Q i) (F i) (hF i) (hFQ i) (B i) (hB i) (hBF i)
  intro x
  obtain ⟨N₀,hN₀,hfin₀⟩ := hLF x
  choose N hN hfin using fun i => hLocal i x
  let I : Set ι := {i | (F i ∩ N₀).Nonempty}
  have hI : I.Finite := hfin₀
  let N' : Set Z := N₀ ∩ ⋂ i ∈ I, N i
  have hN' : N' ∈ 𝓝 x := inter_mem hN₀ ((Filter.biInter_mem hI).mpr (fun i _ => hN i))
  let S : Finset (Σ i, κ i) := hI.toFinset.sigma (fun i => (hfin i).toFinset)
  refine ⟨N',hN',S.finite_toSet.subset ?_⟩
  rintro ⟨i,j⟩ ⟨z,hzH,hzN⟩
  have hi : i ∈ I := ⟨z,by
    obtain ⟨y,hy,rfl⟩ := hzH
    exact hBF i j hy, hzN.1⟩
  have hj : (H i j ∩ N i).Nonempty := ⟨z,hzH,mem_iInter₂.mp hzN.2 i hi⟩
  change ⟨i,j⟩ ∈ S
  exact Finset.mem_sigma.mpr ⟨hI.mem_toFinset.mpr hi,(hfin i).mem_toFinset.mpr hj⟩
end
end Hironaka.HironakaG3LocallyFiniteSupportedFamilies
