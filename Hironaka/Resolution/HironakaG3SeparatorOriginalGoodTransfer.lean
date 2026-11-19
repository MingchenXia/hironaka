import Hironaka.Resolution.HironakaG3MixedBadSubsetSingular
import Hironaka.Resolution.HironakaStageCenters
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatorOriginalGoodTransfer
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaG3RTowerClass
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedMixedBad HironakaG3IndexedMixedGluing
  HironakaG3MixedBadSubsetSingular HironakaG3RegularUnionUniqueComponent HironakaStageCenters

theorem separator_preimage_original_good_subset_component_good {n d : ℕ} {X Z : CMfd.{0} n}
    {ι κ ρ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hLF : LocallyFinite (fun i => (V i).carrier))
    (hDim : ∀ i, (V i).dim < n)
    (hDistinct : ∀ i j, i ≠ j → ¬ (V i).carrier ⊆ (V j).carrier)
    (W : Set X) (hW : W = ⋃ i, (V i).carrier) (D : κ → Set X) (B : ρ → Set Z)
    {P : Z → X} (hG : IsGluedFrom (indexedMixedClass V D) Z P)
    (hB : (⋃ j, B j) ⊆ P ⁻¹' ((⋃ j, D j) ∪ indexedMixedBad V)) :
    P ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ j, D j)ᶜ ⊆
      (⋃ i, (strictTransform n P (V i).carrier \ regularLocus (n := n) (strictTransform n P (V i).carrier) (V i).dim) ∪
        (strictTransform n P (V i).carrier ∩ ⋃ j, B j))ᶜ := by
  intro z hz
  have hBad := indexed_mixed_bad_subset_singular V hLF hDistinct W hW (d := d)
  have hzNotBad : P z ∉ indexedMixedBad V := fun h => hz (Or.inl (hBad h))
  have hzNotExc : z ∉ exceptionalLocus n P :=
    fun h => hzNotBad (glued_indexed_exceptional_subset V hDim hDistinct D hG h)
  intro hzBad
  obtain ⟨i,hi⟩ := mem_iUnion.mp hzBad
  have hzCi : z ∈ strictTransform n P (V i).carrier := hi.elim (fun h => h.1) (fun h => h.1)
  have hxVi : P z ∈ (V i).carrier :=
    HironakaAdmissibleCalculus.strictTransform_subset_preimage hG.1.continuous (V i).isClosed_carrier hzCi
  have hxW : P z ∈ W := by rw [hW]; exact mem_iUnion.mpr ⟨i,hxVi⟩
  have hxReg : RegularAtDim (n := n) W (P z) d := by
    by_contra hn
    exact hz (Or.inl ⟨hxW,hn⟩)
  have hxNotD : P z ∉ ⋃ j, D j := fun h => hz (Or.inr ⟨hxW,h⟩)
  obtain ⟨j,hxVj,hReg,hUnique⟩ := regular_union_unique_component V hLF hDistinct W hW hxReg
  have hij : i = j := hUnique i hxVi
  subst i
  rcases hi with hSing | hBmem
  · have hReg' : RegularAtDim (n := n) (strictTransform n P (V j).carrier) z (V j).dim :=
      (regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus hG.1 (V j).isClosed_carrier hzNotExc _).mpr hReg
    exact hSing.2 hReg'
  · have h := hB hBmem.2
    rcases h with hD | hBad'
    · exact hxNotD hD
    · exact hzNotBad hBad'
end
end Hironaka.HironakaG3SeparatorOriginalGoodTransfer
