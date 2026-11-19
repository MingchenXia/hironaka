import Hironaka.Resolution.HironakaOriginalFullValueVariationLocus
import Hironaka.Resolution.HironakaAdmissibleCalculus

set_option autoImplicit false

/-!
# Literal variation under auxiliary strict transforms

Actual relative neighborhoods transport local constancy away from the
exceptional locus. The resulting inclusion controls the literal original
variation locus by its actual singular set and the image of actual source
variation. No equations for bad sets or transformed numerical values are
assumed. Blueprint: `hironaka-auxiliary-variation-descent.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaAuxiliaryVariationDescent

open Hironaka.BlowupSequences
  HironakaOriginalFullValueVariationLocus HironakaAdmissibleCalculus
  StrictTransformComposition AnalyticSubsetOpens

section Topology

variable {M : Type*} [TopologicalSpace M] {A : Type v}

/-- Ordinary open-neighborhood constancy is exactly eventual relative constancy. -/
theorem exists_open_const_iff_eventually (g : M → A) (W : Set M) (x : M) :
    (∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ W ∩ U, g y = g x) ↔
      ∀ᶠ y in 𝓝[W] x, g y = g x := by
  change _ ↔ {y | g y = g x} ∈ 𝓝[W] x
  rw [mem_nhdsWithin]
  constructor
  · rintro ⟨U,hU,hxU,hg⟩
    exact ⟨U,hU,hxU,fun y hy => hg y ⟨hy.2,hy.1⟩⟩
  · rintro ⟨U,hU,hxU,hg⟩
    exact ⟨U,hU,hxU,fun y hy => hg ⟨hy.2,hy.1⟩⟩

end Topology

noncomputable section

variable {n : ℕ} {Y Z : Type u}
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {A : Type v}

/-- Off the actual exceptional locus, the actual strict transform has exactly
the original carrier's relative neighborhoods under the projection. -/
theorem map_nhdsWithin_strictTransform {π : Z → Y}
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π)
    {W : Set Y} (hW : IsClosed W) {z : Z} (hz : z ∉ exceptionalLocus n π) :
    Filter.map π (𝓝[strictTransform n π W] z) = 𝓝[W] (π z) := by
  have hO := isOpen_compl_exceptionalLocus hπ
  have he : strictTransform n π W ∩ (exceptionalLocus n π)ᶜ =
      (π ⁻¹' W) ∩ (exceptionalLocus n π)ᶜ := by
    ext u
    exact and_congr_left fun hu => mem_strictTransform_iff_of_notMem hπ.continuous hW hu
  have hn : 𝓝[strictTransform n π W] z = 𝓝[π ⁻¹' W] z :=
    nhdsWithin_eq_nhdsWithin hz hO he
  rw [hn]
  change Filter.map π (𝓝 z ⊓ 𝓟 (π ⁻¹' W)) = _
  rw [Filter.map_inf_principal_preimage, map_nhds_eq_of_not_mem_exceptionalLocus hπ hz]
  rfl

/-- Local constancy of the original values descends and pulls back at every
actual nonexceptional point; no numerical transformation law is involved. -/
theorem localConstancy_strictTransform_iff {π : Z → Y}
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π)
    {W : Set Y} (hW : IsClosed W) {z : Z} (hz : z ∉ exceptionalLocus n π)
    (g : Y → A) :
    (∃ U : Set Z, IsOpen U ∧ z ∈ U ∧
      ∀ u ∈ strictTransform n π W ∩ U, (g ∘ π) u = (g ∘ π) z) ↔
    (∃ U : Set Y, IsOpen U ∧ π z ∈ U ∧ ∀ y ∈ W ∩ U, g y = g (π z)) := by
  rw [exists_open_const_iff_eventually, exists_open_const_iff_eventually,
    ← map_nhdsWithin_strictTransform hπ hW hz]
  rfl

/-- The literal original bad set is contained in the actual singular set
and actual image of the source bad set. Source regularity is not assumed. -/
theorem actualValueVariationLocus_subset_singular_union_image {π : Z → Y}
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π)
    {W : Set Y} (hW : IsClosed W) (q : ℕ)
    (hiso : IsIsomorphismOver n π (W \ regularLocus (n := n) W q)ᶜ)
    (g : Y → A) :
    actualValueVariationLocus (n := n) g W q ⊆
      (W \ regularLocus (n := n) W q) ∪
        π '' actualValueVariationLocus (n := n) (g ∘ π) (strictTransform n π W) q := by
  intro x hx
  by_cases hxF : x ∈ W \ regularLocus (n := n) W q
  · exact Or.inl hxF
  · have hxreg : RegularAtDim (n := n) W x q := by
      by_contra hh
      exact hxF ⟨hx.1,hh⟩
    obtain ⟨z,hzF,hzx⟩ := hiso.1.surjOn hxF
    have hzE : z ∉ exceptionalLocus n π := fun hz => Set.disjoint_left.mp hiso.2 hzF hz
    have hzS : z ∈ strictTransform n π W :=
      (mem_strictTransform_iff_of_notMem hπ.continuous hW hzE).mpr (hzx.symm ▸ hx.1)
    refine Or.inr ⟨z,⟨hzS,?_⟩,hzx⟩
    rintro ⟨_hzreg,hzconst⟩
    have hc := (localConstancy_strictTransform_iff hπ hW hzE g).mp hzconst
    rw [hzx] at hc
    exact hx.2 ⟨hxreg,hc⟩

/-- A genuinely resolved carrier also supplies the reverse inclusion, so
the actual bad loci satisfy the exact original singular-plus-image identity. -/
theorem actualValueVariationLocus_strictTransform_eq {π : Z → Y}
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π)
    {W : Set Y} (hW : IsClosed W) (q : ℕ)
    (hreg : ∀ z ∈ strictTransform n π W, RegularAtDim (n := n) (strictTransform n π W) z q)
    (hiso : IsIsomorphismOver n π (W \ regularLocus (n := n) W q)ᶜ)
    (g : Y → A) :
    actualValueVariationLocus (n := n) g W q =
      (W \ regularLocus (n := n) W q) ∪
        π '' actualValueVariationLocus (n := n) (g ∘ π) (strictTransform n π W) q := by
  apply Subset.antisymm (actualValueVariationLocus_subset_singular_union_image hπ hW q hiso g)
  rintro x (hxF | ⟨z,hzB,rfl⟩)
  · exact ⟨hxF.1,fun h => hxF.2 h.1⟩
  · have hzW : π z ∈ W := strictTransform_subset_preimage hπ.continuous hW hzB.1
    refine ⟨hzW,?_⟩
    rintro ⟨_hxreg,U,hU,hzU,hval⟩
    apply hzB.2
    refine ⟨hreg z hzB.1,π ⁻¹' U,hU.preimage hπ.continuous,hzU,?_⟩
    rintro u ⟨huS,huU⟩
    exact hval (π u) ⟨strictTransform_subset_preimage hπ.continuous hW huS,huU⟩

/-- The independently defined literal bad locus commutes with restriction
of the ambient manifold to any actual open subset. -/
theorem actualValueVariationLocus_preimage_val (U : TopologicalSpace.Opens Y)
    (g : Y → A) (W : Set Y) (q : ℕ) :
    (Subtype.val : U → Y) ⁻¹' actualValueVariationLocus (n := n) g W q =
      actualValueVariationLocus (n := n) (g ∘ (Subtype.val : U → Y))
        ((Subtype.val : U → Y) ⁻¹' W) q := by
  ext x
  change (x.val ∈ W ∧ ¬_) ↔ (x.val ∈ W ∧ ¬_)
  apply and_congr_right
  intro _hxW
  apply not_congr
  apply and_congr regularAtDim_preimage_val_iff.symm
  constructor
  · rintro ⟨V,hV,hxV,hval⟩
    exact ⟨Subtype.val ⁻¹' V,hV.preimage continuous_subtype_val,hxV,
      fun y hy => hval y.val ⟨hy.1,hy.2⟩⟩
  · rintro ⟨V,hV,hxV,hval⟩
    refine ⟨Subtype.val '' V,U.isOpen.isOpenMap_subtype_val V hV,⟨x,hxV,rfl⟩,?_⟩
    rintro y ⟨hyW,z,hzV,hzy⟩
    rw [← hzy]
    have hzW : (z : Y) ∈ W := hzy.symm ▸ hyW
    exact hval z ⟨hzW,hzV⟩

end

end Hironaka.HironakaAuxiliaryVariationDescent
