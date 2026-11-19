import Hironaka.Analytic.Unibranch.ComplexSpaceThetaPSHPullbackFinite
import Hironaka.Analytic.FibreDimensionLowerBound

/-! Actual analytic preimages, singletons and fibers in the original
singular category. Blueprint: complex-space-analytic-fibers.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open Hironaka
namespace Hironaka.Analytic.Unibranch.SourceReducedComplexSpace

/-- Actual original analytic subsets pull back under the actual original
morphism, including singular source and target. -/
theorem IsAnalyticSubset.preimage {X Y : SourceReducedComplexSpace}
    {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z) (f : Y ⟶ X) :
    Y.IsAnalyticSubset (f.hom.left.base ⁻¹' Z) := by
  intro y
  obtain ⟨e,he,B,hB,hrep⟩ := hZ (f.hom.left.base y)
  obtain ⟨A,hA⟩ := SpaceForm.morphismChartLift_cover f e y he
  let g : A.source.ambient → e.ambient := fun z => ⟨A.lift z.val,A.maps z.property⟩
  have hg : ContMDiff 𝓘(ℂ,ComplexModel A.source.dim) 𝓘(ℂ,ComplexModel e.dim) ∞ g := by
    apply (ContMDiff.subtypeVal_comp_iff e.ambient g).mp
    exact A.holomorphic.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  refine ⟨A.source,hA,g ⁻¹' B,
    Hironaka.AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg hB,?_⟩
  ext c
  change f.hom.left.base (A.source.toPoint c) ∈ Z ↔ g c.val ∈ B
  obtain ⟨b,hb,hpb⟩ := A.factor c
  have hgcb : g c.val = b.val := Subtype.ext hb.symm
  rw [← hpb,hgcb]
  exact Set.ext_iff.mp hrep b

/-- Genuine singleton analyticity on the ORIGINAL possibly singular space. -/
theorem isAnalyticSubset_singleton (X : SourceReducedComplexSpace) (x : X.obj.left) :
    X.IsAnalyticSubset {x} := by
  let singularAnalyticPointHausdorff : T2Space X.obj.left := X.property.1
  intro y
  by_cases hy : y = x
  · subst y
    let e := LocalEmbedding.ofPoint X x
    obtain ⟨c,hc⟩ := LocalEmbedding.mem_range_ofPoint X x
    refine ⟨e,⟨c,hc⟩,{c.val},
      Hironaka.FibreDimensionLowerBound.isComplexAnalyticSubset_singleton c.val,?_⟩
    ext z
    change e.toPoint z = x ↔ z.val = c.val
    constructor
    · intro h
      exact congrArg Subtype.val (e.toPoint_injective (h.trans hc.symm))
    · intro h
      exact (congrArg e.toPoint (Subtype.ext h)).trans hc
  · obtain ⟨e,he,hsub,-⟩ := LocalEmbedding.exists_domain (X := X) y
      (isClosed_singleton (x := x)).isOpen_compl hy
    refine ⟨e,he,∅,isComplexAnalyticSubset_empty,?_⟩
    ext z
    change e.toPoint z ∈ ({x} : Set X.obj.left) ↔ z.val ∈ (∅ : Set e.ambient)
    exact iff_false_intro (hsub ⟨z,rfl⟩)

/-- The literal fiber of the actual original morphism is genuinely analytic. -/
theorem isAnalyticSubset_fiber {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (x : X.obj.left) : Y.IsAnalyticSubset (f.hom.left.base ⁻¹' {x}) :=
  (isAnalyticSubset_singleton X x).preimage f

end Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
