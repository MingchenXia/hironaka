import Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspace
import Hironaka.Analytic.Unibranch.HironakaG10RmGlobalComponents
import Hironaka.Analytic.Unibranch.HironakaG10MwRemmertRegular

/-!
# Global components as reduced closed subspaces (Remmert for reduced spaces, item 5.2.e)

Run 0081 lane G10R2. Consumer: item 5.7 of `G10MW/remmert-reduced-spaces.md` (native Remmert assembly),
which applies the irreducible case to each native global component `B` of a source `Y` through the reduced
closed subspace `Y_B = OriginalAnalyticClosedSubspace.sourceObject Y B hB` with its closed embedding
`ι = inclusion Y B hB`. Blueprint: `hironaka-g10rm-global-components.tex`.

* `subspaceChart Y B hB a`: the local embedding of `Y_B` given by its gluing chart at `a`: the ambient open set
  of the chosen local embedding of `Y` at `a`, with carrier the trace of `B`; `inclusion_subspaceChart`.
* `isAnalyticSubset_image_inclusion`: `ι` maps analytic subsets of `Y_B` to analytic subsets of `Y`.
* `isIrreducibleAnalyticSubset_univ_sourceObject`: if `B` is irreducible, `Y_B` is irreducible as a space;
  in particular for every native global component (`..._of_mem_nativeGlobalComponents`).
* `nativeDimLE_univ_sourceObject`: `NativeDimLE Y B m → NativeDimLE Y_B univ m` (item 5.0(b), one direction).
* `secondCountableTopology_sourceObject`; `exists_nativePureDim_of_irreducible` (5.2.4 in the shape
  `∃ d, NativePureDim Y d` of `HironakaG10MwRemmertRegular`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10RmClosedSubspace

open Hironaka Hironaka
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaReducedComplexAnalyticSpaces
  SourceReducedComplexSpace OriginalAnalyticClosedSubspace OriginalAnalyticClosedSubspaceOverlap
  HironakaG10RmGlobalComponents

noncomputable section

/-- **5.2.4 in the shape of item 5.7**: an irreducible space has pure dimension. -/
theorem exists_nativePureDim_of_irreducible {Y : SourceReducedComplexSpace}
    (h : Y.IsIrreducibleAnalyticSubset univ) : ∃ d, HironakaG10MwRemmertRegular.NativePureDim Y d :=
  (exists_pureDim_of_irreducible h).imp fun _ hd => hd.1

variable (Y : SourceReducedComplexSpace) (B : Set Y.obj.left) (hB : Y.IsAnalyticSubset B)

/-- The local embedding of the reduced closed subspace `Y_B` given by its gluing chart at `a`. -/
def subspaceChart (a : Y.obj.left) : LocalEmbedding (sourceObject Y B hB) where
  dim := (localEmbedding Y B hB a).dim
  ambient := (localEmbedding Y B hB a).ambient
  carrier := localCentre Y B hB a
  analytic := localCentre_analytic Y B hB a
  map := chartInclusion Y B hB a
  isOpenImmersion := inferInstance
  overPoint := by
    change chartInclusion Y B hB a ≫ projection Y B hB ≫ Y.obj.hom = _
    rw [← Category.assoc, chartInclusion_projection]
    exact Over.w (localProjection Y B hB a).hom

/-- The subspace charts cover `Y_B`. -/
theorem exists_subspaceChart (s : (sourceObject Y B hB).obj.left) :
    ∃ (a : Y.obj.left) (d : (subspaceChart Y B hB a).carrier),
      (subspaceChart Y B hB a).toPoint d = s :=
  chartInclusion_jointly_surjective Y B hB s

/-- In the subspace chart, the closed embedding is the chart of `Y`. -/
theorem inclusion_subspaceChart (a : Y.obj.left) (d : (subspaceChart Y B hB a).carrier) :
    (inclusion Y B hB).hom.left.base ((subspaceChart Y B hB a).toPoint d) =
      (localEmbedding Y B hB a).toPoint ⟨d.val, d.property.1⟩ := by
  have h := congrArg (fun F => F.base d) (chartInclusion_projection Y B hB a)
  exact h

/-- The carrier of the subspace chart is the trace of `B`. -/
theorem trace_eq_localCentre (a : Y.obj.left) :
    HironakaG10EpNativeDim.trace (localEmbedding Y B hB a) B = localCentre Y B hB a := by
  ext v
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.property, (Set.ext_iff.mp (ambientTrace_eq Y B hB a) c).mp hc⟩
  · rintro ⟨hvC, hvA⟩
    exact ⟨⟨v, hvC⟩, (Set.ext_iff.mp (ambientTrace_eq Y B hB a) ⟨v, hvC⟩).mpr hvA, rfl⟩

/-- **The closed embedding maps analytic subsets of `Y_B` to analytic subsets of `Y`.** -/
theorem isAnalyticSubset_image_inclusion {T : Set (sourceObject Y B hB).obj.left}
    (hT : (sourceObject Y B hB).IsAnalyticSubset T) :
    Y.IsAnalyticSubset ((inclusion Y B hB).hom.left.base '' T) := by
  intro x
  refine ⟨localEmbedding Y B hB x, mem_chartOpen_self Y B hB x,
    Subtype.val '' ((subspaceChart Y B hB x).toPoint ⁻¹' T),
    HironakaG10NativeAnalyticClosureDifference.analytic_image_trace hT (subspaceChart Y B hB x), ?_⟩
  ext c
  constructor
  · rintro ⟨t, htT, htc⟩
    have hcB : (localEmbedding Y B hB x).toPoint c ∈ B :=
      (inclusion_range Y B hB).subset ⟨t, htc⟩
    have hcA : c.val ∈ ambientTrace Y B hB x :=
      (Set.ext_iff.mp (ambientTrace_eq Y B hB x) c).mp hcB
    have hd : (subspaceChart Y B hB x).toPoint ⟨c.val, c.property, hcA⟩ = t := by
      apply (inclusion_isClosedEmbedding Y B hB).injective
      rw [inclusion_subspaceChart, htc]
    refine ⟨⟨c.val, c.property, hcA⟩, ?_, rfl⟩
    change (subspaceChart Y B hB x).toPoint ⟨c.val, c.property, hcA⟩ ∈ T
    rw [hd]
    exact htT
  · rintro ⟨d, hdT, hdc⟩
    refine ⟨(subspaceChart Y B hB x).toPoint d, hdT, ?_⟩
    rw [inclusion_subspaceChart]
    congr 1
    exact Subtype.ext hdc

/-- **An irreducible analytic subset gives an irreducible reduced closed subspace.** -/
theorem isIrreducibleAnalyticSubset_univ_sourceObject (hBirr : Y.IsIrreducibleAnalyticSubset B) :
    (sourceObject Y B hB).IsIrreducibleAnalyticSubset univ := by
  have hrange := inclusion_range Y B hB
  have hinj := (inclusion_isClosedEmbedding Y B hB).injective
  refine ⟨isAnalyticSubset_univ, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hBirr.2.1
    rw [← hrange] at hb
    obtain ⟨s, -⟩ := hb
    exact ⟨s, mem_univ s⟩
  · intro T₁ T₂ hT₁ hT₂ _ _ hunion
    have hsub : ∀ T : Set (sourceObject Y B hB).obj.left,
        (inclusion Y B hB).hom.left.base '' T ⊆ B :=
      fun T => (image_subset_range _ _).trans hrange.subset
    have hBeq : B = (inclusion Y B hB).hom.left.base '' T₁ ∪
        (inclusion Y B hB).hom.left.base '' T₂ := by
      rw [← image_union, ← hunion, image_univ, hrange]
    have key : ∀ T : Set (sourceObject Y B hB).obj.left,
        B = (inclusion Y B hB).hom.left.base '' T → univ = T := by
      intro T hT
      refine Subset.antisymm (fun s _ => ?_) (subset_univ T)
      have hs : (inclusion Y B hB).hom.left.base s ∈ (inclusion Y B hB).hom.left.base '' T := by
        rw [← hT]
        exact hrange.subset ⟨s, rfl⟩
      obtain ⟨t, ht, hts⟩ := hs
      exact hinj hts ▸ ht
    rcases hBirr.2.2 _ _ (isAnalyticSubset_image_inclusion Y B hB hT₁)
        (isAnalyticSubset_image_inclusion Y B hB hT₂) (hsub _) (hsub _) hBeq with h | h
    · exact Or.inl (key T₁ h)
    · exact Or.inr (key T₂ h)

/-- **The reduced closed subspace on a native global component is irreducible.** -/
theorem isIrreducibleAnalyticSubset_univ_sourceObject_of_mem_nativeGlobalComponents
    (hBc : B ∈ nativeGlobalComponents Y) :
    (sourceObject Y B hB).IsIrreducibleAnalyticSubset univ :=
  isIrreducibleAnalyticSubset_univ_sourceObject Y B hB
    (isIrreducibleAnalyticSubset_of_mem_nativeGlobalComponents hBc)

/-- The reduced closed subspace on a native global component has pure dimension. -/
theorem exists_nativePureDim_sourceObject_of_mem_nativeGlobalComponents
    (hBc : B ∈ nativeGlobalComponents Y) :
    ∃ d, HironakaG10MwRemmertRegular.NativePureDim (sourceObject Y B hB) d :=
  exists_nativePureDim_of_irreducible
    (isIrreducibleAnalyticSubset_univ_sourceObject_of_mem_nativeGlobalComponents Y B hB hBc)

/-- **Dimension of the subspace (5.0(b), one direction).** -/
theorem nativeDimLE_univ_sourceObject {m : ℕ} (h : HironakaG10EpNativeDim.NativeDimLE Y B m) :
    HironakaG10EpNativeDim.NativeDimLE (sourceObject Y B hB) univ m := by
  intro e' y k hy
  rw [HironakaG10EpNativeDim.trace_univ] at hy
  have hint := (HironakaG10EpNativeDim.regularAtDim_carrier_iff e' ⟨y, hy.2.1⟩ k).mp hy
  obtain ⟨a, d, hd⟩ := exists_subspaceChart Y B hB (e'.toPoint ⟨y, hy.2.1⟩)
  have hreg : RegularAtDim (n := (subspaceChart Y B hB a).dim) (subspaceChart Y B hB a).carrier
      d.val k := by
    refine (HironakaG10EpNativeDim.regularAtDim_carrier_iff (subspaceChart Y B hB a) d k).mpr ?_
    rw [hd]
    exact hint
  refine h (localEmbedding Y B hB a) d.val k ?_
  rw [trace_eq_localCentre]
  exact hreg

/-- The reduced closed subspace of a second-countable space is second countable. -/
theorem secondCountableTopology_sourceObject [hY : SecondCountableTopology Y.obj.left] :
    SecondCountableTopology (sourceObject Y B hB).obj.left := by
  have : SecondCountableTopology Y.obj.left.toPresheafedSpace := hY
  exact (inclusion_isClosedEmbedding Y B hB).isEmbedding.secondCountableTopology

end

end Hironaka.Analytic.Unibranch.HironakaG10RmClosedSubspace
