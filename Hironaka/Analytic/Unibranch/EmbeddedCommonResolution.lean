import Hironaka.Analytic.Unibranch.Resolution
import Hironaka.Resolution.HironakaEmbeddedNativeMorphismCommon

/-!
# Common native models from the ORIGINAL complex-space isomorphism loci

The original `SourceReducedComplexSpace.IsIsoOver` witnesses construct the
native good-open comparison; no native morphism, comparison or singleton-
fibre law is assumed. The common compact smooth model retains both actual
analytic-modification projections and the whole original sheaf square.

The common ambient analytic exceptional set remains explicit. This does not
claim the full non-embeddable or smooth-centre modification form of G11.
Blueprint: `embedded-common-resolution.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch

noncomputable section

open Hironaka Hironaka.BlowupSequences
  Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaEmbeddedNativeMorphism HironakaResolutionSpaceComplex
  AnalyticModificationLocalDiscrepancy SourceReducedComplexSpace

private theorem interior_eq_empty_of_preimage_univ {Y : Type} [TopologicalSpace Y]
    {A : Set Y}
    (h : interior ((Subtype.val : ↥(Set.univ : Set Y) → Y) ⁻¹' A) = ∅) :
    interior A = ∅ := by
  have hi := isOpen_univ.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
    (continuous_subtype_val : Continuous (Subtype.val : ↥(Set.univ : Set Y) → Y)) A
  rw [h] at hi
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hmem : (⟨y, mem_univ y⟩ : ↥(Set.univ : Set Y)) ∈
      (Subtype.val : ↥(Set.univ : Set Y) → Y) ⁻¹' interior A := hy
  rw [hi] at hmem
  exact hmem

section OriginalRestriction

variable {m n : ℕ} {M Y : Type}
  [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {D B : Set M} (hD : IsComplexAnalyticSubset (n := m) D)

/-- The original `IsIsoOver` witness makes the literal original native-open
restriction an actual open immersion, with exactly the SAME original image. -/
theorem original_restriction_of_isIsoOver
    (F : ofClosedAnalytic (n := n) (univ : Set Y)
        (isComplexAnalyticSubset_univ (n := n)) ⟶ ofClosedAnalytic (n := m) D hD)
    (hBc : IsClosed B)
    (hiso : IsIsoOver F (((Subtype.val : D → M) ⁻¹' B)ᶜ)) :
    LocallyRingedSpace.IsOpenImmersion
      (restrictedOriginalMorphism F.hom.left (Over.w F.hom) B hBc) ∧
      range (restrictedOriginalMorphism F.hom.left (Over.w F.hom) B hBc).base =
        ((Subtype.val : D → M) ⁻¹' B)ᶜ := by
  obtain ⟨V, j, hj, hjrange, hjF, hjFrange⟩ := hiso
  have : LocallyRingedSpace.IsOpenImmersion j := hj
  have : LocallyRingedSpace.IsOpenImmersion (j ≫ F.hom.left) := hjF
  let O := originalGoodOpen F.hom.left (Over.w F.hom) B hBc
  let J := actualOpenSubspaceMap (n := n) (univ : Set Y) O
  have hJrange : range J.base = F.hom.left.base ⁻¹' (((Subtype.val : D → M) ⁻¹' B)ᶜ) := by
    rw [range_actualOpenSubspaceMap]
    ext y
    rfl
  let E := openImmersionIsoOfRangeEq J j (hJrange.trans hjrange.symm)
  have hEfac : E.hom ≫ j = J :=
    openImmersionIsoOfRangeEq_hom_fac J j (hJrange.trans hjrange.symm)
  have hR : restrictedOriginalMorphism F.hom.left (Over.w F.hom) B hBc =
      E.hom ≫ (j ≫ F.hom.left) := by
    rw [← Category.assoc, hEfac]
    rfl
  constructor
  · rw [hR]
    infer_instance
  · rw [hR, range_iso_hom_comp_base]
    exact hjFrange

end OriginalRestriction

section CommonModel

variable {m n : ℕ} {M Y₀ Y₁ : Type}
  [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [CompactSpace Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
  [CompactSpace Y₁] [ConnectedSpace Y₁]
  {D B : Set M} (hD : IsComplexAnalyticSubset (n := m) D)

/-- Given original complex-space isomorphisms over ONE original good open,
construct the actual common native smooth model and the complete original
locally ringed-space equality, with no incoming native comparison. -/
theorem exists_embedded_common_model_of_isIsoOver
    (F₀ : ofClosedAnalytic (n := n) (univ : Set Y₀)
        (isComplexAnalyticSubset_univ (n := n)) ⟶ ofClosedAnalytic (n := m) D hD)
    (F₁ : ofClosedAnalytic (n := n) (univ : Set Y₁)
        (isComplexAnalyticSubset_univ (n := n)) ⟶ ofClosedAnalytic (n := m) D hD)
    (hBa : IsComplexAnalyticSubset (n := m) B)
    (hiso₀ : IsIsoOver F₀ (((Subtype.val : D → M) ⁻¹' B)ᶜ))
    (hiso₁ : IsIsoOver F₁ (((Subtype.val : D → M) ⁻¹' B)ᶜ))
    (hthin₀ : interior (F₀.hom.left.base ⁻¹' ((Subtype.val : D → M) ⁻¹' B)) = ∅)
    (hthin₁ : interior (F₁.hom.left.base ⁻¹' ((Subtype.val : D → M) ⁻¹' B)) = ∅) :
    ∃ (Z : Type) (_ : TopologicalSpace Z) (_ : ChartedSpace (ComplexModel n) Z)
      (_ : IsComplexManifold n Z) (_ : ConnectedSpace Z) (_ : CompactSpace Z)
      (g₀ : Z → Y₀) (g₁ : Z → Y₁)
      (hg₀ : IsAnalyticModification (n := n) g₀)
      (hg₁ : IsAnalyticModification (n := n) g₁),
      originalPointMap F₀.hom.left ∘ g₀ = originalPointMap F₁.hom.left ∘ g₁ ∧
      actualSubspaceMap hg₀.1 (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₀ z)) ≫
          F₀.hom.left =
        actualSubspaceMap hg₁.1 (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₁ z)) ≫
          F₁.hom.left := by
  obtain ⟨hR₀, hrange₀⟩ := original_restriction_of_isIsoOver hD F₀ hBa.isClosed hiso₀
  obtain ⟨hR₁, hrange₁⟩ := original_restriction_of_isIsoOver hD F₁ hBa.isClosed hiso₁
  have : LocallyRingedSpace.IsOpenImmersion
      (restrictedOriginalMorphism F₀.hom.left (Over.w F₀.hom) B hBa.isClosed) := hR₀
  have : LocallyRingedSpace.IsOpenImmersion
      (restrictedOriginalMorphism F₁.hom.left (Over.w F₁.hom) B hBa.isClosed) := hR₁
  have hn₀ : interior (originalPointMap F₀.hom.left ⁻¹' B) = ∅ :=
    interior_eq_empty_of_preimage_univ hthin₀
  have hn₁ : interior (originalPointMap F₁.hom.left ⁻¹' B) = ∅ :=
    interior_eq_empty_of_preimage_univ hthin₁
  exact exists_original_compact_smooth_common_model F₀.hom.left F₁.hom.left
    (Over.w F₀.hom) (Over.w F₁.hom) hBa hn₀ hn₁ (hrange₁.trans hrange₀.symm)

end CommonModel

end

end Hironaka.Analytic.Unibranch
