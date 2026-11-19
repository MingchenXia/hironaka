import Hironaka.Analytic.Unibranch.EmbeddedCommonResolutionGeneralAnalyticSubsets
import Hironaka.Analytic.Unibranch.EmbeddedCommonResolution

/-!
# A common smooth model from the ORIGINAL proper bimeromorphic maps

The original independent intrinsic exceptional sets produce their own common
ambient analytic exceptional set. Original good-open restrictions and thinness
are derived; no shared exceptional set or native comparison is supplied.
Both actual analytic modifications and the original whole sheaf square remain
the output of the frozen common-model producer.

Blueprint: `embedded-common-resolution-general.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch

noncomputable section

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaReducedComplexAnalyticSpaces
  HironakaEmbeddedNativeMorphism AnalyticModificationLocalDiscrepancy

namespace SourceReducedComplexSpace

variable {X Y : SourceReducedComplexSpace} {F : Y ⟶ X}

/-- Restrict the ORIGINAL isomorphism-over witness to a smaller original open. -/
theorem IsIsoOver.of_isOpen_subset {U W : Set X.obj.left} (hF : IsIsoOver F U)
    (hW : IsOpen W) (hWU : W ⊆ U) : IsIsoOver F W := by
  obtain ⟨V, j, hj, hjrange, hjF, hjFrange⟩ := hF
  have : LocallyRingedSpace.IsOpenImmersion j := hj
  have : LocallyRingedSpace.IsOpenImmersion (j ≫ F.hom.left) := hjF
  let T : Opens V := ⟨(j ≫ F.hom.left).base ⁻¹' W,
    hW.preimage (j ≫ F.hom.left).base.hom.continuous⟩
  let k := V.ofRestrict (Opens.isOpenEmbedding T)
  refine ⟨V.restrict (Opens.isOpenEmbedding T), k ≫ j, inferInstance, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact v.property
    · intro hy
      have hyU : y ∈ range j.base := by
        rw [hjrange]
        exact hWU hy
      obtain ⟨v, hv⟩ := hyU
      refine ⟨⟨v, ?_⟩, hv⟩
      change F.hom.left.base (j.base v) ∈ W
      rwa [hv]
  · change LocallyRingedSpace.IsOpenImmersion (k ≫ (j ≫ F.hom.left))
    infer_instance
  · ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact v.property
    · intro hx
      have hxU : x ∈ range (j ≫ F.hom.left).base := by
        rw [hjFrange]
        exact hWU hx
      obtain ⟨v, hv⟩ := hxU
      refine ⟨⟨v, ?_⟩, hv⟩
      change (j ≫ F.hom.left).base v ∈ W
      rwa [hv]

/-- The ORIGINAL dense isomorphism locus forces inverse images of EVERY thin
target set to be thin; neither target irreducibility nor a native map is used. -/
theorem IsIsoOver.interior_preimage_eq_empty {E A : Set X.obj.left}
    (hF : IsIsoOver F Eᶜ)
    (hE : interior (F.hom.left.base ⁻¹' E) = ∅) (hA : interior A = ∅) :
    interior (F.hom.left.base ⁻¹' A) = ∅ := by
  obtain ⟨V, j, hj, hjrange, hjF, _⟩ := hF
  have hsub : interior (F.hom.left.base ⁻¹' A) ⊆ F.hom.left.base ⁻¹' E := by
    intro y hy
    by_contra hyE
    have hyrange : y ∈ range j.base := by
      rw [hjrange]
      exact hyE
    obtain ⟨v, hv⟩ := hyrange
    let T : Set V := j.base ⁻¹' interior (F.hom.left.base ⁻¹' A)
    have hTo : IsOpen T := isOpen_interior.preimage j.base.hom.continuous
    have hvT : v ∈ T := by
      change j.base v ∈ interior (F.hom.left.base ⁻¹' A)
      rwa [hv]
    have hWo : IsOpen ((j ≫ F.hom.left).base '' T) :=
      hjF.base_open.isOpenMap T hTo
    have hWA : (j ≫ F.hom.left).base '' T ⊆ A := by
      rintro _ ⟨w, hw, rfl⟩
      exact (interior_subset : interior (F.hom.left.base ⁻¹' A) ⊆
        F.hom.left.base ⁻¹' A) hw
    have hmem : (j ≫ F.hom.left).base v ∈ interior A :=
      interior_maximal hWA hWo ⟨v, hvT, rfl⟩
    rw [hA] at hmem
    exact hmem
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hmem := interior_maximal hsub isOpen_interior hy
  rw [hE] at hmem
  exact hmem

end SourceReducedComplexSpace

open SourceReducedComplexSpace

section CommonModel

variable {m n : ℕ} {M Y₀ Y₁ : Type}
  [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [CompactSpace Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
  [CompactSpace Y₁] [ConnectedSpace Y₁]
  {D : Set M} (hD : IsComplexAnalyticSubset (n := m) D)

/-- GIVEN the ORIGINAL proper bimeromorphic maps to the SAME singular embedded
base, construct a common native smooth model, both ACTUAL analytic modifications
and the WHOLE original sheaf square. The common exceptional set is produced. -/
theorem exists_embedded_common_model_of_isProperBimeromorphic
    (F₀ : ofClosedAnalytic (n := n) (univ : Set Y₀)
        (isComplexAnalyticSubset_univ (n := n)) ⟶ ofClosedAnalytic (n := m) D hD)
    (F₁ : ofClosedAnalytic (n := n) (univ : Set Y₁)
        (isComplexAnalyticSubset_univ (n := n)) ⟶ ofClosedAnalytic (n := m) D hD)
    (hF₀ : IsProperBimeromorphic F₀) (hF₁ : IsProperBimeromorphic F₁) :
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
  obtain ⟨_, E₀, hE₀a, hE₀t, hpre₀, hiso₀⟩ := hF₀
  obtain ⟨_, E₁, hE₁a, hE₁t, hpre₁, hiso₁⟩ := hF₁
  let B : Set M := (Subtype.val : D → M) '' E₀ ∪ (Subtype.val : D → M) '' E₁
  have hBa : IsComplexAnalyticSubset (n := m) B :=
    ConstantRankImage.IsComplexAnalyticSubset.union
      (isComplexAnalyticSubset_image_of_isAnalyticSubset_closedAnalytic hE₀a)
      (isComplexAnalyticSubset_image_of_isAnalyticSubset_closedAnalytic hE₁a)
  have hBtrace : (Subtype.val : D → M) ⁻¹' B = E₀ ∪ E₁ := by
    simp only [B, preimage_union, Subtype.val_injective.preimage_image]
  have hW : IsOpen ((E₀ ∪ E₁)ᶜ) := (hE₀a.isClosed.union hE₁a.isClosed).isOpen_compl
  have hi₀ : IsIsoOver F₀ (E₀ ∪ E₁)ᶜ :=
    hiso₀.of_isOpen_subset hW (fun _ hx h => hx (Or.inl h))
  have hi₁ : IsIsoOver F₁ (E₀ ∪ E₁)ᶜ :=
    hiso₁.of_isOpen_subset hW (fun _ hx h => hx (Or.inr h))
  have hcross₀ : interior (F₀.hom.left.base ⁻¹' E₁) = ∅ :=
    hiso₀.interior_preimage_eq_empty hpre₀ hE₁t
  have hcross₁ : interior (F₁.hom.left.base ⁻¹' E₀) = ∅ :=
    hiso₁.interior_preimage_eq_empty hpre₁ hE₀t
  have ht₀ : interior (F₀.hom.left.base ⁻¹' (E₀ ∪ E₁)) = ∅ := by
    rw [preimage_union, interior_union_isClosed_of_interior_empty
      (hE₀a.isClosed.preimage F₀.hom.left.base.hom.continuous) hcross₀]
    exact hpre₀
  have ht₁ : interior (F₁.hom.left.base ⁻¹' (E₀ ∪ E₁)) = ∅ := by
    rw [preimage_union, interior_union_isClosed_of_interior_empty
      (hE₀a.isClosed.preimage F₁.hom.left.base.hom.continuous) hpre₁]
    exact hcross₁
  refine exists_embedded_common_model_of_isIsoOver hD F₀ F₁ hBa ?_ ?_ ?_ ?_
  · rw [hBtrace]
    exact hi₀
  · rw [hBtrace]
    exact hi₁
  · rw [hBtrace]
    exact ht₀
  · rw [hBtrace]
    exact ht₁

end CommonModel

end

end Hironaka.Analytic.Unibranch
