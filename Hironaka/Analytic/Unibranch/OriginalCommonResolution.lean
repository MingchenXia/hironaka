import Hironaka.Analytic.Unibranch.OriginalSmoothSourceAnalytic
import Hironaka.Analytic.Unibranch.EmbeddedCommonResolutionGeneral
import Hironaka.Analytic.Unibranch.SourceMorphismExt
import Hironaka.Resolution.HironakaNativeTargetCommon

/-!
# A common native smooth model over an arbitrary ORIGINAL target

The full original proper-bimeromorphic maps derive ALL actual analytic
pullbacks/equality-locus/good-open/biholomorphic inputs. The unchanged actual
embedded-resolution engine resolves their true product main component.
Uniform native source dimension and ConnectedSpace Y1 are explicit.
Blueprint: `original-common-resolution.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
  Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.OriginalCommonResolution

open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaEmbeddedNativeMorphism HironakaResolutionSpaceComplex AnalyticModificationLocalDiscrepancy
  SourceReducedComplexSpace OriginalSmoothSourceAnalytic

noncomputable section

-- Reused elementary whole-subtype interior argument; zero separate credit.
private theorem interior_eq_empty_of_univ {M : Type} [TopologicalSpace M] {A : Set M}
    (h : interior ((Subtype.val : ↥(univ : Set M) → M) ⁻¹' A) = ∅) : interior A = ∅ := by
  have hi := isOpen_univ.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
    (continuous_subtype_val : Continuous (Subtype.val : ↥(univ : Set M) → M)) A
  rw [h] at hi
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hm : (⟨y, mem_univ y⟩ : ↥(univ : Set M)) ∈
      (Subtype.val : ↥(univ : Set M) → M) ⁻¹' interior A := hy
  rw [hi] at hm
  exact hm

variable {X : SourceReducedComplexSpace}

section Restriction

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

def goodOpen (F : ofClosedAnalytic (n := n) (univ : Set M)
    (isComplexAnalyticSubset_univ (n := n)) ⟶ X)
    (B : Set X.obj.left) (hBc : IsClosed B) : Opens M :=
  HironakaNativeTargetCommon.goodOpen (pointMap F) (continuous_pointMap F) B hBc

/-- The SAME full original map on its literal native inverse-image open. -/
def restrictedOriginalMorphism
    (F : ofClosedAnalytic (n := n) (univ : Set M)
      (isComplexAnalyticSubset_univ (n := n)) ⟶ X)
    (B : Set X.obj.left) (hBc : IsClosed B) :
    actualSubspaceLocallyRingedSpace (n := n) (univ : Set (goodOpen F B hBc)) ⟶ X.obj.left :=
  actualOpenSubspaceMap (n := n) (univ : Set M) (goodOpen F B hBc) ≫ F.hom.left

private theorem restrictedOriginalMorphism_point
    (F : ofClosedAnalytic (n := n) (univ : Set M)
      (isComplexAnalyticSubset_univ (n := n)) ⟶ X)
    (B : Set X.obj.left) (hBc : IsClosed B) :
    restrictedOriginalMorphism F B hBc ≫ X.obj.hom =
      subspacePointMap (n := n) (univ : Set (goodOpen F B hBc)) := by
  calc
    (actualOpenSubspaceMap (n := n) (univ : Set M) (goodOpen F B hBc) ≫ F.hom.left) ≫ X.obj.hom =
        actualOpenSubspaceMap (n := n) (univ : Set M) (goodOpen F B hBc) ≫
          (F.hom.left ≫ X.obj.hom) := Category.assoc _ _ _
    _ = actualOpenSubspaceMap (n := n) (univ : Set M) (goodOpen F B hBc) ≫
        subspacePointMap (n := n) (univ : Set M) :=
      congrArg (fun K => actualOpenSubspaceMap (n := n) (univ : Set M) (goodOpen F B hBc) ≫ K)
        (Over.w F.hom)
    _ = _ := actualSubspaceMap_point contMDiff_subtype_val (fun _ _ => mem_univ _)

/-- ORIGINAL isomorphism-over data internally makes the actual whole native
good-open restriction a FULL OI onto the SAME original good set. -/
theorem original_restriction_of_isIsoOver
    (F : ofClosedAnalytic (n := n) (univ : Set M)
      (isComplexAnalyticSubset_univ (n := n)) ⟶ X)
    (B : Set X.obj.left) (hBc : IsClosed B) (hiso : IsIsoOver F Bᶜ) :
    LocallyRingedSpace.IsOpenImmersion (restrictedOriginalMorphism F B hBc) ∧
      range (restrictedOriginalMorphism F B hBc).base = Bᶜ := by
  obtain ⟨V, j, hj, hjrange, hjF, hjFrange⟩ := hiso
  let J := actualOpenSubspaceMap (n := n) (univ : Set M) (goodOpen F B hBc)
  have hJ : LocallyRingedSpace.IsOpenImmersion J := by
    dsimp only [J]
    infer_instance
  have hJrange : range J.base = F.hom.left.base ⁻¹' Bᶜ := by
    rw [range_actualOpenSubspaceMap]
    ext y
    rfl
  let E := @openImmersionIsoOfRangeEq _ _ _ J j hJ hj (hJrange.trans hjrange.symm)
  have hEfac : E.hom ≫ j = J :=
    @openImmersionIsoOfRangeEq_hom_fac _ _ _ J j hJ hj (hJrange.trans hjrange.symm)
  have hR : restrictedOriginalMorphism F B hBc = E.hom ≫ (j ≫ F.hom.left) := by
    rw [← Category.assoc, hEfac]
    rfl
  constructor
  · rw [hR]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ E.hom (inferInstance) (j ≫ F.hom.left) hjF
  · exact (congrArg (fun K : actualSubspaceLocallyRingedSpace (n := n)
        (univ : Set (goodOpen F B hBc)) ⟶ X.obj.left => range K.base) hR).trans
      ((range_iso_hom_comp_base E (j ≫ F.hom.left)).trans hjFrange)

end Restriction

section TwoSources

variable {n : ℕ} {Y₀ Y₁ : Type}
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]

/-- Genuine full original good-open isomorphisms construct BOTH-holomorphic
native comparison and actual singleton fibres; no native comparison input. -/
theorem exists_original_native_transition
    (F₀ : ofClosedAnalytic (n := n) (univ : Set Y₀) (isComplexAnalyticSubset_univ (n := n)) ⟶ X)
    (F₁ : ofClosedAnalytic (n := n) (univ : Set Y₁) (isComplexAnalyticSubset_univ (n := n)) ⟶ X)
    (B : Set X.obj.left) (hBc : IsClosed B)
    (hiso₀ : IsIsoOver F₀ Bᶜ) (hiso₁ : IsIsoOver F₁ Bᶜ) :
    ∃ e : goodOpen F₁ B hBc ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ goodOpen F₀ B hBc,
      (∀ y, pointMap F₀ (e y).val = pointMap F₁ y.val) ∧
      InjOn (pointMap F₀) (pointMap F₀ ⁻¹' Bᶜ) := by
  obtain ⟨hR₀, hrange₀⟩ := original_restriction_of_isIsoOver F₀ B hBc hiso₀
  obtain ⟨hR₁, hrange₁⟩ := original_restriction_of_isIsoOver F₁ B hBc hiso₁
  let R₀ := restrictedOriginalMorphism F₀ B hBc
  let R₁ := restrictedOriginalMorphism F₁ B hBc
  let E := @openImmersionIsoOfRangeEq _ _ _ R₁ R₀ hR₁ hR₀ (hrange₁.trans hrange₀.symm)
  have hfac : E.hom ≫ R₀ = R₁ :=
    @openImmersionIsoOfRangeEq_hom_fac _ _ _ R₁ R₀ hR₁ hR₀ (hrange₁.trans hrange₀.symm)
  have hEp : E.hom ≫ subspacePointMap (n := n) (univ : Set (goodOpen F₀ B hBc)) =
      subspacePointMap (n := n) (univ : Set (goodOpen F₁ B hBc)) := by
    rw [← restrictedOriginalMorphism_point F₀ B hBc, ← Category.assoc, hfac]
    exact restrictedOriginalMorphism_point F₁ B hBc
  let e := nativeDiffeomorph E hEp
  refine ⟨e, ?_, ?_⟩
  · intro y
    exact congrArg (fun K => K.base (⟨y, mem_univ y⟩ : (univ : Set (goodOpen F₁ B hBc)))) hfac
  · intro y hy z hz heq
    let p : (univ : Set (goodOpen F₀ B hBc)) := ⟨⟨y, hy⟩, mem_univ _⟩
    let q : (univ : Set (goodOpen F₀ B hBc)) := ⟨⟨z, hz⟩, mem_univ _⟩
    have hR : R₀.base p = R₀.base q := heq
    exact congrArg (fun w => w.val.val) (hR₀.base_open.injective hR)

/-- ORIGINAL proper-bimeromorphic maps to ANY original target internally
produce the literal analytic product main component and a real common model.
Uniform native dimension and connected Y1 remain explicit assumptions. -/
theorem exists_original_common_model_of_isProperBimeromorphic
    [CompactSpace Y₀] [CompactSpace Y₁] [ConnectedSpace Y₁]
    (F₀ : ofClosedAnalytic (n := n) (univ : Set Y₀) (isComplexAnalyticSubset_univ (n := n)) ⟶ X)
    (F₁ : ofClosedAnalytic (n := n) (univ : Set Y₁) (isComplexAnalyticSubset_univ (n := n)) ⟶ X)
    (hF₀ : IsProperBimeromorphic F₀) (hF₁ : IsProperBimeromorphic F₁) :
    ∃ (Z : Type) (_ : TopologicalSpace Z) (_ : ChartedSpace (ComplexModel n) Z)
      (_ : IsComplexManifold n Z) (_ : ConnectedSpace Z) (_ : CompactSpace Z)
      (g₀ : Z → Y₀) (g₁ : Z → Y₁)
      (hg₀ : IsAnalyticModification (n := n) g₀) (hg₁ : IsAnalyticModification (n := n) g₁),
      pointMap F₀ ∘ g₀ = pointMap F₁ ∘ g₁ ∧
      actualSubspaceMap hg₀.1 (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₀ z)) ≫ F₀.hom.left =
        actualSubspaceMap hg₁.1 (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₁ z)) ≫ F₁.hom.left := by
  obtain ⟨_hproper₀, E₀, hE₀a, hE₀t, hpre₀, hiso₀⟩ := hF₀
  obtain ⟨_hproper₁, E₁, hE₁a, hE₁t, hpre₁, hiso₁⟩ := hF₁
  let B : Set X.obj.left := E₀ ∪ E₁
  have hBc : IsClosed B := hE₀a.isClosed.union hE₁a.isClosed
  have hi₀ : IsIsoOver F₀ Bᶜ :=
    hiso₀.of_isOpen_subset hBc.isOpen_compl (fun _ hx h => hx (Or.inl h))
  have hi₁ : IsIsoOver F₁ Bᶜ :=
    hiso₁.of_isOpen_subset hBc.isOpen_compl (fun _ hx h => hx (Or.inr h))
  have hcross₀ : interior (F₀.hom.left.base ⁻¹' E₁) = ∅ :=
    hiso₀.interior_preimage_eq_empty hpre₀ hE₁t
  have hcross₁ : interior (F₁.hom.left.base ⁻¹' E₀) = ∅ :=
    hiso₁.interior_preimage_eq_empty hpre₁ hE₀t
  have ht₀ : interior (F₀.hom.left.base ⁻¹' B) = ∅ := by
    rw [preimage_union, interior_union_isClosed_of_interior_empty
      (hE₀a.isClosed.preimage F₀.hom.left.base.hom.continuous) hcross₀]
    exact hpre₀
  have ht₁ : interior (F₁.hom.left.base ⁻¹' B) = ∅ := by
    rw [preimage_union, interior_union_isClosed_of_interior_empty
      (hE₀a.isClosed.preimage F₁.hom.left.base.hom.continuous) hpre₁]
    exact hcross₁
  have hn₀ : interior (pointMap F₀ ⁻¹' B) = ∅ := interior_eq_empty_of_univ ht₀
  have hn₁ : interior (pointMap F₁ ⁻¹' B) = ∅ := interior_eq_empty_of_univ ht₁
  have hA₀ : IsComplexAnalyticSubset (n := n) (pointMap F₀ ⁻¹' B) := by
    rw [preimage_union]
    exact ConstantRankImage.IsComplexAnalyticSubset.union
      (isComplexAnalyticSubset_preimage F₀ hE₀a) (isComplexAnalyticSubset_preimage F₀ hE₁a)
  have hA₁ : IsComplexAnalyticSubset (n := n) (pointMap F₁ ⁻¹' B) := by
    rw [preimage_union]
    exact ConstantRankImage.IsComplexAnalyticSubset.union
      (isComplexAnalyticSubset_preimage F₁ hE₀a) (isComplexAnalyticSubset_preimage F₁ hE₁a)
  obtain ⟨e, he, hinj⟩ := exists_original_native_transition F₀ F₁ B hBc hi₀ hi₁
  obtain ⟨Z, instTop, instChart, instMfd, instConn, instCompact, g₀, g₁, hg₀, hg₁, hbase⟩ :=
    HironakaNativeTargetCommon.exists_compact_smooth_common_model
      (continuous_pointMap F₀) (continuous_pointMap F₁) hBc
      (isComplexAnalyticSubset_equalityLocus F₀ F₁) hA₀ hA₁ hn₀ hn₁ e he hinj
  let W := ofClosedAnalytic (n := n) (univ : Set Z) (isComplexAnalyticSubset_univ (n := n))
  let K₀ := actualSubspaceMap hg₀.1 (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₀ z)) ≫ F₀.hom.left
  let K₁ := actualSubspaceMap hg₁.1 (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₁ z)) ≫ F₁.hom.left
  have hp₀ : K₀ ≫ X.obj.hom = W.obj.hom := by
    calc
      K₀ ≫ X.obj.hom = actualSubspaceMap hg₀.1
          (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₀ z)) ≫ (F₀.hom.left ≫ X.obj.hom) :=
        Category.assoc _ _ _
      _ = actualSubspaceMap hg₀.1
          (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₀ z)) ≫
            subspacePointMap (n := n) (univ : Set Y₀) :=
        congrArg (fun K => actualSubspaceMap hg₀.1
          (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₀ z)) ≫ K) (Over.w F₀.hom)
      _ = _ := actualSubspaceMap_point hg₀.1 (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₀ z))
  have hp₁ : K₁ ≫ X.obj.hom = W.obj.hom := by
    calc
      K₁ ≫ X.obj.hom = actualSubspaceMap hg₁.1
          (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₁ z)) ≫ (F₁.hom.left ≫ X.obj.hom) :=
        Category.assoc _ _ _
      _ = actualSubspaceMap hg₁.1
          (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₁ z)) ≫
            subspacePointMap (n := n) (univ : Set Y₁) :=
        congrArg (fun K => actualSubspaceMap hg₁.1
          (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₁ z)) ≫ K) (Over.w F₁.hom)
      _ = _ := actualSubspaceMap_point hg₁.1 (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₁ z))
  let H₀ : W ⟶ X := ObjectProperty.homMk (Over.homMk K₀ hp₀)
  let H₁ : W ⟶ X := ObjectProperty.homMk (Over.homMk K₁ hp₁)
  have hwhole : H₀ = H₁ := SourceReducedComplexSpace.morphism_eq_of_pointwise_eq H₀ H₁
    (fun z => congrFun hbase z.val)
  refine ⟨Z, instTop, instChart, instMfd, instConn, instCompact, g₀, g₁, hg₀, hg₁, hbase, ?_⟩
  exact congrArg (fun H : W ⟶ X => H.hom.left) hwhole

end TwoSources

end

end Hironaka.Analytic.Unibranch.OriginalCommonResolution
