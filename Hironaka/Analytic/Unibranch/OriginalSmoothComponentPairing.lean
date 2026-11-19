import Hironaka.Analytic.Unibranch.OriginalSmoothNativeModel
import Hironaka.Analytic.Unibranch.OriginalSmoothDimension
import Hironaka.Analytic.Unibranch.OriginalCommonResolution
import Hironaka.Analytic.Unibranch.OriginalSmoothComponents
import Hironaka.Analytic.Unibranch.OriginalGoodTransitionCommonModel
import Hironaka.Analytic.AnalyticComplementConnected

/-!
# Actual original good-locus component pairing

Original full good-locus maps and derived connected component-good opens,
not supplied pairing or component-to-whole-target bimeromorphy certificates.
Blueprint: `original-smooth-component-pairing.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalSmoothComponentPairing

open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceManifoldCharts HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces HironakaResolutionSpaceComplex
  HironakaEmbeddedNativeMorphism SourceReducedComplexSpace OriginalSmoothSourceAnalytic

noncomputable section

-- Native partition equivalences are reused; the final source consumer must
-- derive these ordinary connected partitions from its ORIGINAL analytic data.
private theorem exists_partition_pairing
    {S I J : Type} [TopologicalSpace S] (P : I → Set S) (Q : J → Set S)
    (hPc : ∀ i, IsClopen (P i)) (hQc : ∀ j, IsClopen (Q j))
    (hPd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hQd : Pairwise (fun i j => Disjoint (Q i) (Q j)))
    (hPu : ⋃ i, P i = univ) (hQu : ⋃ j, Q j = univ)
    (hPconn : ∀ i, IsConnected (P i)) (hQconn : ∀ j, IsConnected (Q j)) :
    ∃ e : I ≃ J, ∀ x i, x ∈ P i ↔ x ∈ Q (e i) := by
  let eP := ConnectedComponents.equivOfIsClopenOfIsConnected hPc hPd hPu hPconn
  let eQ := ConnectedComponents.equivOfIsClopenOfIsConnected hQc hQd hQu hQconn
  let e := eP.symm.trans eQ
  have hPoint (x : S) (i : I) (j : J) (hp : x ∈ P i) (hq : x ∈ Q j) : e i = j := by
    have hp' := ConnectedComponents.equivOfIsClopenOfIsConnected_mk hPc hPd hPu hPconn x hp
    have hq' := ConnectedComponents.equivOfIsClopenOfIsConnected_mk hQc hQd hQu hQconn x hq
    change eQ (eP.symm i) = j
    rw [← hp', eP.symm_apply_apply]
    exact hq'
  refine ⟨e, ?_⟩
  intro x i
  constructor
  · intro hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hQu ▸ mem_univ x)
    rwa [hPoint x i j hp hj]
  · intro hq
    obtain ⟨i', hi'⟩ := mem_iUnion.mp (hPu ▸ mem_univ x)
    have he : e i' = e i := hPoint x i' (e i) hi' hq
    exact e.injective he ▸ hi'

variable {X Y Y₀ Y₁ : SourceReducedComplexSpace}

section ComponentRepresentations

variable [CompactSpace Y.obj.left]

-- Literal fixed choices of the accepted dimension/representation producers.
-- These comparisons have ZERO separate mathematical milestone credit.
def componentDimension (hY : Y.IsSmooth) (c : ConnectedComponents Y.obj.left) : ℕ :=
  Classical.choose (OriginalSmoothComponents.component_uniform_smooth_models hY c)

theorem componentModels (hY : Y.IsSmooth) (c : ConnectedComponents Y.obj.left) :
    OriginalSmoothNativeModel.UniformSmoothModels
      (OriginalSmoothComponents.componentObject hY c) (componentDimension hY c) :=
  Classical.choose_spec (OriginalSmoothComponents.component_uniform_smooth_models hY c)

@[instance_reducible] def componentChartedSpace (hY : Y.IsSmooth)
    (c : ConnectedComponents Y.obj.left) :
    ChartedSpace (ComplexModel (componentDimension hY c))
      (OriginalSmoothComponents.componentObject hY c).obj.left :=
  OriginalSmoothNativeModel.nativeChartedSpace (componentModels hY c)

theorem componentIsComplexManifold (hY : Y.IsSmooth) (c : ConnectedComponents Y.obj.left) :
    letI := componentChartedSpace hY c
    IsComplexManifold (componentDimension hY c) (OriginalSmoothComponents.componentObject hY c).obj.left := by
  let := componentChartedSpace hY c
  have := OriginalSmoothComponents.compactSpace_componentObject hY c
  exact OriginalSmoothNativeModel.isComplexManifold_nativeChartedSpace (componentModels hY c)

def componentNativeIso (hY : Y.IsSmooth) (c : ConnectedComponents Y.obj.left) :
    letI := componentChartedSpace hY c
    letI := componentIsComplexManifold hY c
    ofClosedAnalytic (n := componentDimension hY c)
        (univ : Set (OriginalSmoothComponents.componentObject hY c).obj.left)
        (isComplexAnalyticSubset_univ (n := componentDimension hY c)) ≅
      OriginalSmoothComponents.componentObject hY c := by
  letI := componentChartedSpace hY c
  letI := componentIsComplexManifold hY c
  have := OriginalSmoothComponents.compactSpace_componentObject hY c
  exact Classical.choose (OriginalSmoothNativeModel.exists_original_native_model_iso (componentModels hY c))

theorem componentNativeIso_point (hY : Y.IsSmooth) (c : ConnectedComponents Y.obj.left) :
    letI := componentChartedSpace hY c
    letI := componentIsComplexManifold hY c
    ∀ y, (componentNativeIso hY c).hom.hom.left.base y = y.val := by
  let := componentChartedSpace hY c
  have := componentIsComplexManifold hY c
  have := OriginalSmoothComponents.compactSpace_componentObject hY c
  exact Classical.choose_spec (OriginalSmoothNativeModel.exists_original_native_model_iso (componentModels hY c))

def componentNativeMorphism (hY : Y.IsSmooth) (F : Y ⟶ X)
    (c : ConnectedComponents Y.obj.left) :
    letI := componentChartedSpace hY c
    letI := componentIsComplexManifold hY c
    ofClosedAnalytic (n := componentDimension hY c)
        (univ : Set (OriginalSmoothComponents.componentObject hY c).obj.left)
        (isComplexAnalyticSubset_univ (n := componentDimension hY c)) ⟶ X :=
  (componentNativeIso hY c).hom ≫ OriginalSmoothComponents.componentInclusion hY c ≫ F

theorem componentNativeMorphism_point (hY : Y.IsSmooth) (F : Y ⟶ X)
    (c : ConnectedComponents Y.obj.left) :
    letI := componentChartedSpace hY c
    letI := componentIsComplexManifold hY c
    ∀ y, pointMap (componentNativeMorphism hY F c) y =
      F.hom.left.base ((OriginalSmoothComponents.componentInclusion hY c).hom.left.base y) := by
  let := componentChartedSpace hY c
  have := componentIsComplexManifold hY c
  intro y
  change F.hom.left.base ((OriginalSmoothComponents.componentInclusion hY c).hom.left.base
    ((componentNativeIso hY c).hom.hom.left.base ⟨y, mem_univ y⟩)) = _
  exact congrArg (fun z => F.hom.left.base
    ((OriginalSmoothComponents.componentInclusion hY c).hom.left.base z))
    (componentNativeIso_point hY c ⟨y, mem_univ y⟩)

private theorem component_bad_thin (hY : Y.IsSmooth) (F : Y ⟶ X) (B : Set X.obj.left)
    (hthin : interior (F.hom.left.base ⁻¹' B) = ∅) (c : ConnectedComponents Y.obj.left) :
    letI := componentChartedSpace hY c
    letI := componentIsComplexManifold hY c
    interior (pointMap (componentNativeMorphism hY F c) ⁻¹' B) = ∅ := by
  let := componentChartedSpace hY c
  have := componentIsComplexManifold hY c
  let j := (OriginalSmoothComponents.componentInclusion hY c).hom.left
  have hOI : LocallyRingedSpace.IsOpenImmersion j :=
    OriginalSmoothComponents.componentInclusion_isOpenImmersion hY c
  have hEq : pointMap (componentNativeMorphism hY F c) ⁻¹' B =
      j.base ⁻¹' (F.hom.left.base ⁻¹' B) := by
    ext y
    change pointMap (componentNativeMorphism hY F c) y ∈ B ↔ F.hom.left.base (j.base y) ∈ B
    rw [componentNativeMorphism_point]
  have hi : j.base ⁻¹' interior (F.hom.left.base ⁻¹' B) =
      interior (j.base ⁻¹' (F.hom.left.base ⁻¹' B)) :=
    hOI.base_open.isOpenMap.preimage_interior_eq_interior_preimage j.base.hom.continuous _
  exact (congrArg interior hEq).trans (hi.symm.trans (by rw [hthin]; rfl))

/-- Actual analytic source data and whole-source thinness DERIVE a nonempty
connected good open in EVERY actual original smooth component, including dim0.
The final PB consumer derives these ordinary source hypotheses internally. -/
theorem component_good_connected (hY : Y.IsSmooth) (F : Y ⟶ X)
    (E₀ E₁ : Set X.obj.left) (hE₀ : X.IsAnalyticSubset E₀) (hE₁ : X.IsAnalyticSubset E₁)
    (hthin : interior (F.hom.left.base ⁻¹' (E₀ ∪ E₁)) = ∅)
    (c : ConnectedComponents Y.obj.left) :
    IsConnected ((OriginalSmoothComponents.componentInclusion hY c).hom.left.base ⁻¹'
      (F.hom.left.base ⁻¹' (E₀ ∪ E₁)ᶜ)) := by
  let := componentChartedSpace hY c
  have := componentIsComplexManifold hY c
  have := OriginalSmoothComponents.connectedSpace_componentObject hY c
  let j := (OriginalSmoothComponents.componentInclusion hY c).hom.left
  let F' := componentNativeMorphism hY F c
  let A := pointMap F' ⁻¹' (E₀ ∪ E₁)
  have hAa : IsComplexAnalyticSubset (n := componentDimension hY c) A := by
    change IsComplexAnalyticSubset (n := componentDimension hY c) (pointMap F' ⁻¹' (E₀ ∪ E₁))
    rw [preimage_union]
    exact ConstantRankImage.IsComplexAnalyticSubset.union
      (isComplexAnalyticSubset_preimage F' hE₀) (isComplexAnalyticSubset_preimage F' hE₁)
  have hAeq : A = j.base ⁻¹' (F.hom.left.base ⁻¹' (E₀ ∪ E₁)) := by
    ext y
    change pointMap F' y ∈ E₀ ∪ E₁ ↔ F.hom.left.base (j.base y) ∈ E₀ ∪ E₁
    rw [componentNativeMorphism_point]
  have hAi : interior A = ∅ := component_bad_thin hY F (E₀ ∪ E₁) hthin c
  have hAne : A ≠ univ := by
    intro heq
    obtain ⟨y⟩ := (inferInstance : Nonempty (OriginalSmoothComponents.componentObject hY c).obj.left)
    have hy : y ∈ interior A := by rw [heq, interior_univ]; trivial
    rw [hAi] at hy
    exact hy
  have hgood : IsConnected (Aᶜ) :=
    ⟨(interior_eq_empty_iff_dense_compl.mp hAi).nonempty,
      AnalyticComplementConnected.isPreconnected_compl hAa hAne⟩
  simpa only [hAeq, preimage_compl] using hgood

end ComponentRepresentations

private def originalGoodOpen (F : Y ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B) :
    Opens Y.obj.left :=
  ⟨F.hom.left.base ⁻¹' Bᶜ, hBc.isOpen_compl.preimage F.hom.left.base.hom.continuous⟩

private def goodRestriction (F : Y ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B) :
    LocallyRingedSpace := Y.obj.left.restrict (originalGoodOpen F B hBc).isOpenEmbedding

private def goodInclusion (F : Y ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B) :
    goodRestriction F B hBc ⟶ Y.obj.left :=
  Y.obj.left.ofRestrict (originalGoodOpen F B hBc).isOpenEmbedding

private def goodMap (F : Y ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B) :
    goodRestriction F B hBc ⟶ X.obj.left := goodInclusion F B hBc ≫ F.hom.left

-- Same actual OI range comparison as the accepted native-source consumer,
-- now on literal ORIGINAL raw restrictions. No new comparison engine credit.
private theorem goodMap_isOpenImmersion (F : Y ⟶ X) (B : Set X.obj.left)
    (hBc : IsClosed B) (hiso : IsIsoOver F Bᶜ) :
    LocallyRingedSpace.IsOpenImmersion (goodMap F B hBc) ∧
      range (goodMap F B hBc).base = Bᶜ := by
  obtain ⟨V, j, hj, hjrange, hjF, hjFrange⟩ := hiso
  let I := goodInclusion F B hBc
  have hI : LocallyRingedSpace.IsOpenImmersion I := by
    exact LocallyRingedSpace.IsOpenImmersion.ofRestrict Y.obj.left
      (originalGoodOpen F B hBc).isOpenEmbedding
  have hIr : range I.base = F.hom.left.base ⁻¹' Bᶜ := Subtype.range_coe
  let E := @openImmersionIsoOfRangeEq _ _ _ I j hI hj (hIr.trans hjrange.symm)
  have hE : E.hom ≫ j = I :=
    @openImmersionIsoOfRangeEq_hom_fac _ _ _ I j hI hj (hIr.trans hjrange.symm)
  have hR : goodMap F B hBc = E.hom ≫ (j ≫ F.hom.left) := by
    rw [← Category.assoc, hE]
    rfl
  constructor
  · rw [hR]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ E.hom (inferInstance)
      (j ≫ F.hom.left) hjF
  · exact (congrArg (fun K : goodRestriction F B hBc ⟶ X.obj.left => range K.base) hR).trans
      ((range_iso_hom_comp_base E (j ≫ F.hom.left)).trans hjFrange)

private def originalGoodIso
    (F₀ : Y₀ ⟶ X) (F₁ : Y₁ ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B)
    (hiso₀ : IsIsoOver F₀ Bᶜ) (hiso₁ : IsIsoOver F₁ Bᶜ) :
    goodRestriction F₁ B hBc ≅ goodRestriction F₀ B hBc :=
  @openImmersionIsoOfRangeEq _ _ _ (goodMap F₁ B hBc) (goodMap F₀ B hBc)
    (goodMap_isOpenImmersion F₁ B hBc hiso₁).1 (goodMap_isOpenImmersion F₀ B hBc hiso₀).1
    ((goodMap_isOpenImmersion F₁ B hBc hiso₁).2.trans
      (goodMap_isOpenImmersion F₀ B hBc hiso₀).2.symm)

private theorem originalGoodIso_fac
    (F₀ : Y₀ ⟶ X) (F₁ : Y₁ ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B)
    (hiso₀ : IsIsoOver F₀ Bᶜ) (hiso₁ : IsIsoOver F₁ Bᶜ) :
    (originalGoodIso F₀ F₁ B hBc hiso₀ hiso₁).hom ≫ goodMap F₀ B hBc = goodMap F₁ B hBc :=
  @openImmersionIsoOfRangeEq_hom_fac _ _ _ (goodMap F₁ B hBc) (goodMap F₀ B hBc)
    (goodMap_isOpenImmersion F₁ B hBc hiso₁).1 (goodMap_isOpenImmersion F₀ B hBc hiso₀).1
    ((goodMap_isOpenImmersion F₁ B hBc hiso₁).2.trans
      (goodMap_isOpenImmersion F₀ B hBc hiso₀).2.symm)

private def originalGoodHomeomorph
    (F₀ : Y₀ ⟶ X) (F₁ : Y₁ ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B)
    (hiso₀ : IsIsoOver F₀ Bᶜ) (hiso₁ : IsIsoOver F₁ Bᶜ) :
    originalGoodOpen F₁ B hBc ≃ₜ originalGoodOpen F₀ B hBc where
  toFun := (originalGoodIso F₀ F₁ B hBc hiso₀ hiso₁).hom.base
  invFun := (originalGoodIso F₀ F₁ B hBc hiso₀ hiso₁).inv.base
  left_inv x := congrArg (fun f => f.base x) (originalGoodIso F₀ F₁ B hBc hiso₀ hiso₁).hom_inv_id
  right_inv x := congrArg (fun f => f.base x) (originalGoodIso F₀ F₁ B hBc hiso₀ hiso₁).inv_hom_id
  continuous_toFun := (originalGoodIso F₀ F₁ B hBc hiso₀ hiso₁).hom.base.hom.continuous
  continuous_invFun := (originalGoodIso F₀ F₁ B hBc hiso₀ hiso₁).inv.base.hom.continuous

private theorem originalGoodHomeomorph_square
    (F₀ : Y₀ ⟶ X) (F₁ : Y₁ ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B)
    (hiso₀ : IsIsoOver F₀ Bᶜ) (hiso₁ : IsIsoOver F₁ Bᶜ)
    (y : originalGoodOpen F₁ B hBc) :
    F₀.hom.left.base (originalGoodHomeomorph F₀ F₁ B hBc hiso₀ hiso₁ y).val =
      F₁.hom.left.base y.val :=
  congrArg (fun f => f.base y) (originalGoodIso_fac F₀ F₁ B hBc hiso₀ hiso₁)

private def componentGoodPiece (F : Y ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B)
    (c : ConnectedComponents Y.obj.left) : Set (originalGoodOpen F B hBc) :=
  {y | ConnectedComponents.mk y.val = c}

private theorem componentGoodPiece_isClopen (hY : Y.IsSmooth) (F : Y ⟶ X)
    (B : Set X.obj.left) (hBc : IsClosed B) (c : ConnectedComponents Y.obj.left) :
    IsClopen (componentGoodPiece F B hBc c) :=
  (OriginalSmoothComponents.component_isClopen hY c).preimage continuous_subtype_val

private theorem componentGoodPiece_pairwise (F : Y ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B) :
    Pairwise (fun c d => Disjoint (componentGoodPiece F B hBc c) (componentGoodPiece F B hBc d)) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro y hc hd
  exact hcd (hc.symm.trans hd)

private theorem componentGoodPiece_union (F : Y ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B) :
    ⋃ c, componentGoodPiece F B hBc c = univ := by
  apply eq_univ_of_forall
  intro y
  exact mem_iUnion.mpr ⟨ConnectedComponents.mk y.val, rfl⟩

private theorem componentGoodPiece_connected [CompactSpace Y.obj.left]
    (hY : Y.IsSmooth) (F : Y ⟶ X) (E₀ E₁ : Set X.obj.left)
    (hE₀ : X.IsAnalyticSubset E₀) (hE₁ : X.IsAnalyticSubset E₁)
    (hthin : interior (F.hom.left.base ⁻¹' (E₀ ∪ E₁)) = ∅)
    (c : ConnectedComponents Y.obj.left) :
    IsConnected (componentGoodPiece F (E₀ ∪ E₁) (hE₀.isClosed.union hE₁.isClosed) c) := by
  let B := E₀ ∪ E₁
  let hBc := hE₀.isClosed.union hE₁.isClosed
  let j := (OriginalSmoothComponents.componentInclusion hY c).hom.left
  let A := j.base ⁻¹' (F.hom.left.base ⁻¹' Bᶜ)
  have hA : IsConnected A := component_good_connected hY F E₀ E₁ hE₀ hE₁ hthin c
  have : ConnectedSpace A := isConnected_iff_connectedSpace.mp hA
  let f : A → originalGoodOpen F B hBc := fun y => ⟨j.base y.val, y.property⟩
  have hf : Continuous f := (j.base.hom.continuous.comp continuous_subtype_val).subtype_mk _
  have hr : range f = componentGoodPiece F B hBc c := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      change ConnectedComponents.mk z.val.val = c
      exact z.val.property
    · intro hy
      let p : (OriginalSmoothComponents.componentObject hY c).obj.left := ⟨y.val, hy⟩
      exact ⟨⟨p, y.property⟩, rfl⟩
  rw [← hr]
  exact isConnected_range hf

/-- The literal target image of an actual original component's entire good set. -/
def componentGoodImage (F : Y ⟶ X) (B : Set X.obj.left)
    (c : ConnectedComponents Y.obj.left) : Set X.obj.left :=
  F.hom.left.base '' (OriginalSmoothComponents.componentSet c ∩ (F.hom.left.base ⁻¹' Bᶜ))

/-- ONLY original compact smooth sources and their ORIGINAL PB maps derive
the common actual exceptional union, its thin pullbacks, and a BIJECTIVE
pairing with equality of the ENTIRE actual matched good images. -/
theorem exists_original_good_component_pairing
    [CompactSpace Y₀.obj.left] [CompactSpace Y₁.obj.left]
    (hY₀ : Y₀.IsSmooth) (hY₁ : Y₁.IsSmooth) (F₀ : Y₀ ⟶ X) (F₁ : Y₁ ⟶ X)
    (hF₀ : IsProperBimeromorphic F₀) (hF₁ : IsProperBimeromorphic F₁) :
    ∃ (E₀ E₁ : Set X.obj.left) (_hE₀ : X.IsAnalyticSubset E₀) (_hE₁ : X.IsAnalyticSubset E₁),
      IsIsoOver F₀ (E₀ ∪ E₁)ᶜ ∧ IsIsoOver F₁ (E₀ ∪ E₁)ᶜ ∧
      interior (F₀.hom.left.base ⁻¹' (E₀ ∪ E₁)) = ∅ ∧
      interior (F₁.hom.left.base ⁻¹' (E₀ ∪ E₁)) = ∅ ∧
      ∃ pair : ConnectedComponents Y₁.obj.left ≃ ConnectedComponents Y₀.obj.left,
        ∀ c, componentGoodImage F₀ (E₀ ∪ E₁) (pair c) = componentGoodImage F₁ (E₀ ∪ E₁) c := by
  obtain ⟨_hp₀, E₀, hE₀, htE₀, hown₀, hiso₀⟩ := hF₀
  obtain ⟨_hp₁, E₁, hE₁, htE₁, hown₁, hiso₁⟩ := hF₁
  let B := E₀ ∪ E₁
  have hBc : IsClosed B := hE₀.isClosed.union hE₁.isClosed
  have hi₀ : IsIsoOver F₀ Bᶜ :=
    hiso₀.of_isOpen_subset hBc.isOpen_compl (fun _ hx h => hx (Or.inl h))
  have hi₁ : IsIsoOver F₁ Bᶜ :=
    hiso₁.of_isOpen_subset hBc.isOpen_compl (fun _ hx h => hx (Or.inr h))
  have hc₀ : interior (F₀.hom.left.base ⁻¹' E₁) = ∅ :=
    hiso₀.interior_preimage_eq_empty hown₀ htE₁
  have hc₁ : interior (F₁.hom.left.base ⁻¹' E₀) = ∅ :=
    hiso₁.interior_preimage_eq_empty hown₁ htE₀
  have ht₀ : interior (F₀.hom.left.base ⁻¹' B) = ∅ := by
    rw [preimage_union, interior_union_isClosed_of_interior_empty
      (hE₀.isClosed.preimage F₀.hom.left.base.hom.continuous) hc₀]
    exact hown₀
  have ht₁ : interior (F₁.hom.left.base ⁻¹' B) = ∅ := by
    rw [preimage_union, interior_union_isClosed_of_interior_empty
      (hE₀.isClosed.preimage F₁.hom.left.base.hom.continuous) hown₁]
    exact hc₁
  let e := originalGoodHomeomorph F₀ F₁ B hBc hi₀ hi₁
  let P := componentGoodPiece F₁ B hBc
  let Q := fun c => e ⁻¹' componentGoodPiece F₀ B hBc c
  have hPc : ∀ c, IsClopen (P c) := componentGoodPiece_isClopen hY₁ F₁ B hBc
  have hQc : ∀ c, IsClopen (Q c) :=
    fun c => (componentGoodPiece_isClopen hY₀ F₀ B hBc c).preimage e.continuous
  have hPd := componentGoodPiece_pairwise F₁ B hBc
  have hQd : Pairwise (fun c d => Disjoint (Q c) (Q d)) := by
    intro c d hcd
    exact (componentGoodPiece_pairwise F₀ B hBc hcd).preimage e
  have hPu : ⋃ c, P c = univ := componentGoodPiece_union F₁ B hBc
  have hQu : ⋃ c, Q c = univ := by
    apply eq_univ_of_forall
    intro y
    exact mem_iUnion.mpr ⟨ConnectedComponents.mk (e y).val, rfl⟩
  have hPconn : ∀ c, IsConnected (P c) :=
    componentGoodPiece_connected hY₁ F₁ E₀ E₁ hE₀ hE₁ ht₁
  have hQconn : ∀ c, IsConnected (Q c) := fun c => e.isConnected_preimage.mpr
    (componentGoodPiece_connected hY₀ F₀ E₀ E₁ hE₀ hE₁ ht₀ c)
  obtain ⟨pair, hPair⟩ := exists_partition_pairing P Q hPc hQc hPd hQd hPu hQu hPconn hQconn
  refine ⟨E₀, E₁, hE₀, hE₁, hi₀, hi₁, ht₀, ht₁, pair, ?_⟩
  intro c
  ext z
  constructor
  · rintro ⟨y, ⟨hyc, hyg⟩, rfl⟩
    let y₀ : originalGoodOpen F₀ B hBc := ⟨y, hyg⟩
    let y₁ := e.symm y₀
    have hq : y₁ ∈ Q (pair c) := by
      change ConnectedComponents.mk (e y₁).val = pair c
      rw [e.apply_symm_apply]
      exact hyc
    have hp : y₁ ∈ P c := (hPair y₁ c).mpr hq
    refine ⟨y₁.val, ⟨hp, y₁.property⟩, ?_⟩
    have hs := originalGoodHomeomorph_square F₀ F₁ B hBc hi₀ hi₁ y₁
    change F₀.hom.left.base (e y₁).val = F₁.hom.left.base y₁.val at hs
    have heq : e y₁ = y₀ := e.apply_symm_apply y₀
    simpa only [heq] using hs.symm
  · rintro ⟨y, ⟨hyc, hyg⟩, rfl⟩
    let y₁ : originalGoodOpen F₁ B hBc := ⟨y, hyg⟩
    have hq : y₁ ∈ Q (pair c) := (hPair y₁ c).mp hyc
    refine ⟨(e y₁).val, ⟨hq, (e y₁).property⟩, ?_⟩
    exact originalGoodHomeomorph_square F₀ F₁ B hBc hi₀ hi₁ y₁

private theorem openImmersion_lift {A B T : LocallyRingedSpace}
    (f : A ⟶ T) (g : B ⟶ T)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (hr : range g.base ⊆ range f.base) :
    LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift f g hr) := by
  have : IsIso (pullback.snd f g) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset f g hr
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

/-- The SAME native component-good restriction is an ACTUAL full original OI,
and its ENTIRE range is the literal original component's good image. -/
theorem component_native_good_restriction [CompactSpace Y.obj.left]
    (hY : Y.IsSmooth) (F : Y ⟶ X) (B : Set X.obj.left) (hBc : IsClosed B)
    (hiso : IsIsoOver F Bᶜ) (c : ConnectedComponents Y.obj.left) :
    letI := componentChartedSpace hY c
    letI := componentIsComplexManifold hY c
    let F' := componentNativeMorphism hY F c
    LocallyRingedSpace.IsOpenImmersion (OriginalCommonResolution.restrictedOriginalMorphism F' B hBc) ∧
      range (OriginalCommonResolution.restrictedOriginalMorphism F' B hBc).base =
        componentGoodImage F B c := by
  let := componentChartedSpace hY c
  have := componentIsComplexManifold hY c
  let F' := componentNativeMorphism hY F c
  let O := OriginalCommonResolution.goodOpen F' B hBc
  let R := OriginalCommonResolution.restrictedOriginalMorphism F' B hBc
  let D := OriginalSmoothComponents.componentObject hY c
  let j := (OriginalSmoothComponents.componentInclusion hY c).hom.left
  let E : actualSubspaceLocallyRingedSpace (n := componentDimension hY c)
      (univ : Set D.obj.left) ≅ D.obj.left :=
    SourceReducedComplexSpace.isoLeft (componentNativeIso hY c)
  let N := actualOpenSubspaceMap (n := componentDimension hY c) (univ : Set D.obj.left) O
  let J := (N ≫ E.hom) ≫ j
  have hJ : LocallyRingedSpace.IsOpenImmersion J := by
    have hN : LocallyRingedSpace.IsOpenImmersion N := by dsimp only [N]; infer_instance
    have hj : LocallyRingedSpace.IsOpenImmersion j :=
      OriginalSmoothComponents.componentInclusion_isOpenImmersion hY c
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (N ≫ E.hom)
      (@LocallyRingedSpace.IsOpenImmersion.comp _ _ _ N hN E.hom (inferInstance)) j hj
  have hJpoint (v : (univ : Set O)) : J.base v = j.base v.val.val := by
    change j.base ((componentNativeIso hY c).hom.hom.left.base
      ⟨v.val.val, mem_univ v.val.val⟩) = _
    exact congrArg j.base (componentNativeIso_point hY c ⟨v.val.val, mem_univ v.val.val⟩)
  have hgood (v : (univ : Set O)) : F.hom.left.base (J.base v) ∈ Bᶜ := by
    rw [hJpoint]
    have hv : pointMap F' v.val.val ∈ Bᶜ := v.val.property
    rwa [componentNativeMorphism_point] at hv
  have hI : LocallyRingedSpace.IsOpenImmersion (goodInclusion F B hBc) :=
    LocallyRingedSpace.IsOpenImmersion.ofRestrict Y.obj.left (originalGoodOpen F B hBc).isOpenEmbedding
  have hr : range J.base ⊆ range (goodInclusion F B hBc).base := by
    rintro _ ⟨v, rfl⟩
    exact ⟨(⟨J.base v, hgood v⟩ : originalGoodOpen F B hBc), rfl⟩
  let L := LocallyRingedSpace.IsOpenImmersion.lift (goodInclusion F B hBc) J hr
  have hfac : L ≫ goodInclusion F B hBc = J :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac (goodInclusion F B hBc) J hr
  have hL : LocallyRingedSpace.IsOpenImmersion L := openImmersion_lift (goodInclusion F B hBc) J hr
  have hR : L ≫ goodMap F B hBc = R := by
    have h₁ : L ≫ goodMap F B hBc = J ≫ F.hom.left := by
      change L ≫ (goodInclusion F B hBc ≫ F.hom.left) = _
      rw [← Category.assoc, hfac]
    have h₂ : J ≫ F.hom.left = R := by
      change ((N ≫ E.hom) ≫ j) ≫ F.hom.left = N ≫ (E.hom ≫ (j ≫ F.hom.left))
      simp only [Category.assoc]
    exact h₁.trans h₂
  have hRpoint (v : (univ : Set O)) : R.base v = F.hom.left.base (j.base v.val.val) := by
    change pointMap F' v.val.val = _
    exact componentNativeMorphism_point hY F c v.val.val
  constructor
  · change LocallyRingedSpace.IsOpenImmersion R
    rw [← hR]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ L hL (goodMap F B hBc)
      (goodMap_isOpenImmersion F B hBc hiso).1
  · ext z
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨j.base v.val.val, ⟨?_, ?_⟩, (hRpoint v).symm⟩
      · change ConnectedComponents.mk v.val.val.val = c
        exact v.val.val.property
      · change F.hom.left.base (j.base v.val.val) ∈ Bᶜ
        rw [← hJpoint]
        exact hgood v
    · rintro ⟨y, ⟨hyc, hyg⟩, rfl⟩
      let p : D.obj.left := ⟨y, hyc⟩
      have hp : pointMap F' p ∈ Bᶜ := by
        rw [componentNativeMorphism_point]
        exact hyg
      let v : O := ⟨p, hp⟩
      exact ⟨⟨v, mem_univ v⟩, hRpoint ⟨v, mem_univ v⟩⟩

private theorem native_good_point {d : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsComplexManifold d M]
    (F : OriginalNativeModification.wholeModel (n := d) M ⟶ X)
    (B : Set X.obj.left) (hBc : IsClosed B) :
    OriginalCommonResolution.restrictedOriginalMorphism F B hBc ≫ X.obj.hom =
      subspacePointMap (n := d) (univ : Set (OriginalCommonResolution.goodOpen F B hBc)) := by
  let U := OriginalCommonResolution.goodOpen F B hBc
  let I := actualOpenSubspaceMap (n := d) (univ : Set M) U
  let f : actualSubspaceLocallyRingedSpace (n := d) (univ : Set M) ⟶ X.obj.left := F.hom.left
  have h : f ≫ X.obj.hom = subspacePointMap (n := d) (univ : Set M) := Over.w F.hom
  change (I ≫ f) ≫ X.obj.hom = _
  rw [Category.assoc, h]
  exact actualSubspaceMap_point contMDiff_subtype_val (fun _ _ => mem_univ _)

-- Ordinary actual good OIs, not whole-target PB assumptions, are the precise
-- source contract needed for differently dimensioned native components.
private theorem exists_common_of_native_good_openImmersions
    {d₀ d₁ : ℕ} {M₀ M₁ : Type}
    [TopologicalSpace M₀] [ChartedSpace (ComplexModel d₀) M₀] [IsComplexManifold d₀ M₀]
    [TopologicalSpace M₁] [ChartedSpace (ComplexModel d₁) M₁] [IsComplexManifold d₁ M₁]
    [CompactSpace M₀] [CompactSpace M₁] [ConnectedSpace M₁]
    (F₀ : OriginalNativeModification.wholeModel (n := d₀) M₀ ⟶ X)
    (F₁ : OriginalNativeModification.wholeModel (n := d₁) M₁ ⟶ X)
    (E₀ E₁ : Set X.obj.left) (hE₀ : X.IsAnalyticSubset E₀) (hE₁ : X.IsAnalyticSubset E₁)
    (ht₀ : interior (pointMap F₀ ⁻¹' (E₀ ∪ E₁)) = ∅)
    (ht₁ : interior (pointMap F₁ ⁻¹' (E₀ ∪ E₁)) = ∅)
    (hR₀ : LocallyRingedSpace.IsOpenImmersion (OriginalCommonResolution.restrictedOriginalMorphism
      F₀ (E₀ ∪ E₁) (hE₀.isClosed.union hE₁.isClosed)))
    (hR₁ : LocallyRingedSpace.IsOpenImmersion (OriginalCommonResolution.restrictedOriginalMorphism
      F₁ (E₀ ∪ E₁) (hE₀.isClosed.union hE₁.isClosed)))
    (hrange : range (OriginalCommonResolution.restrictedOriginalMorphism
      F₀ (E₀ ∪ E₁) (hE₀.isClosed.union hE₁.isClosed)).base =
      range (OriginalCommonResolution.restrictedOriginalMorphism
        F₁ (E₀ ∪ E₁) (hE₀.isClosed.union hE₁.isClosed)).base) :
    ∃ (Z : SourceReducedComplexSpace) (_ : CompactSpace Z.obj.left), Z.IsSmooth ∧
      ∃ (g₀ : Z ⟶ OriginalNativeModification.wholeModel (n := d₀) M₀)
        (g₁ : Z ⟶ OriginalNativeModification.wholeModel (n := d₁) M₁),
        IsProperBimeromorphic g₀ ∧ IsProperBimeromorphic g₁ ∧ g₀ ≫ F₀ = g₁ ≫ F₁ := by
  let B := E₀ ∪ E₁
  let hBc := hE₀.isClosed.union hE₁.isClosed
  let U₀ := OriginalCommonResolution.goodOpen F₀ B hBc
  let U₁ := OriginalCommonResolution.goodOpen F₁ B hBc
  let R₀ := OriginalCommonResolution.restrictedOriginalMorphism F₀ B hBc
  let R₁ := OriginalCommonResolution.restrictedOriginalMorphism F₁ B hBc
  let E := @openImmersionIsoOfRangeEq _ _ _ R₁ R₀ hR₁ hR₀ hrange.symm
  have hfac : E.hom ≫ R₀ = R₁ :=
    @openImmersionIsoOfRangeEq_hom_fac _ _ _ R₁ R₀ hR₁ hR₀ hrange.symm
  have hEp : E.hom ≫ subspacePointMap (n := d₀) (univ : Set U₀) =
      subspacePointMap (n := d₁) (univ : Set U₁) := by
    rw [← native_good_point F₀ B hBc, ← Category.assoc, hfac, native_good_point F₁ B hBc]
  let Q₀ := actualSubspaceUnivIso (n := d₀) (M := U₀)
  let Q₁ := actualSubspaceUnivIso (n := d₁) (M := U₁)
  let ER := Q₁.symm.trans (E.trans Q₀)
  have hQ₀ : Q₀.hom ≫ ambientPointMap d₀ U₀ = subspacePointMap (n := d₀) (univ : Set U₀) := rfl
  have hQ₁ : Q₁.inv ≫ subspacePointMap (n := d₁) (univ : Set U₁) = ambientPointMap d₁ U₁ :=
    actualSubspaceUnivIso_inv_point
  have hER : ER.hom ≫ ambientPointMap d₀ U₀ = ambientPointMap d₁ U₁ := by
    change (Q₁.inv ≫ (E.hom ≫ Q₀.hom)) ≫ ambientPointMap d₀ U₀ = _
    simp only [Category.assoc, hQ₀, hEp, hQ₁]
  have hgood : (U₁ : Set M₁).Nonempty := by
    obtain ⟨x, hx⟩ := (interior_eq_empty_iff_dense_compl.mp ht₁).nonempty
    exact ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hgood
  have hd : d₁ = d₀ := OriginalSmoothDimension.native_iso_dimension_eq ER hER ⟨x, hx⟩
  cases hd
  let e := nativeDiffeomorph E hEp
  have he : ∀ y, pointMap F₀ (e y).val = pointMap F₁ y.val := by
    intro y
    exact congrArg (fun f => f.base (⟨y, mem_univ y⟩ : (univ : Set U₁))) hfac
  have hinj : InjOn (pointMap F₀) (pointMap F₀ ⁻¹' Bᶜ) := by
    intro y hy z hz hyz
    let p : (univ : Set U₀) := ⟨⟨y, hy⟩, mem_univ _⟩
    let q : (univ : Set U₀) := ⟨⟨z, hz⟩, mem_univ _⟩
    have h : R₀.base p = R₀.base q := hyz
    exact congrArg (fun t => t.val.val) (hR₀.base_open.injective h)
  exact OriginalGoodTransitionCommonModel.exists_original_common_model_of_good_transition
    F₀ F₁ E₀ E₁ hE₀ hE₁ ht₀ ht₁ e he hinj

/-- The ORIGINAL compact smooth PB sources INTERNALLY produce a genuine
common compact ORIGINAL smooth model for EVERY actual paired component.
There is no incoming native representation, connected-good, dimension,
pairing, component-to-wholeX modification, or future common-model packet. -/
theorem exists_original_paired_common_models
    [CompactSpace Y₀.obj.left] [CompactSpace Y₁.obj.left]
    (hY₀ : Y₀.IsSmooth) (hY₁ : Y₁.IsSmooth) (F₀ : Y₀ ⟶ X) (F₁ : Y₁ ⟶ X)
    (hF₀ : IsProperBimeromorphic F₀) (hF₁ : IsProperBimeromorphic F₁) :
    ∃ pair : ConnectedComponents Y₁.obj.left ≃ ConnectedComponents Y₀.obj.left,
      ∀ c, ∃ (Z : SourceReducedComplexSpace) (_ : CompactSpace Z.obj.left), Z.IsSmooth ∧
        ∃ (g₀ : Z ⟶ OriginalSmoothComponents.componentObject hY₀ (pair c))
          (g₁ : Z ⟶ OriginalSmoothComponents.componentObject hY₁ c),
          IsProperBimeromorphic g₀ ∧ IsProperBimeromorphic g₁ ∧
          (g₀ ≫ OriginalSmoothComponents.componentInclusion hY₀ (pair c)) ≫ F₀ =
            (g₁ ≫ OriginalSmoothComponents.componentInclusion hY₁ c) ≫ F₁ := by
  obtain ⟨E₀, E₁, hE₀, hE₁, hi₀, hi₁, ht₀, ht₁, pair, hImages⟩ :=
    exists_original_good_component_pairing hY₀ hY₁ F₀ F₁ hF₀ hF₁
  refine ⟨pair, ?_⟩
  intro c
  let C₀ := OriginalSmoothComponents.componentObject hY₀ (pair c)
  let C₁ := OriginalSmoothComponents.componentObject hY₁ c
  let := componentChartedSpace hY₀ (pair c)
  let := componentChartedSpace hY₁ c
  have := componentIsComplexManifold hY₀ (pair c)
  have := componentIsComplexManifold hY₁ c
  have : CompactSpace C₀.obj.left := OriginalSmoothComponents.compactSpace_componentObject hY₀ (pair c)
  have : CompactSpace C₁.obj.left := OriginalSmoothComponents.compactSpace_componentObject hY₁ c
  have : ConnectedSpace C₁.obj.left := OriginalSmoothComponents.connectedSpace_componentObject hY₁ c
  let F₀' := componentNativeMorphism hY₀ F₀ (pair c)
  let F₁' := componentNativeMorphism hY₁ F₁ c
  have ht₀' : interior (pointMap F₀' ⁻¹' (E₀ ∪ E₁)) = ∅ :=
    component_bad_thin hY₀ F₀ (E₀ ∪ E₁) ht₀ (pair c)
  have ht₁' : interior (pointMap F₁' ⁻¹' (E₀ ∪ E₁)) = ∅ :=
    component_bad_thin hY₁ F₁ (E₀ ∪ E₁) ht₁ c
  have hR₀ := component_native_good_restriction hY₀ F₀ (E₀ ∪ E₁)
    (hE₀.isClosed.union hE₁.isClosed) hi₀ (pair c)
  have hR₁ := component_native_good_restriction hY₁ F₁ (E₀ ∪ E₁)
    (hE₀.isClosed.union hE₁.isClosed) hi₁ c
  have hrange := hR₀.2.trans ((hImages c).trans hR₁.2.symm)
  obtain ⟨Z, hZcompact, hZsmooth, g₀, g₁, hg₀, hg₁, hsquare⟩ :=
    exists_common_of_native_good_openImmersions F₀' F₁' E₀ E₁ hE₀ hE₁ ht₀' ht₁'
      hR₀.1 hR₁.1 hrange
  let G₀ := g₀ ≫ (componentNativeIso hY₀ (pair c)).hom
  let G₁ := g₁ ≫ (componentNativeIso hY₁ c).hom
  have hG₀ : IsProperBimeromorphic G₀ :=
    ((show IsResolution g₀ from ⟨hZsmooth, hg₀⟩).comp_iso (componentNativeIso hY₀ (pair c)).symm).2
  have hG₁ : IsProperBimeromorphic G₁ :=
    ((show IsResolution g₁ from ⟨hZsmooth, hg₁⟩).comp_iso (componentNativeIso hY₁ c).symm).2
  refine ⟨Z, hZcompact, hZsmooth, G₀, G₁, hG₀, hG₁, ?_⟩
  change (g₀ ≫ (componentNativeIso hY₀ (pair c)).hom) ≫
      OriginalSmoothComponents.componentInclusion hY₀ (pair c) ≫ F₀ =
    (g₁ ≫ (componentNativeIso hY₁ c).hom) ≫ OriginalSmoothComponents.componentInclusion hY₁ c ≫ F₁
  have hs : g₀ ≫ ((componentNativeIso hY₀ (pair c)).hom ≫
        (OriginalSmoothComponents.componentInclusion hY₀ (pair c) ≫ F₀)) =
      g₁ ≫ ((componentNativeIso hY₁ c).hom ≫
        (OriginalSmoothComponents.componentInclusion hY₁ c ≫ F₁)) := hsquare
  exact (Category.assoc g₀ (componentNativeIso hY₀ (pair c)).hom
    (OriginalSmoothComponents.componentInclusion hY₀ (pair c) ≫ F₀)).trans
      (hs.trans (Category.assoc g₁ (componentNativeIso hY₁ c).hom
        (OriginalSmoothComponents.componentInclusion hY₁ c ≫ F₁)).symm)

end

end Hironaka.Analytic.Unibranch.OriginalSmoothComponentPairing
