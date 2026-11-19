import Hironaka.Analytic.Unibranch.OriginalCommonResolution
import Hironaka.Analytic.Unibranch.OriginalNativeModification

/-! ORIGINAL proper-bimeromorphic whole-model morphisms derive genuine
native analytic modifications, with the SAME full original morphism.
Blueprint FIRST: `original-proper-bimeromorphic-native.tex`. -/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalProperBimeromorphicNative

open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaEmbeddedNativeMorphism HironakaResolutionSpaceComplex
  AnalyticModificationLocalDiscrepancy SourceReducedComplexSpace
  OriginalNativeModification OriginalSmoothSourceAnalytic

noncomputable section

-- Native homeomorphism transfer, generic reuse with no separate credit.
private theorem thin_whole_parametrization {T : Type} [TopologicalSpace T]
    {S : Set (univ : Set T)} (hS : interior S = ∅) :
    interior ((Homeomorph.Set.univ T).symm ⁻¹' S) = ∅ := by
  rw [← (Homeomorph.Set.univ T).symm.preimage_interior, hS, preimage_empty]

variable {n m : ℕ} {M N : Type}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace N] [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

/-- The literal native function of the ORIGINAL whole-model morphism. -/
def nativePointMap (F : wholeModel (n := n) M ⟶ wholeModel (n := m) N) : M → N :=
  fun x => (F.hom.left.base ⟨x, mem_univ x⟩).val

/-- Original scalar compatibility DERIVES holomorphy of the same native map. -/
theorem nativePointMap_contMDiff
    (F : wholeModel (n := n) M ⟶ wholeModel (n := m) N) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ (nativePointMap F) :=
  contMDiff_original_pointMap F.hom.left (Over.w F.hom)

/-- The native function recovers the ENTIRE original quotient-sheaf morphism. -/
theorem nativeMorphism_nativePointMap
    (F : wholeModel (n := n) M ⟶ wholeModel (n := m) N) :
    nativeMorphism (nativePointMap_contMDiff F) = F :=
  SourceReducedComplexSpace.morphism_eq_of_pointwise_eq _ _ (fun _ => rfl)

section SameDimension

variable {P : Type} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P]
  [IsComplexManifold n P]

/-- ORIGINAL proper-bimeromorphic geometry derives the native modification
predicate; no native modification or good inverse is supplied. -/
theorem isAnalyticModification_of_isProperBimeromorphic
    (F : wholeModel (n := n) M ⟶ wholeModel (n := n) P)
    (hF : IsProperBimeromorphic F) :
    IsAnalyticModification (n := n) (nativePointMap F) := by
  classical
  obtain ⟨hproper, E, hEa, hEt, hpre, hiso⟩ := hF
  let f := nativePointMap F
  have hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f :=
    nativePointMap_contMDiff F
  let B : Set P := fun x => (⟨x, mem_univ x⟩ : (univ : Set P)) ∈ E
  let A : Set M := f ⁻¹' B
  have hBa : IsComplexAnalyticSubset (n := n) B :=
    isComplexAnalyticSubset_preimage (𝟙 (wholeModel (n := n) P)) hEa
  have hAa : IsComplexAnalyticSubset (n := n) A :=
    isComplexAnalyticSubset_preimage F hEa
  have hBt : interior B = ∅ := by
    exact thin_whole_parametrization hEt
  have hAt : interior A = ∅ := by
    exact thin_whole_parametrization hpre
  have hproperf : IsProperMap f :=
    (Homeomorph.Set.univ P).isProperMap.comp
      (hproper.comp (Homeomorph.Set.univ M).symm.isProperMap)
  let U := OriginalCommonResolution.goodOpen F E hEa.isClosed
  let V : Opens P := ⟨Bᶜ, hBa.isClosed.isOpen_compl⟩
  let R := OriginalCommonResolution.restrictedOriginalMorphism F E hEa.isClosed
  let K := actualOpenSubspaceMap (n := n) (univ : Set P) V
  obtain ⟨hR, hRrange⟩ :=
    OriginalCommonResolution.original_restriction_of_isIsoOver F E hEa.isClosed hiso
  have hK : LocallyRingedSpace.IsOpenImmersion K := by
    dsimp only [K]
    infer_instance
  have hKrange : range K.base = Eᶜ := by
    rw [range_actualOpenSubspaceMap]
    ext x
    rfl
  let D := @openImmersionIsoOfRangeEq _ _ _ R K hR hK (hRrange.trans hKrange.symm)
  have hfac : D.hom ≫ K = R :=
    @openImmersionIsoOfRangeEq_hom_fac _ _ _ R K hR hK (hRrange.trans hKrange.symm)
  have hKp : K ≫ subspacePointMap (n := n) (univ : Set P) =
      subspacePointMap (n := n) (univ : Set V) :=
    actualSubspaceMap_point contMDiff_subtype_val (fun _ _ => mem_univ _)
  have hRp : R ≫ subspacePointMap (n := n) (univ : Set P) =
      subspacePointMap (n := n) (univ : Set U) :=
    Over.w ((nativeMorphism (M := U) (N := M) contMDiff_subtype_val) ≫ F).hom
  have hDp : D.hom ≫ subspacePointMap (n := n) (univ : Set V) =
      subspacePointMap (n := n) (univ : Set U) := by
    rw [← hKp, ← Category.assoc, hfac]
    exact hRp
  let e := nativeDiffeomorph D hDp
  have he (y : U) : (e y).val = f y.val :=
    congrArg (fun H => (H.base (⟨y, mem_univ y⟩ : (univ : Set U))).val) hfac
  have hnonempty (x : P) : Nonempty M := by
    obtain ⟨z, hz⟩ := (interior_eq_empty_iff_dense_compl.mp hBt).nonempty_iff.mpr ⟨x⟩
    exact ⟨(e.symm (⟨z, hz⟩ : V)).val⟩
  let s₀ : V → M := fun x => (e.symm x).val
  have hs₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s₀ :=
    contMDiff_subtype_val.comp e.symm.contMDiff
  let s : P → M := fun x => if hx : x ∈ Bᶜ then s₀ ⟨x, hx⟩ else
    Classical.choice (hnonempty x)
  have hsrest : (fun x : V => s x.val) = s₀ := by
    funext x
    exact dif_pos x.property
  have hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ := by
    have hrest : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (fun x : V => s x.val) := hsrest ▸ hs₀
    intro x hx
    exact (contMDiffAt_subtype_iff.mp (hrest ⟨x, hx⟩)).contMDiffWithinAt
  refine ⟨hf, hproperf, A, B, s, hAa.isClosed, hAa, hAt, hBa.isClosed, hBa, hBt,
    rfl, hs, ?_, ?_⟩
  · intro x hx
    rw [show s x = s₀ ⟨x, hx⟩ from dif_pos hx]
    exact (he (e.symm ⟨x, hx⟩)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩))
  · intro y hy
    have hyB : f y ∈ Bᶜ := hy
    rw [show s (f y) = s₀ ⟨f y, hyB⟩ from dif_pos hyB]
    let q : U := ⟨y, hyB⟩
    have hq : e q = (⟨f y, hyB⟩ : V) := Subtype.ext (he q)
    change (e.symm ⟨f y, hyB⟩).val = y
    rw [← hq, e.symm_apply_apply]

end SameDimension

end

end Hironaka.Analytic.Unibranch.OriginalProperBimeromorphicNative
