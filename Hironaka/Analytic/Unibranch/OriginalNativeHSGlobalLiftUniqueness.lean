import Hironaka.Analytic.Unibranch.OriginalNativeHSGlobalStrongResolution
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothSingularLocus
import Hironaka.Analytic.Unibranch.HironakaG11LiftUniqueness
import Hironaka.Analytic.Unibranch.SourceMorphismExt

/-! Concrete ANY-native-map uniqueness on the ACTUAL global assignments and
actual prescribed atlas sources; real lift identity/composition laws.
Blueprint FIRST: original-native-hs-global-lift-uniqueness.tex.
No supplied density/resolution/future-lift or global finite-clock packet. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSGlobalLiftUniqueness
noncomputable section
open Hironaka HironakaIntrinsicComplexAnalyticRegularLocus
  SourceReducedComplexSpace OriginalNativeSmoothLocalProduct

private theorem eq_of_dense_reg {A B C D : SourceReducedComplexSpace} (q : A ⟶ B) (p : C ⟶ D)
    (hDense : Dense (q.hom.left.base ⁻¹' intrinsicRegularLocus B.obj))
    (hReg : IsIsoOver p (intrinsicRegularLocus D.obj))
    (f : B ⟶ D) (hf : IsSmoothMorphism f) (a b : A ⟶ C)
    (ha : a ≫ p = q ≫ f) (hb : b ≫ p = q ≫ f) : a = b := by
  have hBase : ∀ z, p.hom.left.base (a.hom.left.base z) = p.hom.left.base (b.hom.left.base z) := by
    intro z
    exact (congrArg (fun t => t.hom.left.base z) ha).trans (congrArg (fun t => t.hom.left.base z) hb).symm
  have hGood : ∀ z ∈ q.hom.left.base ⁻¹' intrinsicRegularLocus B.obj,
      p.hom.left.base (a.hom.left.base z) ∈ intrinsicRegularLocus D.obj := by
    intro z hz
    have hs := congrArg (fun t => t.hom.left.base z) ha
    change p.hom.left.base (a.hom.left.base z) = f.hom.left.base (q.hom.left.base z) at hs
    rw [hs]
    exact (OriginalNativeSmoothSingularLocus.smoothAt_regular_iff f (q.hom.left.base z) (hf _)).mp hz
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  exact congrFun (HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense hReg
    a.hom.left.base.hom.continuous b.hom.left.base.hom.continuous hBase hDense hGood) z

variable (X Y : SourceReducedComplexSpace) (f : X ⟶ Y) (hf : IsSmoothMorphism f)

include hf in
theorem raw_maps_eq (a b : OriginalNativeHSGlobalResolution.source X ⟶ OriginalNativeHSGlobalResolution.source Y)
    (ha : a ≫ OriginalNativeHSGlobalResolution.projection Y = OriginalNativeHSGlobalResolution.projection X ≫ f)
    (hb : b ≫ OriginalNativeHSGlobalResolution.projection Y = OriginalNativeHSGlobalResolution.projection X ≫ f) : a = b :=
  eq_of_dense_reg (OriginalNativeHSGlobalResolution.projection X) (OriginalNativeHSGlobalResolution.projection Y)
    (OriginalNativeHSGlobalResolution.dense_originalReg X) (OriginalNativeHSGlobalResolution.originalReg Y) f hf a b ha hb

-- Actual prescribed-history sources, including pair/triple atlas intersections.
include hf in
theorem prescribed_maps_eq (i k : OriginalNativeHSResolutionAtlasChoice.Index X)
    (hki : OriginalNativeHSResolutionAtlasChoice.openSet k ≤ OriginalNativeHSResolutionAtlasChoice.openSet i)
    (a b : OriginalNativeHSResolutionAtlasOverlap.sourceOn i k hki ⟶ OriginalNativeHSGlobalResolution.source Y)
    (ha : a ≫ OriginalNativeHSGlobalResolution.projection Y =
      OriginalNativeHSResolutionAtlasOverlap.projectionOn i k hki ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion k ≫ f)
    (hb : b ≫ OriginalNativeHSGlobalResolution.projection Y =
      OriginalNativeHSResolutionAtlasOverlap.projectionOn i k hki ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion k ≫ f) : a = b :=
  eq_of_dense_reg (OriginalNativeHSResolutionAtlasOverlap.projectionOn i k hki)
    (OriginalNativeHSGlobalResolution.projection Y)
    (OriginalNativeHSResolutionAtlasOverlap.historyOn i k hki).singularModification.dense_preimage_intrinsicRegularLocus
    (OriginalNativeHSGlobalResolution.originalReg Y) (OriginalNativeHSResolutionAtlasChoice.baseInclusion k ≫ f)
    (OriginalNativeSmoothComposition.isSmoothMorphism_comp (OriginalNativeHSResolutionAtlasChoice.baseInclusion k) f
      (isSmoothMorphism_of_isOpenImmersion _ (OriginalNativeHSResolutionAtlasChoice.baseInclusion_isOpenImmersion k)) hf)
    a b ha hb

private theorem compose_square {A B C D E F : SourceReducedComplexSpace}
    (a : A ⟶ B) (b : B ⟶ C) (p : A ⟶ D) (q : B ⟶ E) (r : C ⟶ F)
    (f : D ⟶ E) (g : E ⟶ F) (ha : a ≫ q = p ≫ f) (hb : b ≫ r = q ≫ g) :
    (a ≫ b) ≫ r = p ≫ (f ≫ g) := by
  calc
    _ = a ≫ (b ≫ r) := Category.assoc _ _ _
    _ = a ≫ (q ≫ g) := congrArg (fun t => a ≫ t) hb
    _ = (a ≫ q) ≫ g := (Category.assoc _ _ _).symm
    _ = (p ≫ f) ≫ g := congrArg (fun t => t ≫ g) ha
    _ = _ := Category.assoc _ _ _

theorem raw_identity (a : OriginalNativeHSGlobalResolution.source X ⟶ OriginalNativeHSGlobalResolution.source X)
    (ha : a ≫ OriginalNativeHSGlobalResolution.projection X = OriginalNativeHSGlobalResolution.projection X) : a = 𝟙 _ := by
  apply raw_maps_eq X X (𝟙 X) (isSmoothMorphism_identity X) a (𝟙 _)
  · simpa only [Category.comp_id] using ha
  · simp only [Category.id_comp,Category.comp_id]

include hf in
theorem raw_composition (Z : SourceReducedComplexSpace) (g : Y ⟶ Z) (hg : IsSmoothMorphism g)
    (a : OriginalNativeHSGlobalResolution.source X ⟶ OriginalNativeHSGlobalResolution.source Y)
    (b : OriginalNativeHSGlobalResolution.source Y ⟶ OriginalNativeHSGlobalResolution.source Z)
    (c : OriginalNativeHSGlobalResolution.source X ⟶ OriginalNativeHSGlobalResolution.source Z)
    (ha : a ≫ OriginalNativeHSGlobalResolution.projection Y = OriginalNativeHSGlobalResolution.projection X ≫ f)
    (hb : b ≫ OriginalNativeHSGlobalResolution.projection Z = OriginalNativeHSGlobalResolution.projection Y ≫ g)
    (hc : c ≫ OriginalNativeHSGlobalResolution.projection Z = OriginalNativeHSGlobalResolution.projection X ≫ (f ≫ g)) :
    a ≫ b = c :=
  raw_maps_eq X Z (f ≫ g) (OriginalNativeSmoothComposition.isSmoothMorphism_comp f g hf hg) (a ≫ b) c
    (compose_square a b _ _ _ f g ha hb) hc

theorem strong_dense_originalReg : Dense
    ((OriginalNativeHSGlobalStrongResolution.projection X).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) := by
  have ht : interior ((OriginalNativeHSGlobalStrongResolution.projection X).hom.left.base ⁻¹'
      intrinsicSingularLocus X.obj) = ∅ := by
    obtain ⟨_hp,E,_hEa,_hEt,hpre,hiso⟩ := (OriginalNativeHSGlobalStrongResolution.resolution X).2
    exact hiso.interior_preimage_eq_empty hpre
      (OriginalIntrinsicSingularLocus.interior_intrinsicSingularLocus_eq_empty X)
  rw [intrinsicSingularLocus,preimage_compl,interior_eq_empty_iff_dense_compl,compl_compl] at ht
  exact ht

include hf in
theorem strong_maps_eq (a b : OriginalNativeHSGlobalStrongResolution.source X ⟶ OriginalNativeHSGlobalStrongResolution.source Y)
    (ha : a ≫ OriginalNativeHSGlobalStrongResolution.projection Y = OriginalNativeHSGlobalStrongResolution.projection X ≫ f)
    (hb : b ≫ OriginalNativeHSGlobalStrongResolution.projection Y = OriginalNativeHSGlobalStrongResolution.projection X ≫ f) : a = b :=
  eq_of_dense_reg (OriginalNativeHSGlobalStrongResolution.projection X) (OriginalNativeHSGlobalStrongResolution.projection Y)
    (strong_dense_originalReg X) (OriginalNativeHSGlobalStrongResolution.originalReg Y) f hf a b ha hb

theorem strong_identity (a : OriginalNativeHSGlobalStrongResolution.source X ⟶ OriginalNativeHSGlobalStrongResolution.source X)
    (ha : a ≫ OriginalNativeHSGlobalStrongResolution.projection X = OriginalNativeHSGlobalStrongResolution.projection X) : a = 𝟙 _ := by
  apply strong_maps_eq X X (𝟙 X) (isSmoothMorphism_identity X) a (𝟙 _)
  · simpa only [Category.comp_id] using ha
  · simp only [Category.id_comp,Category.comp_id]

include hf in
theorem strong_composition (Z : SourceReducedComplexSpace) (g : Y ⟶ Z) (hg : IsSmoothMorphism g)
    (a : OriginalNativeHSGlobalStrongResolution.source X ⟶ OriginalNativeHSGlobalStrongResolution.source Y)
    (b : OriginalNativeHSGlobalStrongResolution.source Y ⟶ OriginalNativeHSGlobalStrongResolution.source Z)
    (c : OriginalNativeHSGlobalStrongResolution.source X ⟶ OriginalNativeHSGlobalStrongResolution.source Z)
    (ha : a ≫ OriginalNativeHSGlobalStrongResolution.projection Y = OriginalNativeHSGlobalStrongResolution.projection X ≫ f)
    (hb : b ≫ OriginalNativeHSGlobalStrongResolution.projection Z = OriginalNativeHSGlobalStrongResolution.projection Y ≫ g)
    (hc : c ≫ OriginalNativeHSGlobalStrongResolution.projection Z = OriginalNativeHSGlobalStrongResolution.projection X ≫ (f ≫ g)) :
    a ≫ b = c :=
  strong_maps_eq X Z (f ≫ g) (OriginalNativeSmoothComposition.isSmoothMorphism_comp f g hf hg) (a ≫ b) c
    (compose_square a b _ _ _ f g ha hb) hc

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSGlobalLiftUniqueness
