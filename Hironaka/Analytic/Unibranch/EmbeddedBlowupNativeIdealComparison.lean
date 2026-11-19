import Hironaka.Analytic.Unibranch.EmbeddedBlowupComparison
import Hironaka.Analytic.Unibranch.EmbeddedBlowupGlobalUniversalLocal
import Hironaka.Resolution.HironakaEmbeddedNativeMorphismCommon

/-! Current whole original ideal geometry gives an actual unique comparison
of literal strict-transform models. Ambient centres need not lie in the
carriers. The final graph caller DERIVES the current ideal dictionaries;
this generic comparison/inverse adaptation has zero independent milestone
credit. Blueprint FIRST: `embedded-blowup-native-ideal-comparison.tex`. -/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedBlowupNativeIdealComparison

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaSingularSubspaceBlowupLift HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealSheaf HironakaEmbeddedNativeMorphism
  HironakaSingularSubspaceBlowupCartierUniversalProjectionInvertible
  SourceReducedComplexSpace EmbeddedBlowup EmbeddedBlowupUniversal
  EmbeddedBlowupGlobalUniversalLocal

noncomputable section

private def baseIso {A D X : SourceReducedComplexSpace} (j₀ : A ⟶ X) (j₁ : D ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion j₀.hom.left]
    [LocallyRingedSpace.IsOpenImmersion j₁.hom.left]
    (hr : range j₀.hom.left.base = range j₁.hom.left.base) : A ≅ D := by
  let E := openImmersionIsoOfRangeEq j₀.hom.left j₁.hom.left hr
  have hE : E.hom ≫ j₁.hom.left = j₀.hom.left :=
    openImmersionIsoOfRangeEq_hom_fac j₀.hom.left j₁.hom.left hr
  have hp : E.hom ≫ D.obj.hom = A.obj.hom := by
    rw [← Over.w j₁.hom, ← Category.assoc, hE]
    exact Over.w j₀.hom
  exact ObjectProperty.isoMk sourceReducedComplexSpaceProperty (Over.isoMk E hp)

private theorem baseIso_fac {A D X : SourceReducedComplexSpace} (j₀ : A ⟶ X) (j₁ : D ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion j₀.hom.left]
    [LocallyRingedSpace.IsOpenImmersion j₁.hom.left]
    (hr : range j₀.hom.left.base = range j₁.hom.left.base) :
    (baseIso j₀ j₁ hr).hom ≫ j₁ = j₀ := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact openImmersionIsoOfRangeEq_hom_fac j₀.hom.left j₁.hom.left hr

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))

variable {n₀ n₁ : ℕ} {M₀ Y₀ M₁ Y₁ : Type}
  [TopologicalSpace M₀] [ChartedSpace (ComplexModel n₀) M₀] [IsComplexManifold n₀ M₀]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n₀) Y₀] [IsComplexManifold n₀ Y₀]
  [TopologicalSpace M₁] [ChartedSpace (ComplexModel n₁) M₁] [IsComplexManifold n₁ M₁]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n₁) Y₁] [IsComplexManifold n₁ Y₁]
  {C₀ W₀ : Set M₀} {C₁ W₁ : Set M₁} {π₀ : Y₀ → M₀} {π₁ : Y₁ → M₁}

private theorem composite_projection_invertible
    (hπ₀ : IsBlowupAlong n₀ C₀ π₀)
    (hW₀ : IsComplexAnalyticSubset (n := n₀) W₀)
    (j₀ : actualSubspaceLocallyRingedSpace (n := n₀) W₀ ⟶ X.obj.left)
    (j₁ : actualSubspaceLocallyRingedSpace (n := n₁) W₁ ⟶ X.obj.left)
    (F : actualSubspaceLocallyRingedSpace (n := n₀) W₀ ⟶
      actualSubspaceLocallyRingedSpace (n := n₁) W₁)
    (he : F ≫ j₁ = j₀)
    (hd₀ : W₀ ⊆ closure (W₀ \ C₀))
    (hJ₀ : ∀ y : W₀,
      Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) y.val) =
          nativePulledIdealStalkIdeal j₀ B b y)
    (hJ₁ : ∀ y : W₁,
      Ideal.map ((actualSubspaceInclusion (n := n₁) W₁).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₁) C₁) y.val) =
          nativePulledIdealStalkIdeal j₁ B b y)
    (z : strictTransform n₀ π₀ W₀) :
    Module.Invertible
      ((actualSubspaceLocallyRingedSpace (n := n₀) (strictTransform n₀ π₀ W₀)).presheaf.stalk z).carrier
      (Ideal.map (((strictTransformProjection hπ₀ hW₀.isClosed) ≫ F).stalkMap z).hom
        (Ideal.map ((actualSubspaceInclusion (n := n₁) W₁).stalkMap
          (((strictTransformProjection hπ₀ hW₀.isClosed) ≫ F).base z)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₁) C₁)
            (((strictTransformProjection hπ₀ hW₀.isClosed) ≫ F).base z).val))) := by
  let p₀ := strictTransformProjection hπ₀ hW₀.isClosed
  have hfac : (p₀ ≫ F) ≫ j₁ = p₀ ≫ j₀ := by rw [Category.assoc, he]
  have hnat := congrArg
    (fun G : actualSubspaceLocallyRingedSpace (n := n₀) (strictTransform n₀ π₀ W₀) ⟶ X.obj.left =>
      nativePulledIdealStalkIdeal G B b z) hfac
  have ht := congrArg (Ideal.map ((p₀ ≫ F).stalkMap z).hom) (hJ₁ ((p₀ ≫ F).base z))
  have hs := congrArg (Ideal.map (p₀.stalkMap z).hom) (hJ₀ (p₀.base z))
  have hp₁ := nativePulledIdealStalkIdeal_comp (p₀ ≫ F) j₁ B b z
  have hp₀ := nativePulledIdealStalkIdeal_comp p₀ j₀ B b z
  have heq := ht.trans (hp₁.symm.trans (hnat.trans (hp₀.trans hs.symm)))
  exact (congrArg (fun I : Ideal
      ((actualSubspaceLocallyRingedSpace (n := n₀) (strictTransform n₀ π₀ W₀)).presheaf.stalk z).carrier =>
        Module.Invertible _ I) heq).mpr
    (projection_pulled_ideal_moduleInvertible hπ₀ hW₀.isClosed hd₀ z)

/-- CURRENT whole ideal geometry, derived by actual graph source producers,
gives a unique full ORIGINAL strict-transform iso. No contained/reduced centre
or comparison/base-iso/cocycle certificate is assumed. -/
theorem exists_unique_strictTransform_iso_of_native_ideal
    (hπ₀ : IsBlowupAlong n₀ C₀ π₀) (hπ₁ : IsBlowupAlong n₁ C₁ π₁)
    (hW₀ : IsComplexAnalyticSubset (n := n₀) W₀)
    (hW₁ : IsComplexAnalyticSubset (n := n₁) W₁)
    (j₀ : ofClosedAnalytic W₀ hW₀ ⟶ X) (j₁ : ofClosedAnalytic W₁ hW₁ ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion j₀.hom.left]
    [LocallyRingedSpace.IsOpenImmersion j₁.hom.left]
    (hr : range j₀.hom.left.base = range j₁.hom.left.base)
    (hd₀ : W₀ ⊆ closure (W₀ \ C₀)) (hd₁ : W₁ ⊆ closure (W₁ \ C₁))
    (hJ₀ : ∀ y : W₀,
      Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) y.val) =
          nativePulledIdealStalkIdeal j₀.hom.left B b y)
    (hJ₁ : ∀ y : W₁,
      Ideal.map ((actualSubspaceInclusion (n := n₁) W₁).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₁) C₁) y.val) =
          nativePulledIdealStalkIdeal j₁.hom.left B b y) :
    ∃! E : ofClosedAnalytic (strictTransform n₀ π₀ W₀)
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ₀ hW₀) ≅
      ofClosedAnalytic (strictTransform n₁ π₁ W₁)
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ₁ hW₁),
      E.hom ≫ strictTransformMorphism hπ₁ hW₁ ≫ j₁ = strictTransformMorphism hπ₀ hW₀ ≫ j₀ := by
  let A₀ := ofClosedAnalytic (strictTransform n₀ π₀ W₀)
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ₀ hW₀)
  let A₁ := ofClosedAnalytic (strictTransform n₁ π₁ W₁)
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ₁ hW₁)
  let p₀ : A₀ ⟶ ofClosedAnalytic W₀ hW₀ := strictTransformMorphism hπ₀ hW₀
  let p₁ : A₁ ⟶ ofClosedAnalytic W₁ hW₁ := strictTransformMorphism hπ₁ hW₁
  let e := baseIso j₀ j₁ hr
  have he : e.hom ≫ j₁ = j₀ := baseIso_fac j₀ j₁ hr
  have hei : e.inv ≫ j₀ = j₁ := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have heRaw : e.hom.hom.left ≫ j₁.hom.left = j₀.hom.left :=
    congrArg (fun F => F.hom.left) he
  have heiRaw : e.inv.hom.left ≫ j₀.hom.left = j₁.hom.left :=
    congrArg (fun F => F.hom.left) hei
  obtain ⟨L,hL,hLu⟩ := exists_unique_source_factorization_of_module_invertible hπ₁ hW₁ A₀ (p₀ ≫ e.hom)
    (composite_projection_invertible B b hπ₀ hW₀ j₀.hom.left j₁.hom.left e.hom.hom.left heRaw hd₀ hJ₀ hJ₁)
  obtain ⟨R,hR,_⟩ := exists_unique_source_factorization_of_module_invertible hπ₀ hW₀ A₁ (p₁ ≫ e.inv)
    (composite_projection_invertible B b hπ₁ hW₁ j₁.hom.left j₀.hom.left e.inv.hom.left heiRaw hd₁ hJ₁ hJ₀)
  obtain ⟨Q₀,_,hQ₀⟩ := exists_unique_source_factorization_of_module_invertible hπ₀ hW₀ A₀ p₀
    (projection_pulled_ideal_moduleInvertible hπ₀ hW₀.isClosed hd₀)
  obtain ⟨Q₁,_,hQ₁⟩ := exists_unique_source_factorization_of_module_invertible hπ₁ hW₁ A₁ p₁
    (projection_pulled_ideal_moduleInvertible hπ₁ hW₁.isClosed hd₁)
  have hLR : L ≫ R = 𝟙 A₀ := by
    apply (hQ₀ (L ≫ R) ?_).trans (hQ₀ (𝟙 A₀) (Category.id_comp p₀)).symm
    calc
      (L ≫ R) ≫ p₀ = L ≫ (R ≫ p₀) := Category.assoc _ _ _
      _ = L ≫ (p₁ ≫ e.inv) := congrArg (fun t => L ≫ t) hR
      _ = (L ≫ p₁) ≫ e.inv := (Category.assoc _ _ _).symm
      _ = (p₀ ≫ e.hom) ≫ e.inv := congrArg (fun t => t ≫ e.inv) hL
      _ = p₀ := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  have hRL : R ≫ L = 𝟙 A₁ := by
    apply (hQ₁ (R ≫ L) ?_).trans (hQ₁ (𝟙 A₁) (Category.id_comp p₁)).symm
    calc
      (R ≫ L) ≫ p₁ = R ≫ (L ≫ p₁) := Category.assoc _ _ _
      _ = R ≫ (p₀ ≫ e.hom) := congrArg (fun t => R ≫ t) hL
      _ = (R ≫ p₀) ≫ e.hom := (Category.assoc _ _ _).symm
      _ = (p₁ ≫ e.inv) ≫ e.hom := congrArg (fun t => t ≫ e.hom) hR
      _ = p₁ := by rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  let E : A₀ ≅ A₁ := ⟨L,R,hLR,hRL⟩
  refine ⟨E,?_,?_⟩
  · calc
      L ≫ p₁ ≫ j₁ = (L ≫ p₁) ≫ j₁ := (Category.assoc _ _ _).symm
      _ = (p₀ ≫ e.hom) ≫ j₁ := congrArg (fun t => t ≫ j₁) hL
      _ = p₀ ≫ j₀ := by rw [Category.assoc, he]
  · intro E' hE'
    have hp : E'.hom ≫ p₁ = p₀ ≫ e.hom := by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply (cancel_mono j₁.hom.left).mp
      have h := congrArg (fun F : A₀ ⟶ X => F.hom.left) hE'
      have ht := congrArg (fun F : ofClosedAnalytic W₀ hW₀ ⟶ X => F.hom.left) he
      change E'.hom.hom.left ≫ p₁.hom.left ≫ j₁.hom.left = p₀.hom.left ≫ j₀.hom.left at h
      change e.hom.hom.left ≫ j₁.hom.left = j₀.hom.left at ht
      change (E'.hom.hom.left ≫ p₁.hom.left) ≫ j₁.hom.left =
        (p₀.hom.left ≫ e.hom.hom.left) ≫ j₁.hom.left
      calc
        _ = p₀.hom.left ≫ j₀.hom.left := h
        _ = _ := by rw [Category.assoc, ht]
    apply Iso.ext
    exact hLu E'.hom hp

end
end Hironaka.Analytic.Unibranch.EmbeddedBlowupNativeIdealComparison
