import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupOpenSource
import Hironaka.Analytic.Unibranch.EmbeddedBlowupOpenRestriction

/-!
# Full map uniqueness on actual raw open sources

The existing original literal restriction on the actual source image is
canonically isomorphic to the given raw open source. Pulling back the full
maps lets the original UP apply without a new source object or certificate.
Blueprint: `embedded-ideal-blowup-raw-open-source.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupRawOpenSource

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaSingularSubspaceBlowupLift HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealSheaf HironakaEmbeddedNativeMorphism
  SourceReducedComplexSpace EmbeddedBlowup EmbeddedBlowupOpenRestriction
  EmbeddedIdealBlowupOpenSource

noncomputable section

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))

variable {n₀ n₁ : ℕ} {M₀ Y₀ M₁ Y₁ : Type}
  [TopologicalSpace M₀] [ChartedSpace (ComplexModel n₀) M₀] [IsComplexManifold n₀ M₀]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n₀) Y₀] [IsComplexManifold n₀ Y₀]
  [TopologicalSpace M₁] [ChartedSpace (ComplexModel n₁) M₁] [IsComplexManifold n₁ M₁]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n₁) Y₁] [IsComplexManifold n₁ Y₁]
  {C₀ W₀ : Set M₀} {C₁ W₁ : Set M₁} {π₀ : Y₀ → M₀} {π₁ : Y₁ → M₁}

/-- Actual raw source-open maps with the SAME full projection square are
equal. An existing original restriction on the actual range supplies the
original-source UP; no source atlas/category/countability packet is input. -/
theorem raw_lift_eq_of_over_X
    (hπ₀ : IsBlowupAlong n₀ C₀ π₀) (hπ₁ : IsBlowupAlong n₁ C₁ π₁)
    (hW₀ : IsComplexAnalyticSubset (n := n₀) W₀)
    (hW₁ : IsComplexAnalyticSubset (n := n₁) W₁)
    (j₀ : ofClosedAnalytic W₀ hW₀ ⟶ X) (j₁ : ofClosedAnalytic W₁ hW₁ ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion j₁.hom.left]
    (hd₀ : W₀ ⊆ closure (W₀ \ C₀))
    (hJ₀ : ∀ y : W₀,
      Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) y.val) =
          nativePulledIdealStalkIdeal j₀.hom.left B b y)
    (hJ₁ : ∀ y : W₁,
      Ideal.map ((actualSubspaceInclusion (n := n₁) W₁).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₁) C₁) y.val) =
          nativePulledIdealStalkIdeal j₁.hom.left B b y)
    {H : LocallyRingedSpace}
    (r : H ⟶ actualSubspaceLocallyRingedSpace (n := n₀) (strictTransform n₀ π₀ W₀))
    [hr : LocallyRingedSpace.IsOpenImmersion r]
    (L₁ L₂ : H ⟶ actualSubspaceLocallyRingedSpace (n := n₁) (strictTransform n₁ π₁ W₁))
    (h₁ : L₁ ≫ strictTransformProjection hπ₁ hW₁.isClosed ≫ j₁.hom.left =
      r ≫ strictTransformProjection hπ₀ hW₀.isClosed ≫ j₀.hom.left)
    (h₂ : L₂ ≫ strictTransformProjection hπ₁ hW₁.isClosed ≫ j₁.hom.left =
      r ≫ strictTransformProjection hπ₀ hW₀.isClosed ≫ j₀.hom.left) : L₁ = L₂ := by
  let hS₀ := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ₀ hW₀
  let hS₁ := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ₁ hW₁
  let V : Opens (strictTransform n₀ π₀ W₀) := ⟨range r.base, hr.base_open.isOpen_range⟩
  let K := restrictedClosedAnalytic hS₀ V
  let s : K ⟶ ofClosedAnalytic _ hS₀ := restrictionInclusion hS₀ V
  have hs : range s.hom.left.base = range r.base := by
    change range (Subtype.val : V → strictTransform n₀ π₀ W₀) = range r.base
    exact Subtype.range_coe
  let E := @openImmersionIsoOfRangeEq K.obj.left H _ s.hom.left r inferInstance hr hs
  have hE : E.hom ≫ r = s.hom.left :=
    @openImmersionIsoOfRangeEq_hom_fac K.obj.left H _ s.hom.left r inferInstance hr hs
  let p₀ := strictTransformMorphism hπ₀ hW₀
  let p₁ := strictTransformMorphism hπ₁ hW₁
  have hp₀ : p₀.hom.left ≫ j₀.hom.left ≫ X.obj.hom = (ofClosedAnalytic _ hS₀).obj.hom := by
    rw [Over.w j₀.hom]
    exact Over.w p₀.hom
  have hp₁ : p₁.hom.left ≫ j₁.hom.left ≫ X.obj.hom = (ofClosedAnalytic _ hS₁).obj.hom := by
    rw [Over.w j₁.hom]
    exact Over.w p₁.hom
  have hraw (L : H ⟶ actualSubspaceLocallyRingedSpace (n := n₁) (strictTransform n₁ π₁ W₁))
      (h : L ≫ strictTransformProjection hπ₁ hW₁.isClosed ≫ j₁.hom.left =
        r ≫ strictTransformProjection hπ₀ hW₀.isClosed ≫ j₀.hom.left) :
      (E.hom ≫ L) ≫ p₁.hom.left ≫ j₁.hom.left =
        s.hom.left ≫ p₀.hom.left ≫ j₀.hom.left := by
    calc
      _ = E.hom ≫ (L ≫ strictTransformProjection hπ₁ hW₁.isClosed ≫ j₁.hom.left) := by
        simp only [Category.assoc]; rfl
      _ = E.hom ≫ (r ≫ strictTransformProjection hπ₀ hW₀.isClosed ≫ j₀.hom.left) := congrArg (fun t => E.hom ≫ t) h
      _ = _ := by rw [← Category.assoc E.hom r, hE]; rfl
  have hσ (L : H ⟶ actualSubspaceLocallyRingedSpace (n := n₁) (strictTransform n₁ π₁ W₁))
      (h : (E.hom ≫ L) ≫ p₁.hom.left ≫ j₁.hom.left =
        s.hom.left ≫ p₀.hom.left ≫ j₀.hom.left) :
      (E.hom ≫ L) ≫ (ofClosedAnalytic _ hS₁).obj.hom = K.obj.hom := by
    calc
      _ = (E.hom ≫ L) ≫ (p₁.hom.left ≫ j₁.hom.left ≫ X.obj.hom) :=
        congrArg (fun t => (E.hom ≫ L) ≫ t) hp₁.symm
      _ = ((E.hom ≫ L) ≫ p₁.hom.left ≫ j₁.hom.left) ≫ X.obj.hom :=
        (Category.assoc _ _ _).symm
      _ = (s.hom.left ≫ p₀.hom.left ≫ j₀.hom.left) ≫ X.obj.hom := congrArg (fun t => t ≫ X.obj.hom) h
      _ = s.hom.left ≫ (p₀.hom.left ≫ j₀.hom.left ≫ X.obj.hom) := by simp only [Category.assoc]
      _ = s.hom.left ≫ (ofClosedAnalytic _ hS₀).obj.hom := congrArg (fun t => s.hom.left ≫ t) hp₀
      _ = K.obj.hom := Over.w s.hom
  let F₁ : K ⟶ ofClosedAnalytic _ hS₁ := ObjectProperty.homMk (Over.homMk (E.hom ≫ L₁) (hσ L₁ (hraw L₁ h₁)))
  let F₂ : K ⟶ ofClosedAnalytic _ hS₁ := ObjectProperty.homMk (Over.homMk (E.hom ≫ L₂) (hσ L₂ (hraw L₂ h₂)))
  have heq : F₁ = F₂ := lift_eq_of_over_X B b hπ₀ hπ₁ hW₀ hW₁ j₀ j₁ hd₀ hJ₀ hJ₁ K s
    F₁ F₂ (by apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext; exact hraw L₁ h₁)
    (by apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext; exact hraw L₂ h₂)
  exact (cancel_epi E.hom).mp (congrArg (fun F : K ⟶ ofClosedAnalytic _ hS₁ => F.hom.left) heq)

end
end Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupRawOpenSource
