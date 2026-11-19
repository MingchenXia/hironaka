import Hironaka.Analytic.Unibranch.EmbeddedBlowupNativeIdealComparison

/-!
# Full lifts from actual source opens over unequal original chart ranges

Current whole ideal dictionaries and honest source-model density imply
the required source ideal invertible through actual open-immersion stalk
isomorphisms. The existing arbitrary ORIGINAL-source UP supplies all full
maps. This generic connection has no independent milestone credit.
Blueprint: `embedded-ideal-blowup-open-source.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupOpenSource

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaSingularSubspaceBlowupLift HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealSheaf HironakaSingularIdealRegularPrincipal
  HironakaSingularSubspaceBlowupCartierUniversalProjectionInvertible
  HironakaSingularSubspaceBlowupCartierUniversalStalkTransport
  SourceReducedComplexSpace EmbeddedBlowup EmbeddedBlowupUniversal
  EmbeddedBlowupGlobalUniversalLocal

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

private theorem projection_global_invertible
    (hπ₀ : IsBlowupAlong n₀ C₀ π₀) (hW₀ : IsComplexAnalyticSubset (n := n₀) W₀)
    (j₀ : actualSubspaceLocallyRingedSpace (n := n₀) W₀ ⟶ X.obj.left)
    (hd₀ : W₀ ⊆ closure (W₀ \ C₀))
    (hJ₀ : ∀ y : W₀,
      Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) y.val) =
          nativePulledIdealStalkIdeal j₀ B b y)
    (z : strictTransform n₀ π₀ W₀) :
    Module.Invertible
      ((actualSubspaceLocallyRingedSpace (n := n₀) (strictTransform n₀ π₀ W₀)).presheaf.stalk z).carrier
      (nativePulledIdealStalkIdeal (strictTransformProjection hπ₀ hW₀.isClosed ≫ j₀) B b z) := by
  let p := strictTransformProjection hπ₀ hW₀.isClosed
  have hi := congrArg (Ideal.map (p.stalkMap z).hom) (hJ₀ (p.base z))
  have hc := nativePulledIdealStalkIdeal_comp p j₀ B b z
  have he := hi.trans hc.symm
  exact (congrArg (fun I : Ideal
      ((actualSubspaceLocallyRingedSpace (n := n₀) (strictTransform n₀ π₀ W₀)).presheaf.stalk z).carrier =>
        Module.Invertible _ I) he).mp
    (projection_pulled_ideal_moduleInvertible hπ₀ hW₀.isClosed hd₀ z)

private theorem open_source_global_invertible
    (hπ₀ : IsBlowupAlong n₀ C₀ π₀) (hW₀ : IsComplexAnalyticSubset (n := n₀) W₀)
    (j₀ : actualSubspaceLocallyRingedSpace (n := n₀) W₀ ⟶ X.obj.left)
    (hd₀ : W₀ ⊆ closure (W₀ \ C₀))
    (hJ₀ : ∀ y : W₀,
      Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) y.val) =
          nativePulledIdealStalkIdeal j₀ B b y)
    {A : LocallyRingedSpace}
    (r : A ⟶ actualSubspaceLocallyRingedSpace (n := n₀) (strictTransform n₀ π₀ W₀))
    [hr : LocallyRingedSpace.IsOpenImmersion r] (x : A) :
    Module.Invertible (A.presheaf.stalk x).carrier
      (nativePulledIdealStalkIdeal (r ≫ strictTransformProjection hπ₀ hW₀.isClosed ≫ j₀) B b x) := by
  let F := strictTransformProjection hπ₀ hW₀.isClosed ≫ j₀
  let I := LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b (F.base (r.base x)))
  obtain ⟨a,ha,hs⟩ := exists_regular_generator_on_open_chart r F x I
    (projection_global_invertible B b hπ₀ hW₀ j₀ hd₀ hJ₀ (r.base x))
  exact moduleInvertible_of_span_eq _ hs ha

private theorem open_source_target_invertible
    (hπ₀ : IsBlowupAlong n₀ C₀ π₀) (hW₀ : IsComplexAnalyticSubset (n := n₀) W₀)
    (j₀ : actualSubspaceLocallyRingedSpace (n := n₀) W₀ ⟶ X.obj.left)
    (j₁ : actualSubspaceLocallyRingedSpace (n := n₁) W₁ ⟶ X.obj.left)
    (hd₀ : W₀ ⊆ closure (W₀ \ C₀))
    (hJ₀ : ∀ y : W₀,
      Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) y.val) =
          nativePulledIdealStalkIdeal j₀ B b y)
    (hJ₁ : ∀ y : W₁,
      Ideal.map ((actualSubspaceInclusion (n := n₁) W₁).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₁) C₁) y.val) =
          nativePulledIdealStalkIdeal j₁ B b y)
    {A : LocallyRingedSpace}
    (r : A ⟶ actualSubspaceLocallyRingedSpace (n := n₀) (strictTransform n₀ π₀ W₀))
    [hr : LocallyRingedSpace.IsOpenImmersion r]
    (F : A ⟶ actualSubspaceLocallyRingedSpace (n := n₁) W₁)
    (he : F ≫ j₁ = r ≫ strictTransformProjection hπ₀ hW₀.isClosed ≫ j₀) (x : A) :
    Module.Invertible (A.presheaf.stalk x).carrier
      (Ideal.map (F.stalkMap x).hom
        (Ideal.map ((actualSubspaceInclusion (n := n₁) W₁).stalkMap (F.base x)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₁) C₁) (F.base x).val))) := by
  have ht := congrArg (Ideal.map (F.stalkMap x).hom) (hJ₁ (F.base x))
  have hc := nativePulledIdealStalkIdeal_comp F j₁ B b x
  have hn := congrArg (fun G : A ⟶ X.obj.left => nativePulledIdealStalkIdeal G B b x) he
  have hI := ht.trans (hc.symm.trans hn)
  exact (congrArg (fun I : Ideal (A.presheaf.stalk x).carrier => Module.Invertible _ I) hI).mpr
    (open_source_global_invertible B b hπ₀ hW₀ j₀ hd₀ hJ₀ r x)

/-- A genuine ORIGINAL source open lifts uniquely through the other local
blowup over X. Only actual image containment is required, not equal ranges. -/
theorem exists_unique_lift_over_X
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
    (A : SourceReducedComplexSpace)
    (r : A ⟶ ofClosedAnalytic (strictTransform n₀ π₀ W₀)
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ₀ hW₀))
    [hr : LocallyRingedSpace.IsOpenImmersion r.hom.left]
    (hrange : range (r ≫ strictTransformMorphism hπ₀ hW₀ ≫ j₀).hom.left.base ⊆ range j₁.hom.left.base) :
    ∃! L : A ⟶ ofClosedAnalytic (strictTransform n₁ π₁ W₁)
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ₁ hW₁),
      L ≫ strictTransformMorphism hπ₁ hW₁ ≫ j₁ = r ≫ strictTransformMorphism hπ₀ hW₀ ≫ j₀ := by
  let A₀ := ofClosedAnalytic (strictTransform n₀ π₀ W₀)
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ₀ hW₀)
  let A₁ := ofClosedAnalytic (strictTransform n₁ π₁ W₁)
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ₁ hW₁)
  let p₀ : A₀ ⟶ ofClosedAnalytic W₀ hW₀ := strictTransformMorphism hπ₀ hW₀
  let p₁ : A₁ ⟶ ofClosedAnalytic W₁ hW₁ := strictTransformMorphism hπ₁ hW₁
  let f : A ⟶ X := r ≫ p₀ ≫ j₀
  let q := LocallyRingedSpace.IsOpenImmersion.lift j₁.hom.left f.hom.left hrange
  have hq : q ≫ j₁.hom.left = f.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac j₁.hom.left f.hom.left hrange
  have hqp : q ≫ (ofClosedAnalytic W₁ hW₁).obj.hom = A.obj.hom := by
    rw [← Over.w j₁.hom,← Category.assoc,hq]
    exact Over.w f.hom
  let F : A ⟶ ofClosedAnalytic W₁ hW₁ := ObjectProperty.homMk (Over.homMk q hqp)
  have hF : F ≫ j₁ = f := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hq
  have hqRaw : q ≫ j₁.hom.left =
      r.hom.left ≫ strictTransformProjection hπ₀ hW₀.isClosed ≫ j₀.hom.left := hq
  have hInv := open_source_target_invertible B b hπ₀ hW₀ j₀.hom.left j₁.hom.left
    hd₀ hJ₀ hJ₁ r.hom.left (hr := hr) q hqRaw
  obtain ⟨L,hL,hLu⟩ := exists_unique_source_factorization_of_module_invertible hπ₁ hW₁ A F hInv
  refine ⟨L,?_,?_⟩
  · calc
      L ≫ p₁ ≫ j₁ = (L ≫ p₁) ≫ j₁ := (Category.assoc _ _ _).symm
      _ = F ≫ j₁ := congrArg (fun t => t ≫ j₁) hL
      _ = f := hF
  · intro L' hL'
    have hp : L' ≫ p₁ = F := by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply (cancel_mono j₁.hom.left).mp
      have h := congrArg (fun H : A ⟶ X => H.hom.left) hL'
      have hf := congrArg (fun H : A ⟶ X => H.hom.left) hF
      change L'.hom.left ≫ p₁.hom.left ≫ j₁.hom.left = f.hom.left at h
      change (L'.hom.left ≫ p₁.hom.left) ≫ j₁.hom.left = F.hom.left ≫ j₁.hom.left
      exact (Category.assoc _ _ _).trans (h.trans hf.symm)
    exact hLu L' hp

/-- Two FULL original maps from a genuine source open with the SAME
projection-to-X square are equal. Their square itself derives containment. -/
theorem lift_eq_of_over_X
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
    (A : SourceReducedComplexSpace)
    (r : A ⟶ ofClosedAnalytic (strictTransform n₀ π₀ W₀)
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ₀ hW₀))
    [hr : LocallyRingedSpace.IsOpenImmersion r.hom.left]
    (L₁ L₂ : A ⟶ ofClosedAnalytic (strictTransform n₁ π₁ W₁)
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ₁ hW₁))
    (h₁ : L₁ ≫ strictTransformMorphism hπ₁ hW₁ ≫ j₁ = r ≫ strictTransformMorphism hπ₀ hW₀ ≫ j₀)
    (h₂ : L₂ ≫ strictTransformMorphism hπ₁ hW₁ ≫ j₁ = r ≫ strictTransformMorphism hπ₀ hW₀ ≫ j₀) : L₁ = L₂ := by
  have hrange : range (r ≫ strictTransformMorphism hπ₀ hW₀ ≫ j₀).hom.left.base ⊆ range j₁.hom.left.base := by
    rintro x ⟨u,rfl⟩
    refine ⟨(strictTransformMorphism hπ₁ hW₁).hom.left.base (L₁.hom.left.base u),?_⟩
    exact congrArg (fun H => H.hom.left.base u) h₁
  obtain ⟨L,_,hLu⟩ := exists_unique_lift_over_X B b hπ₀ hπ₁ hW₀ hW₁ j₀ j₁ hd₀ hJ₀ hJ₁ A r (hr := hr) hrange
  exact (hLu L₁ h₁).trans (hLu L₂ h₂).symm

end
end Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupOpenSource
