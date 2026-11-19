import Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowupCartier
import Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowupUniversal
import Hironaka.Analytic.Unibranch.EmbeddedBlowupGlobalUniversalLocal

/-!
# Actual geometric source-open lifting with NO target density

OWN geometric projection invertibility and the actual source OI derive
all required whole-ideal input to the genuine no-target-density GEO UP.
No centre containment/equalranges/source packet or reduced ideal.
Blueprint FIRST: `embedded-geometric-ideal-open-source.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedGeometricIdealOpenSource

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaSingularSubspaceBlowupLift HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealSheaf HironakaSingularIdealRegularPrincipal BlowupStrictSubmanifold
  HironakaSingularSubspaceBlowupCartierUniversalStalkTransport
  SourceReducedComplexSpace EmbeddedGeometricBlowup EmbeddedGeometricBlowupCartier EmbeddedGeometricBlowupUniversal
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
    (hJ₀ : ∀ y : W₀,
      Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) y.val) =
          nativePulledIdealStalkIdeal j₀ B b y)
    (z : geoStrictTransform π₀ C₀ W₀) :
    Module.Invertible
      ((actualSubspaceLocallyRingedSpace (n := n₀) (geoStrictTransform π₀ C₀ W₀)).presheaf.stalk z).carrier
      (nativePulledIdealStalkIdeal (geometricProjection hπ₀ hW₀.isClosed ≫ j₀) B b z) := by
  let p := geometricProjection hπ₀ hW₀.isClosed
  have hi := congrArg (Ideal.map (p.stalkMap z).hom) (hJ₀ (p.base z))
  have hc := nativePulledIdealStalkIdeal_comp p j₀ B b z
  have he := hi.trans hc.symm
  exact (congrArg (fun I : Ideal
      ((actualSubspaceLocallyRingedSpace (n := n₀) (geoStrictTransform π₀ C₀ W₀)).presheaf.stalk z).carrier =>
        Module.Invertible _ I) he).mp
    (geometricProjection_ideal_moduleInvertible hπ₀ hW₀.isClosed z)

private theorem open_source_global_invertible
    (hπ₀ : IsBlowupAlong n₀ C₀ π₀) (hW₀ : IsComplexAnalyticSubset (n := n₀) W₀)
    (j₀ : actualSubspaceLocallyRingedSpace (n := n₀) W₀ ⟶ X.obj.left)
    (hJ₀ : ∀ y : W₀,
      Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) y.val) =
          nativePulledIdealStalkIdeal j₀ B b y)
    {A : LocallyRingedSpace}
    (r : A ⟶ actualSubspaceLocallyRingedSpace (n := n₀) (geoStrictTransform π₀ C₀ W₀))
    [hr : LocallyRingedSpace.IsOpenImmersion r] (x : A) :
    Module.Invertible (A.presheaf.stalk x).carrier
      (nativePulledIdealStalkIdeal (r ≫ geometricProjection hπ₀ hW₀.isClosed ≫ j₀) B b x) := by
  let F := geometricProjection hπ₀ hW₀.isClosed ≫ j₀
  let I := LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b (F.base (r.base x)))
  obtain ⟨a,ha,hs⟩ := exists_regular_generator_on_open_chart r F x I
    (projection_global_invertible B b hπ₀ hW₀ j₀ hJ₀ (r.base x))
  exact moduleInvertible_of_span_eq _ hs ha

private theorem open_source_target_invertible
    (hπ₀ : IsBlowupAlong n₀ C₀ π₀) (hW₀ : IsComplexAnalyticSubset (n := n₀) W₀)
    (j₀ : actualSubspaceLocallyRingedSpace (n := n₀) W₀ ⟶ X.obj.left)
    (j₁ : actualSubspaceLocallyRingedSpace (n := n₁) W₁ ⟶ X.obj.left)
    (hJ₀ : ∀ y : W₀,
      Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) y.val) =
          nativePulledIdealStalkIdeal j₀ B b y)
    (hJ₁ : ∀ y : W₁,
      Ideal.map ((actualSubspaceInclusion (n := n₁) W₁).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₁) C₁) y.val) =
          nativePulledIdealStalkIdeal j₁ B b y)
    {A : LocallyRingedSpace}
    (r : A ⟶ actualSubspaceLocallyRingedSpace (n := n₀) (geoStrictTransform π₀ C₀ W₀))
    [hr : LocallyRingedSpace.IsOpenImmersion r]
    (F : A ⟶ actualSubspaceLocallyRingedSpace (n := n₁) W₁)
    (he : F ≫ j₁ = r ≫ geometricProjection hπ₀ hW₀.isClosed ≫ j₀) (x : A) :
    Module.Invertible (A.presheaf.stalk x).carrier
      (Ideal.map (F.stalkMap x).hom
        (Ideal.map ((actualSubspaceInclusion (n := n₁) W₁).stalkMap (F.base x)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₁) C₁) (F.base x).val))) := by
  have ht := congrArg (Ideal.map (F.stalkMap x).hom) (hJ₁ (F.base x))
  have hc := nativePulledIdealStalkIdeal_comp F j₁ B b x
  have hn := congrArg (fun G : A ⟶ X.obj.left => nativePulledIdealStalkIdeal G B b x) he
  have hI := ht.trans (hc.symm.trans hn)
  exact (congrArg (fun I : Ideal (A.presheaf.stalk x).carrier => Module.Invertible _ I) hI).mpr
    (open_source_global_invertible B b hπ₀ hW₀ j₀ hJ₀ r x)

/-- A genuine ORIGINAL source open lifts uniquely through the other local
blowup over X. Only actual image containment is required, not equal ranges. -/
theorem exists_unique_lift_over_X
    (hπ₀ : IsBlowupAlong n₀ C₀ π₀) (hπ₁ : IsBlowupAlong n₁ C₁ π₁)
    (hW₀ : IsComplexAnalyticSubset (n := n₀) W₀)
    (hW₁ : IsComplexAnalyticSubset (n := n₁) W₁)
    (j₀ : ofClosedAnalytic W₀ hW₀ ⟶ X) (j₁ : ofClosedAnalytic W₁ hW₁ ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion j₁.hom.left]
    (hJ₀ : ∀ y : W₀,
      Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) y.val) =
          nativePulledIdealStalkIdeal j₀.hom.left B b y)
    (hJ₁ : ∀ y : W₁,
      Ideal.map ((actualSubspaceInclusion (n := n₁) W₁).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₁) C₁) y.val) =
          nativePulledIdealStalkIdeal j₁.hom.left B b y)
    (A : SourceReducedComplexSpace)
    (r : A ⟶ geometricSource hπ₀ hW₀)
    [hr : LocallyRingedSpace.IsOpenImmersion r.hom.left]
    (hrange : range (r ≫ geometricProjectionMorphism hπ₀ hW₀ ≫ j₀).hom.left.base ⊆ range j₁.hom.left.base) :
    ∃! L : A ⟶ geometricSource hπ₁ hW₁,
      L ≫ geometricProjectionMorphism hπ₁ hW₁ ≫ j₁ = r ≫ geometricProjectionMorphism hπ₀ hW₀ ≫ j₀ := by
  let A₀ := geometricSource hπ₀ hW₀
  let A₁ := geometricSource hπ₁ hW₁
  let p₀ : A₀ ⟶ ofClosedAnalytic W₀ hW₀ := geometricProjectionMorphism hπ₀ hW₀
  let p₁ : A₁ ⟶ ofClosedAnalytic W₁ hW₁ := geometricProjectionMorphism hπ₁ hW₁
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
      r.hom.left ≫ geometricProjection hπ₀ hW₀.isClosed ≫ j₀.hom.left := hq
  have hInv := open_source_target_invertible B b hπ₀ hW₀ j₀.hom.left j₁.hom.left
    hJ₀ hJ₁ r.hom.left (hr := hr) q hqRaw
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

/-- Two FULL original maps from a genuine geometric source open with the SAME
projection-to-X square are equal. Their square itself derives containment. -/
theorem lift_eq_of_over_X
    (hπ₀ : IsBlowupAlong n₀ C₀ π₀) (hπ₁ : IsBlowupAlong n₁ C₁ π₁)
    (hW₀ : IsComplexAnalyticSubset (n := n₀) W₀)
    (hW₁ : IsComplexAnalyticSubset (n := n₁) W₁)
    (j₀ : ofClosedAnalytic W₀ hW₀ ⟶ X) (j₁ : ofClosedAnalytic W₁ hW₁ ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion j₁.hom.left]
    (hJ₀ : ∀ y : W₀,
      Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) y.val) =
          nativePulledIdealStalkIdeal j₀.hom.left B b y)
    (hJ₁ : ∀ y : W₁,
      Ideal.map ((actualSubspaceInclusion (n := n₁) W₁).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₁) C₁) y.val) =
          nativePulledIdealStalkIdeal j₁.hom.left B b y)
    (A : SourceReducedComplexSpace)
    (r : A ⟶ geometricSource hπ₀ hW₀)
    [hr : LocallyRingedSpace.IsOpenImmersion r.hom.left]
    (L₁ L₂ : A ⟶ geometricSource hπ₁ hW₁)
    (h₁ : L₁ ≫ geometricProjectionMorphism hπ₁ hW₁ ≫ j₁ = r ≫ geometricProjectionMorphism hπ₀ hW₀ ≫ j₀)
    (h₂ : L₂ ≫ geometricProjectionMorphism hπ₁ hW₁ ≫ j₁ = r ≫ geometricProjectionMorphism hπ₀ hW₀ ≫ j₀) : L₁ = L₂ := by
  have hrange : range (r ≫ geometricProjectionMorphism hπ₀ hW₀ ≫ j₀).hom.left.base ⊆ range j₁.hom.left.base := by
    rintro x ⟨u,rfl⟩
    refine ⟨(geometricProjectionMorphism hπ₁ hW₁).hom.left.base (L₁.hom.left.base u),?_⟩
    exact congrArg (fun H => H.hom.left.base u) h₁
  obtain ⟨L,_,hLu⟩ := exists_unique_lift_over_X B b hπ₀ hπ₁ hW₀ hW₁ j₀ j₁ hJ₀ hJ₁ A r (hr := hr) hrange
  exact (hLu L₁ h₁).trans (hLu L₂ h₂).symm

end
end Hironaka.Analytic.Unibranch.EmbeddedGeometricIdealOpenSource
