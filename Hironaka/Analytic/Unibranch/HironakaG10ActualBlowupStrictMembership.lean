import Hironaka.Analytic.Unibranch.HironakaG10StrictChartMembership
import Hironaka.Analytic.Unibranch.OriginalFiniteIdealBlowupUniversal
import Hironaka.Analytic.Unibranch.OriginalFiniteIdealGeometricBlowupUniversal

/-!
# Strict membership from an actual ordinary blowup's own exceptional section

The existing embedded global Cartier producers already construct the regular
generating section. This module specializes them to the same ordinary
finite-ideal source objects and consumes their whole-ideal dictionaries in
the single-generator strict-membership criterion. No generator, span equality,
or regularity certificate is supplied by the caller. This is an integration
of existing geometric producers, not a new blowup construction.

Blueprint: `hironaka-g10-actual-blowup-strict-membership.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10ActualBlowupStrictMembership

open Hironaka HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealSheaf HironakaG10ChowArtinReesCentre
  HironakaG10ChowTrackedDatum HironakaG10StrictChartMembership

noncomputable section

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType]

/-- On the actual ordinary dense-unit-locus blowup, one actual source section
provides regular exceptional equations and the strict-membership criterion
for every stalk ideal on a whole neighbourhood. -/
theorem exists_local_projection_strict_criterion
    (hDense : Dense {x : X.obj.left |
      LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
    (x : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left) :
    ∃ (U : Opens (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left.toTopCat)
      (_hxU : x ∈ U)
      (s : nativePulledIdealSectionIdeal
        (OriginalFiniteIdealBlowup.projectionMorphism B b hDense).hom.left B b U),
      ∀ (y : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left) (hy : y ∈ U),
        let G := (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left.presheaf.germ U y hy s.val
        let D := LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
          ((OriginalFiniteIdealBlowup.projectionMorphism B b hDense).hom.left.base y))
        IsRegular G ∧
          Ideal.map ((OriginalFiniteIdealBlowup.projectionMorphism B b hDense).hom.left.stalkMap y).hom D =
            Ideal.span {G} ∧
          ∀ I : Ideal (X.obj.left.presheaf.stalk
              ((OriginalFiniteIdealBlowup.projectionMorphism B b hDense).hom.left.base y)),
            OnStrictTransform (OriginalFiniteIdealBlowup.projectionMorphism B b hDense) y I D ↔
              strictIdeal ((OriginalFiniteIdealBlowup.projectionMorphism B b hDense).hom.left.stalkMap y).hom
                I D G ≠ ⊤ := by
  have hgen :
      ∀ x : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left,
      ∃ (U : Opens (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left.toTopCat)
        (_hxU : x ∈ U)
        (s : nativePulledIdealSectionIdeal
          (OriginalFiniteIdealBlowup.projectionMorphism B b hDense).hom.left B b U),
        ∀ (y : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left) (hy : y ∈ U),
          nativePulledIdealStalkIdeal
              (OriginalFiniteIdealBlowup.projectionMorphism B b hDense).hom.left B b y =
            Ideal.span {(OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left.presheaf.germ U y hy s.val} ∧
          IsRegular ((OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left.presheaf.germ U y hy s.val) := by
    unfold OriginalFiniteIdealBlowup.projectionMorphism
    exact EmbeddedIdealBlowupGlobalCartier.exists_local_projection_ideal_generator _ _ _ B b _ _
  obtain ⟨U,hxU,s,hs⟩ := hgen x
  refine ⟨U,hxU,s,?_⟩
  intro y hy
  dsimp only
  obtain ⟨hspan,hreg⟩ := hs y hy
  exact ⟨hreg,hspan,fun I => onStrictTransform_iff_of_generator
    (OriginalFiniteIdealBlowup.projectionMorphism B b hDense) y I _ _ hreg hspan⟩

/-- The actual geometric finite-ideal blowup has the same local strict-ideal
criterion without target density or source surjectivity hypotheses. -/
theorem exists_local_geometric_projection_strict_criterion
    (x : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left) :
    ∃ (U : Opens (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.toTopCat)
      (_hxU : x ∈ U)
      (s : nativePulledIdealSectionIdeal
        (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b U),
      ∀ (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left) (hy : y ∈ U),
        let G := (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ U y hy s.val
        let D := LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
          ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y))
        IsRegular G ∧
          Ideal.map ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.stalkMap y).hom D =
            Ideal.span {G} ∧
          ∀ I : Ideal (X.obj.left.presheaf.stalk
              ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y)),
            OnStrictTransform (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b) y I D ↔
              strictIdeal ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.stalkMap y).hom
                I D G ≠ ⊤ := by
  have hgen :
      ∀ x : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left,
      ∃ (U : Opens (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.toTopCat)
        (_hxU : x ∈ U)
        (s : nativePulledIdealSectionIdeal
          (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b U),
        ∀ (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left) (hy : y ∈ U),
          nativePulledIdealStalkIdeal
              (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b y =
            Ideal.span {(OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ U y hy s.val} ∧
          IsRegular ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ U y hy s.val) := by
    unfold OriginalFiniteIdealGeometricBlowup.projectionMorphism
    exact EmbeddedGeometricIdealGlobalCartier.exists_local_projection_ideal_generator _ _ _ B b _
  obtain ⟨U,hxU,s,hs⟩ := hgen x
  refine ⟨U,hxU,s,?_⟩
  intro y hy
  dsimp only
  obtain ⟨hspan,hreg⟩ := hs y hy
  exact ⟨hreg,hspan,fun I => onStrictTransform_iff_of_generator
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b) y I _ _ hreg hspan⟩

end

end Hironaka.Analytic.Unibranch.HironakaG10ActualBlowupStrictMembership
