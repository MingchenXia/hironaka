import Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalFlattener

/-!
# `flat_base` at the chart origin, read at the base point of the new chart (G10H3's `flat_base₀` form)

Lane G10N34, run 0081.  Convenience form of `HironakaG10GlCanonicalFlattener.flat_base_canonical` for lane G10H3's
`HironakaG10NfGeoFibreModel.GeoFibreModel.flat_base₀`: the test ideal `J` lives at the image `π_T(Q)` of the target
chart point (`Q = targetChartMap ⟨actualMap w₀, hV₀⟩`), the old fibre map is read through the square
`F x = π_T(Q)`, and the base change is the bare stalk map of `π_T` at `Q`.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalFlatBase

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict HironakaRealOpenGeometricStrictSaturation
  HironakaG10JointStrictTorsion HironakaG10JointNativeScalar HironakaG10HirFlatQuotient
  BlowupConstruction BlowupStrictSubmanifold
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialStrictRestriction
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease Hironaka.Analytic.Unibranch.HironakaG10GlChartPresentation
  Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalFlattener

noncomputable section

/-- Transport of a base change of flatness along the point of the base. -/
theorem flat_transport {T S Bl : LocallyRingedSpace.{0}} {C : Type*} [CommRing C] (Fm : T ⟶ S) (σm : Bl ⟶ S)
    (x₁ : T) (Q : Bl) (ψ : Bl.presheaf.stalk Q →+* C) (y : S) (h₁ : Fm.base x₁ = y) (h₂ : σm.base Q = y)
    (H : ∀ J₀ : Ideal (S.presheaf.stalk (Fm.base x₁)),
      (quotMap (lrsFibreMap Fm (Fm.base x₁) x₁ rfl) J₀).Flat →
        (quotMap ψ (J₀.map (lrsFibreMap σm (Fm.base x₁) Q (h₂.trans h₁.symm)))).Flat)
    (J : Ideal (S.presheaf.stalk y)) (hJ : (quotMap (lrsFibreMap Fm y x₁ h₁) J).Flat) :
    (quotMap ψ (J.map (lrsFibreMap σm y Q h₂))).Flat := by
  subst h₁
  exact H J hJ

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

variable (t : CanonicalTargetGraph B b y)
  (c : CanonicalCompatibleSourceGraph B b F x t)
  (g : CanonicalSquareGeometry B b F x t c)
  (d : CanonicalNormalSectionData B b F x t c g)
  (E : SameCanonicalExplicitProductModels B b F x t c g d)
  (M : AllAmbientMonomialLiftData B b F x t c g d E)
  (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank))
  (hvj : v (j.natAdd c.embedding.dim) = 0)

include M in
/-- **`flat_base` at the chart origin, read at `π_T(Q)`** (the form of G10H3's `GeoFibreModel.flat_base₀`). -/
theorem flat_base_geo (w₀ : sourceDomain B b F x t c g d E j v)
    (hV₀ : actualMap B b F x t c g d E j v hvj w₀ ∈ targetStrict B b F x t c g d E j)
    (hsrc : (blowupProj (c.embedding.dim+t.rank) {q : c.subdomain × ComplexModel t.rank | q.2 = 0}
      (arbitraryCanonicalRecenteredChart E.source.charts j v hvj w₀).val).1 = c.point.val.1)
    (hsq : F.hom.left.base x = (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
      ((targetChartMap B b F x t c g d E j).base ⟨actualMap B b F x t c g d E j v hvj w₀, hV₀⟩))
    (J : Ideal (Y.obj.left.presheaf.stalk ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
      ((targetChartMap B b F x t c g d E j).base ⟨actualMap B b F x t c g d E j v hvj w₀, hV₀⟩))))
    (hJ : (quotMap (fibreStalkMap F _ x hsq) J).Flat) :
    (quotMap ((targetStalkToJoint (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
          (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
          (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
          (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) w₀ hV₀).comp
        ((targetChartMap B b F x t c g d E j).stalkMap ⟨actualMap B b F x t c g d E j v hvj w₀, hV₀⟩).hom)
      (Ideal.map ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.stalkMap
          ((targetChartMap B b F x t c g d E j).base ⟨actualMap B b F x t c g d E j v hvj w₀, hV₀⟩)).hom J)).Flat :=
  flat_transport F.hom.left (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left x
    ((targetChartMap B b F x t c g d E j).base ⟨actualMap B b F x t c g d E j v hvj w₀, hV₀⟩) _ _ hsq rfl
    (fun J₀ hJ₀ => flat_base_canonical B b F x t c g d E M j v hvj w₀ hV₀ hsrc hsq J₀ (fun _ => hJ₀)) J hJ

end

end Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalFlatBase
