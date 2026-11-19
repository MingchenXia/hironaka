import Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalCoverage
import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotMonomialConjugacy
import Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease
import Hironaka.Resolution.HironakaG10JointNativeScalar

/-!
# N2(b–c): the base-side square of the canonical strict-torsion readout

Lane G10GL, run 0081, item GL-3b/N2 (`work/hironaka-run0081-20261117/G10GL/GL-3b-4-route.md`).  Setting of
`HironakaG10SbCanonicalStrictTorsion`.  At a canonical chart point `w` (on the strict transform, in the local
saturation domain), the target chart point `⟨actualMap w, _⟩` of the canonical target strict chart (no target
recentring is needed: `TargetStalk` is the stalk of the domain of `targetChartMap j`) maps to the image of the native
chart point under the induced map `Bl_{F*B} X ⟶ Bl_B Y`, and

* `square_apply` — a commutative square of locally ringed spaces, on stalks at one point (generic);
* `strictPt`, `targetPoint`, `chartPoint` — the strict chart point, its target chart point `⟨actualMap w, _⟩` and the
  native chart point (`nativePoint_eq_chartPoint`), with `targetChartMap_targetPoint`: the target chart point lies
  under the native chart point (`pivot_native_square`, a copy of `intrinsic_pivot_native_square`);
* `canonicalPsi` — at EVERY source chart point `w` of the fibre-product locus (`actualMap w ∈ targetStrict`, `w` not
  assumed on the strict transform): `𝒪_{Bl_B Y}` at the target chart point → `TargetStalk` → `JointQuotient w`
  (`targetStalkToJoint`);
* `chart_square` — the two routes from the recentred strict chart to `Bl_B Y` agree (strict chart then induced map;
  actual map then target chart);
* `canonical_square_morphisms`, **`canonical_square_joint`** — on stalks at the native chart point: the stalk map of
  the induced map, read through the strict chart (`sourceChartMap`, `chartIso`), equals `jointStrictStalkMap` of
  `targetStalkToJoint` of the target-chart stalk map (`targetStalkToJoint_strict_square`).  These two are stated by
  term with INFERRED type (`linter.defProp` off): elaborating them against a written-out statement costs 7–9 min of
  unification in this namespace, the inferred form 1 min.

No named input.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalBaseSquare

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeIdealMap HironakaG10JointNativeScalar
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialStrictRestriction
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupOriginalPivotObjects
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotMonomialConjugacy
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation
  Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion

/-- A commutative square of locally ringed spaces, on stalks at one point (generic form). -/
theorem square_apply {T S A C D : LocallyRingedSpace.{0}}
    (i₁ : T ⟶ A) (i₂ : A ⟶ C) (ind : C ⟶ S) (m : T ⟶ D) (tc : D ⟶ S)
    (H : i₁ ≫ (i₂ ≫ ind) = m ≫ tc) (t : T)
    (hs : tc.base (m.base t) = ind.base (i₂.base (i₁.base t)))
    (r : S.presheaf.stalk (ind.base (i₂.base (i₁.base t)))) :
    (i₁.stalkMap t).hom ((i₂.stalkMap (i₁.base t)).hom ((ind.stalkMap (i₂.base (i₁.base t))).hom r)) =
      (m.stalkMap t).hom ((tc.stalkMap (m.base t)).hom
        ((eqToHom (congrArg S.presheaf.stalk hs.symm)).hom r)) := by
  have e := Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease.stalkMap_eq_of_eq _ _ H t hs r
  have c1 := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp i₁ (i₂ ≫ ind) t) r
  have c2 := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp i₂ ind (i₁.base t)) r
  have c3 := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp m tc t)
    ((eqToHom (congrArg S.presheaf.stalk hs.symm)).hom r)
  exact (congrArg (i₁.stalkMap t).hom c2).symm.trans (c1.symm.trans (e.trans c3))

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
  (w : sourceDomain B b F x t c g d E j v)
  (hwS : w ∈ realOpenStrictTransform c.embedding.dim t.rank j (fun i => v i)
    (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v))

/-- The canonical chart square on the strict pivot charts (a copy of
`CompatibleCanonicalIdealBlowupIntrinsicPivotMap.intrinsic_pivot_native_square`, whose module is outside the built
closure). -/
theorem pivot_native_square :
    (actualOriginalMonomialStrictMap B b F x t c g d E M j).hom.left ≫
        targetChartMap B b F x t c g d E j =
      sourceChartMap B b F x t c g d E j ≫
        (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left := by
  have h := congrArg (fun f => f.hom.left)
    (monomial_full_strict_square B b F x t c g d E M j)
  have hC := congrArg (fun f => f.hom.left) E.square.canonical_square
  change (actualOriginalMonomialStrictMap B b F x t c g d E M j).hom.left ≫
      (targetStrictInclusion B b F x t c g d E j).hom.left =
    (sourceStrictInclusion B b F x t c g d E j).hom.left ≫
      (explicitStrictMap B b F x t c g E.target E.source).hom.left at h
  change (sourceCanonicalMap B b F x t c g E.source).hom.left ≫
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left =
    (explicitStrictMap B b F x t c g E.target E.source).hom.left ≫
      (targetCanonicalMap B b t E.target).hom.left at hC
  change (actualOriginalMonomialStrictMap B b F x t c g d E M j).hom.left ≫
      ((targetStrictInclusion B b F x t c g d E j).hom.left ≫
        (targetCanonicalMap B b t E.target).hom.left) =
    ((sourceStrictInclusion B b F x t c g d E j).hom.left ≫
      (sourceCanonicalMap B b F x t c g E.source).hom.left) ≫
        (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left
  rw [← Category.assoc,h,Category.assoc,← hC,← Category.assoc]

/-- The canonical chart point as a point of the actual strict-transform subspace (one elaborated term, shared). -/
abbrev strictPt : actualSubspaceLocallyRingedSpace (n := c.embedding.dim+t.rank)
    (realOpenStrictTransform c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)) :=
  ⟨w, hwS⟩

/-- The target chart point of a canonical chart point on the strict transform. -/
abbrev targetPoint : strictChartCarrier E.target.charts (targetGraphSet B b t) j :=
  ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩

/-- The native chart point, written as the composite of the two chart maps (`nativePoint` unfolded). -/
abbrev chartPoint :
    (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.left :=
  (sourceChartMap B b F x t c g d E j).base
    ((chartIso B b F x t c g d E j v hvj).hom.base (strictPt B b F x t c g d E j v w hwS))

theorem nativePoint_eq_chartPoint :
    nativePoint B b F x t c g d E j v hvj w hwS = chartPoint B b F x t c g d E j v hvj w hwS :=
  rfl

theorem targetPoint_val :
    (targetPoint B b F x t c g d E M j v hvj w hwS).val = actualMap B b F x t c g d E j v hvj w :=
  rfl

theorem monomial_base_chartIso :
    (actualOriginalMonomialStrictMap B b F x t c g d E M j).hom.left.base
        ((chartIso B b F x t c g d E j v hvj).hom.base (strictPt B b F x t c g d E j v w hwS)) =
      targetPoint B b F x t c g d E M j v hvj w hwS :=
  rfl

/-- The target chart point lies under the native chart point. -/
theorem targetChartMap_targetPoint :
    (targetChartMap B b F x t c g d E j).base (targetPoint B b F x t c g d E M j v hvj w hwS) =
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base
        (chartPoint B b F x t c g d E j v hvj w hwS) :=
  congrArg (fun f => f.base ((chartIso B b F x t c g d E j v hvj).hom.base
      (strictPt B b F x t c g d E j v w hwS)))
    (pivot_native_square B b F x t c g d E M j)


/-- **The canonical base map** at a source chart point `w` of the fibre-product locus (`actualMap w` on the target
strict chart; `w` not assumed on the strict transform): the stalk of `Bl_B Y` at the target chart point, read on the
target strict chart (open immersion), followed by the joint target scalar map `targetStalkToJoint`. -/
def canonicalPsi
    (hV : actualMap B b F x t c g d E j v hvj w ∈ targetStrict B b F x t c g d E j) :
    (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.stalk
        ((targetChartMap B b F x t c g d E j).base ⟨actualMap B b F x t c g d E j v hvj w, hV⟩) →+*
      JointQuotient (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
        (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w :=
  (targetStalkToJoint (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
      (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
      (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) w hV).comp
    ((targetChartMap B b F x t c g d E j).stalkMap ⟨actualMap B b F x t c g d E j v hvj w, hV⟩).hom

/-- The two routes from the recentred strict chart to `Bl_B Y` agree. -/
theorem chart_square :
    (chartIso B b F x t c g d E j v hvj).hom ≫ (sourceChartMap B b F x t c g d E j ≫
        (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left) =
      actualSubspaceMap (actualMap_holomorphic B b F x t c g d E M j v hvj)
          (fun _ hx => actual_landing B b F x t c g d E M j v hvj hx) ≫
        targetChartMap B b F x t c g d E j := by
  have hcomp : (chartIso B b F x t c g d E j v hvj).hom ≫
      (actualOriginalMonomialStrictMap B b F x t c g d E M j).hom.left =
        actualSubspaceMap (actualMap_holomorphic B b F x t c g d E M j v hvj)
          (fun _ hx => actual_landing B b F x t c g d E M j v hvj hx) :=
    (actualSubspaceMap_comp (arbitraryCanonicalRecenteredChart E.source.charts j v hvj).contMDiff
      (M.restricted_holomorphic j) _ (monomial_strict_landing B b F x t c g d E M j)).symm
  exact (congrArg (fun k => (chartIso B b F x t c g d E j v hvj).hom ≫ k)
      (pivot_native_square B b F x t c g d E M j).symm).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ targetChartMap B b F x t c g d E j) hcomp))




set_option linter.defProp false in
/-- **The base-side square of the canonical strict chart on stalks** (instance of `square_apply`, type inferred):
at the native chart point, the stalk map of the induced map `Bl_{F*B} X ⟶ Bl_B Y` read through the strict chart
(`sourceChartMap`, then `chartIso`) equals the stalk map of the actual map `actualMap` read through the target strict
chart (`targetChartMap`), after the point transport `targetChartMap_targetPoint`. -/
def canonical_square_morphisms
    (r : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.stalk
        ((OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base
          ((sourceChartMap B b F x t c g d E j).base
            ((chartIso B b F x t c g d E j v hvj).hom.base (strictPt B b F x t c g d E j v w hwS))))) :=
  square_apply (chartIso B b F x t c g d E j v hvj).hom (sourceChartMap B b F x t c g d E j)
    (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left
    (actualSubspaceMap (actualMap_holomorphic B b F x t c g d E M j v hvj)
      (fun _ hx => actual_landing B b F x t c g d E M j v hvj hx))
    (targetChartMap B b F x t c g d E j) (chart_square B b F x t c g d E M j v hvj)
    (strictPt B b F x t c g d E j v w hwS)
    (targetChartMap_targetPoint B b F x t c g d E M j v hvj w hwS) r


set_option linter.defProp false in
/-- **The base-side square of the canonical strict readout** (type inferred): the stalk map of the induced map at the
native chart point, read through the strict chart, is the joint strict stalk map of the canonical base map. -/
def canonical_square_joint
    (h0 : (0 : ComplexModel (c.embedding.dim+t.rank)) ∈ targetOpen B b F x t c g d E j v)
    (hw : w ∈ localDomain c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v) h0
        (originalGraph_analytic B b F x t c g d E j v))
    (r : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.stalk
        ((OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base
          ((sourceChartMap B b F x t c g d E j).base
            ((chartIso B b F x t c g d E j v hvj).hom.base (strictPt B b F x t c g d E j v w hwS))))) :=
  (canonical_square_morphisms B b F x t c g d E M j v hvj w hwS r).trans
    (targetStalkToJoint_strict_square (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j
      (fun i => v i) (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
      (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
      (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) h0
      (originalGraph_analytic B b F x t c g d E j v) (actual_landing B b F x t c g d E M j v hvj) w hw hwS
      (((targetChartMap B b F x t c g d E j).stalkMap
          ((actualSubspaceMap (actualMap_holomorphic B b F x t c g d E M j v hvj)
            (fun _ hx => actual_landing B b F x t c g d E M j v hvj hx)).base
              (strictPt B b F x t c g d E j v w hwS))).hom
        ((eqToHom (congrArg (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.stalk
          (targetChartMap_targetPoint B b F x t c g d E M j v hvj w hwS).symm)).hom r))).symm


end

end Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalBaseSquare
