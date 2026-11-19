import Hironaka.Analytic.Unibranch.HironakaG10NfStrictCanonicalPre
import Hironaka.Analytic.Unibranch.HironakaG10NfStrictZero
import Hironaka.Analytic.Unibranch.HironakaG10NfStrictFused
import Hironaka.Analytic.Unibranch.HironakaG10NfFibreDescent
import Hironaka.Analytic.Unibranch.HironakaG10NfFibreGlue
import Hironaka.Analytic.Unibranch.HironakaG10NfJointPivotCanonical
import Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalBaseSquare
import Hironaka.Analytic.Unibranch.HironakaG10NfStrictMembership
import Hironaka.Analytic.Unibranch.HironakaG10NfFlatTransport

/-!
# H3.4 (`strict`, `strict₀` on the canonical chart)

Lane G10H3, run 0081 (fields `strict`, `strict₀` of `HironakaG10NfGeoFibreModel.GeoFibreModel`).  Canonical setting of
`HironakaG10SbCanonicalStrictTorsion`.  Instances of the fused generic lemmas `HironakaG10NfStrictFused.strict_generic`
and `HironakaG10NfStrictZero.strict0_generic`, fed only with morphisms and morphism squares
(`sourceProjection`, `HironakaG10GlCanonicalBaseSquare.chart_square`) — feeding stalk-level squares is slow, since the
stalk-level statements of different modules carry different (defeq) instance constants.  The statements use the
`IsFiniteType` instance of `HironakaG10NfGeoFibreModel` (so that they are literally its fields) and the witness of
`strict` is read off the fused lemma.

* `mem_strict_of_le` — a pair with `Tors ⊆ ψ(𝔪)` lies on the strict transform;
* `strict_field`, `strict0_field` — the fields `strict` and `strict₀`.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10NfStrictCanonical

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeScalar BlowupConstruction BlowupStrictSubmanifold
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowup
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation
  Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}

attribute [local instance] Hironaka.Analytic.Unibranch.HironakaG10NfGeoFibreModel.instIsFiniteTypeOpensCarrierCarrierCommRingCatLeftLocallyRingedSpaceObjOverComplexPointSourceReducedComplexSpacePropertyNativePulledIdealModuleLeftHomFullSubcategory

variable (t : CanonicalTargetGraph B b y)
  (c : CanonicalCompatibleSourceGraph B b F x t)
  (g : CanonicalSquareGeometry B b F x t c)
  (d : CanonicalNormalSectionData B b F x t c g)
  (E : SameCanonicalExplicitProductModels B b F x t c g d)
  (M : AllAmbientMonomialLiftData B b F x t c g d E)
  (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank))
  (hvj : v (j.natAdd c.embedding.dim) = 0)
  (h0 : (0 : ComplexModel (c.embedding.dim+t.rank)) ∈ targetOpen B b F x t c g d E j v)


/-- A pair with a proper torsion bound lies on the strict transform. -/
theorem mem_strict_of_le (w : HironakaG10NfFibreCover.W B b F x t c g d E j v hvj h0)
    (hT : (pivotTorsion (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
        (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w.1) ≤
      Ideal.map (HironakaG10NfJointPivotCanonical.psi B b F x t c g d E M j v hvj w.1 w.2.2.2)
        (IsLocalRing.maximalIdeal _)) :
    w.1 ∈ HironakaG10NfSourceSquare.strict B b F x t c g d E j v :=
  HironakaG10NfStrictMembership.mem_strict_of_pivotTorsion_ne_top c.embedding.dim t.rank j (fun i => v i)
    (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
    (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) h0
    (originalGraph_analytic B b F x t c g d E j v) (actualMap_holomorphic B b F x t c g d E M j v hvj).continuous
    (actual_landing B b F x t c g d E M j v hvj) w.1 w.2.1 (pivotTorsion_ne_top B b F x t c g d E M j v hvj h0 w hT)

/-- **The field `strict` of `GeoFibreModel` on the canonical chart** (`HironakaG10NfStrictFused.strict_generic`
instantiated with morphisms and morphism squares only). -/
theorem strict_field (w : HironakaG10NfFibreCover.W B b F x t c g d E j v hvj h0)
    (hT : pivotTorsion (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
        (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w.1 ≤
      Ideal.map (HironakaG10NfJointPivotCanonical.psi B b F x t c g d E M j v hvj w.1 w.2.2.2)
        (IsLocalRing.maximalIdeal _)) :
    ∃ y'' : (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.left,
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).hom.left.base y'' =
          HironakaG10NfFibreCover.pY B b F x t c g d E j v hvj h0 w ∧
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base y'' =
        HironakaG10NfFibreCover.pT B b F x t c g d E j v hvj h0 w ∧
      Ideal.comap ((OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
          (nativePulledIdealInclusion F.hom.left B b)).hom.left.stalkMap y'').hom
          (HironakaG10ChowFibreChain.fibreIdealAt (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F) y'') ≤
        HironakaG10ChowFibreChain.fibreIdealAt F ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base y'') :=
  by
  have hwS := mem_strict_of_le B b F x t c g d E M j v hvj h0 w hT
  have key :=
      HironakaG10NfStrictFused.strict_generic
        (A := (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
          (nativePulledIdealInclusion F.hom.left B b)).obj.left) E.source.charts t.positive (sourceGraphSet B b F x t c) j v hvj
        (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
        (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j)
        c.analytic h0 (actual_landing B b F x t c g d E M j v hvj)
        (HironakaG10NfFibreGlue.map_source_le_raw B b F x t c g d E j v hvj)
        (sourceCanonicalMap B b F x t c g E.source).hom.left
        (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
          (nativePulledIdealInclusion F.hom.left B b)).hom.left c.chart.hom.left
        (sourceProjection B b F x t c g d E)
        (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left F.hom.left
        (targetChartMap B b F x t c g d E j)
        (chartIso B b F x t c g d E j v hvj).hom rfl (sourceChartMap B b F x t c g d E j) rfl
        (HironakaG10GlCanonicalBaseSquare.chart_square B b F x t c g d E M j v hvj)
        w.1 w.2.1 w.2.2.1 hwS w.2.2.2
        (HironakaG10NfSourceSquare.chart_q_point B b F x t c g d E j v hvj w.1 hwS) hT
        (fun rr hr => fibre_native B b F x t c g d E M j v hvj h0 w rr hr)
  refine ⟨_, ?_, ?_, key⟩
  · exact HironakaG10NfSourceSquare.q_nativePoint B b F x t c g d E j v hvj w.1 hwS
  · exact (HironakaG10GlCanonicalBaseSquare.targetChartMap_targetPoint B b F x t c g d E M j v hvj w.1 hwS).symm

/-- **The field `strict₀` of `GeoFibreModel` on the canonical chart** (flatness transfer through the torsion
readout of the strict stalk). -/
theorem strict0_field (w : HironakaG10NfFibreCover.W B b F x t c g d E j v hvj h0)
    (hT : (pivotTorsion (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
        (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w.1) ≤
      Ideal.map (HironakaG10NfJointPivotCanonical.psi B b F x t c g d E M j v hvj w.1 w.2.2.2)
        (IsLocalRing.maximalIdeal _)) :
    ∃ (y'' : (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.left)
      (hp : (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base y'' =
        HironakaG10NfFibreCover.pT B b F x t c g d E j v hvj h0 w),
      ∀ J₁ : Ideal ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.stalk
          (HironakaG10NfFibreCover.pT B b F x t c g d E j v hvj h0 w)),
        (HironakaG10HirFlatQuotient.quotMap (Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease.fibreStalkMap (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F)
          (HironakaG10NfFibreCover.pT B b F x t c g d E j v hvj h0 w) y'' hp) J₁).Flat →
          (HironakaG10HirFlatQuotient.quotMap ((Ideal.Quotient.mk (pivotTorsion (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
        (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w.1)).comp (HironakaG10NfJointPivotCanonical.psi B b F x t c g d E M j v hvj w.1 w.2.2.2)) J₁).Flat :=
  have hwS := mem_strict_of_le B b F x t c g d E M j v hvj h0 w hT
  ⟨(sourceChartMap B b F x t c g d E j).base ((chartIso B b F x t c g d E j v hvj).hom.base ⟨w.1, hwS⟩),
    (HironakaG10GlCanonicalBaseSquare.targetChartMap_targetPoint B b F x t c g d E M j v hvj w.1 hwS).symm,
    fun J₁ hJ => HironakaG10NfStrictZero.strict0_generic c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
      (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
      (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) h0
      (originalGraph_analytic B b F x t c g d E j v) (actual_landing B b F x t c g d E M j v hvj)
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left
      (chartIso B b F x t c g d E j v hvj).hom (sourceChartMap B b F x t c g d E j)
      (targetChartMap B b F x t c g d E j)
      (HironakaG10GlCanonicalBaseSquare.chart_square B b F x t c g d E M j v hvj)
      w.1 w.2.1 hwS w.2.2.2
      (HironakaG10GlCanonicalBaseSquare.targetChartMap_targetPoint B b F x t c g d E M j v hvj w.1 hwS).symm
      J₁ hJ⟩

end

end Hironaka.Analytic.Unibranch.HironakaG10NfStrictCanonical
