import Hironaka.Analytic.Unibranch.HironakaG10GlPresentationCentre
import Hironaka.Analytic.Unibranch.HironakaG10GlPresentationStage
import Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalFlattener
import Hironaka.Analytic.Unibranch.HironakaG10GlOffCentrePresentation
import Hironaka.Analytic.Unibranch.HironakaG10NfN5

/-!
# `hpres` and Lemma 4.4.5: pulled torsion presentations at every point of the strict source

Lane G10HP, run 0081 (continuing lane G10GL: item GL-3b, the `hpres` assembly, and GL-5).  Hironaka 1975, Lemma 4.4.5,
proof (printed pp. 537–538): the strict transform is the fibre product modulo its exceptional torsion ((4.3.1),
p. 535), and the flattener commutes with base change (Th. 2.5).  Assembly:

* `hpres_of_flattener` — the `hpres` binder of `HironakaG10GlOffCentrePresentation.hT_of_presentation_centre`
  (= `HironakaG10FinalAssembly.PresentationsOverCentre`, verbatim) from the flattener field at the canonical chart
  points (`hfl`, in the exact form of `HironakaG10GlCanonicalFlattener.isFlattenerIdeal_canonical`): the canonical
  presentations over the geometric blowup (`HironakaG10GlPresentationCentre.exists_genPresentation`) moved to the
  native blowup (`HironakaG10GlPresentationStage.hpres_of_genPresentation`, lane G10S1);
* `hT_of_flattener`, `hi_of_flattener` — GL-5: Lemma 4.4.5 (`hT`) and Hironaka's (i) from it, with the native N5
  (`HironakaG10NfN5.hN5`);
* **`hpres`**, **`hi`**, **`hT_of_fibreComparison`** — the same with G10N34's proved flattener field: `hpres` and
  `hi` are unconditional; `hT` needs only the fibre comparison `hfib` (lanes G10H3/G10FI).

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry Filter
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10GlPresentationStep

open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10GlLeavingContradiction Hironaka.Analytic.Unibranch.HironakaG10GlStrictFlatAssembly
  Hironaka.Analytic.Unibranch.HironakaG10SbBlowupComparison Hironaka.Analytic.Unibranch.HironakaG10GlStepSquare
  Hironaka.Analytic.Unibranch.HironakaG10GlPresentationTransport Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
open Hironaka Hironaka HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealSheaf HironakaG10HirFlatQuotient HironakaG10PNIdealFamily HironakaG10HirIdealGerms
  HironakaG10ChowArtinReesCentre HironakaG10StrictIdealGenerator
  HironakaRealOpenGeometricStrictSaturation HironakaG10JointNativeScalar
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion
  Hironaka.Analytic.Unibranch.HironakaG10GlPresentationCentre Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease
  Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation Hironaka.Analytic.Unibranch.HironakaG10GlOffCentrePresentation
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform Hironaka.Analytic.Unibranch.HironakaG10ChowFibreChain
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10SbLemma445 Hironaka.Analytic.Unibranch.HironakaG10GlPresentationStage

noncomputable section

local instance pulledFiniteType {X Y : SourceReducedComplexSpace}
    (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType] (F : X ⟶ Y) :
    (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

/-- **`hpres` (GL-3b): pulled torsion presentations at every point of the strict source over the centre**, the
`hpres` binder of `HironakaG10GlOffCentrePresentation.hT_of_presentation_centre` (verbatim
`HironakaG10FinalAssembly.PresentationsOverCentre`), from the flattener field at the canonical chart points
(`hfl`: lane G10N34's `isFlattenerIdeal_canonical`, Hironaka 1975 Th. 2.5, in its exact form). -/
theorem hpres_of_flattener
    (hfl : ∀ {X Y : SourceReducedComplexSpace}
      (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
      (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
      [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
      {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
      (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t)
      (g : CanonicalSquareGeometry B b F x t c) (d : CanonicalNormalSectionData B b F x t c g)
      (E : SameCanonicalExplicitProductModels B b F x t c g d) (M : AllAmbientMonomialLiftData B b F x t c g d E)
      (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank)) (hvj : v (j.natAdd c.embedding.dim) = 0)
      (w : sourceDomain B b F x t c g d E j v)
      (hwS : w ∈ realOpenStrictTransform c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v))
      (hbase : F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)) =
        (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
          ((targetChartMap B b F x t c g d E j).base
            ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩))
      (P : Ideal (Y.obj.left.presheaf.stalk (F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)))))
      (_hP : IsPointFlattenerAt F (F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)))
        ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)) rfl P),
      IsFlattenerIdeal
        ((targetStalkToJoint (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
            (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
            (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
            (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) w
            (actual_landing B b F x t c g d E M j v hvj hwS)).comp
          ((targetChartMap B b F x t c g d E j).stalkMap
            ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩).hom)
        (Ideal.map (((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.stalkMap
            ((targetChartMap B b F x t c g d E j).base
              ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩)).hom.comp
          (eqToHom (congrArg Y.obj.left.presheaf.stalk hbase)).hom) P)) :
    ∀ (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left),
      (stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'') ∈ nonunitLocus c.B c.b →
      Nonempty (PulledPresentation s c y'') := by
  refine hpres_of_genPresentation fun s c y'' hc => ?_
  let _ := c.finiteType
  exact exists_genPresentation c.B c.b s.f
    (hfl c.B c.b s.f) y''
    (Eq.mpr (congrArg (· ∈ nonunitLocus c.B c.b) (stepQ_comp_apply s c y'')) hc)

/-- **GL-5: Hironaka's Lemma 4.4.5 (`hT`, the literal binder of the final splice)** from the flattener field at the
canonical chart points (`hfl`, G10N34) and the fibre comparison (`hfib`, lanes G10H3/G10FI), with the proved native
N5 (`HironakaG10NfN5.hN5`). -/
theorem hT_of_flattener
    (hfl : ∀ {X Y : SourceReducedComplexSpace}
      (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
      (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
      [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
      {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
      (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t)
      (g : CanonicalSquareGeometry B b F x t c) (d : CanonicalNormalSectionData B b F x t c g)
      (E : SameCanonicalExplicitProductModels B b F x t c g d) (M : AllAmbientMonomialLiftData B b F x t c g d E)
      (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank)) (hvj : v (j.natAdd c.embedding.dim) = 0)
      (w : sourceDomain B b F x t c g d E j v)
      (hwS : w ∈ realOpenStrictTransform c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v))
      (hbase : F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)) =
        (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
          ((targetChartMap B b F x t c g d E j).base
            ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩))
      (P : Ideal (Y.obj.left.presheaf.stalk (F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)))))
      (_hP : IsPointFlattenerAt F (F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)))
        ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)) rfl P),
      IsFlattenerIdeal
        ((targetStalkToJoint (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
            (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
            (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
            (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) w
            (actual_landing B b F x t c g d E M j v hvj hwS)).comp
          ((targetChartMap B b F x t c g d E j).stalkMap
            ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩).hom)
        (Ideal.map (((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.stalkMap
            ((targetChartMap B b F x t c g d E j).base
              ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩)).hom.comp
          (eqToHom (congrArg Y.obj.left.presheaf.stalk hbase)).hom) P))
    (hfib : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            ∀ᶠ y' in 𝓝 x', y' ∈ Z₁.support →
              ∀ y : s.Y.obj.left, s.f.hom.left.base y = (stepσ s c).hom.left.base y' →
                ∃ y'' : (nextWith s c).Y.obj.left, (stepQ s c).hom.left.base y'' = y ∧
                  (nextWith s c).f.hom.left.base y'' = y' ∧
                  Ideal.comap ((stepQ s c).hom.left.stalkMap y'').hom
                      (fibreIdealAt (nextWith s c).f y'') ≤
                    fibreIdealAt s.f ((stepQ s c).hom.left.base y'')) :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z :=
  hT_of_presentation_centre HironakaG10NfN5.hN5 (hpres_of_flattener hfl) hfib

/-- **GL-5: Hironaka's (i)** (the `hi` binder of `HironakaG10SbLemma445.hT_of_strictFlat_of_upper`) from the flattener
field at the canonical chart points, with the proved native N5. -/
theorem hi_of_flattener
    (hfl : ∀ {X Y : SourceReducedComplexSpace}
      (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
      (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
      [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
      {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
      (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t)
      (g : CanonicalSquareGeometry B b F x t c) (d : CanonicalNormalSectionData B b F x t c g)
      (E : SameCanonicalExplicitProductModels B b F x t c g d) (M : AllAmbientMonomialLiftData B b F x t c g d E)
      (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank)) (hvj : v (j.natAdd c.embedding.dim) = 0)
      (w : sourceDomain B b F x t c g d E j v)
      (hwS : w ∈ realOpenStrictTransform c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v))
      (hbase : F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)) =
        (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
          ((targetChartMap B b F x t c g d E j).base
            ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩))
      (P : Ideal (Y.obj.left.presheaf.stalk (F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)))))
      (_hP : IsPointFlattenerAt F (F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)))
        ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
            (nativePoint B b F x t c g d E j v hvj w hwS)) rfl P),
      IsFlattenerIdeal
        ((targetStalkToJoint (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
            (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
            (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
            (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) w
            (actual_landing B b F x t c g d E M j v hvj hwS)).comp
          ((targetChartMap B b F x t c g d E j).stalkMap
            ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩).hom)
        (Ideal.map (((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.stalkMap
            ((targetChartMap B b F x t c g d E j).base
              ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩)).hom.comp
          (eqToHom (congrArg Y.obj.left.presheaf.stalk hbase)).hom) P)) :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ (U : Opens (nextWith s c).X.obj.left) (hxU : x' ∈ U)
            (sG : (nextWith s c).X.obj.left.presheaf.obj (op U)),
            IsRegular ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG) →
            Ideal.map ((stepσ s c).hom.left.stalkMap x').hom
                (centreIdeal c ((stepσ s c).hom.left.base x')) =
              Ideal.span {(nextWith s c).X.obj.left.presheaf.germ U x' hxU sG} →
            FlatOverAt (nextWith s c).f x'
              (strictIdeal ((stepσ s c).hom.left.stalkMap x').hom
                (germFlattener s.f ((stepσ s c).hom.left.base x'))
                (centreIdeal c ((stepσ s c).hom.left.base x'))
                ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG)) :=
  hi_of_presentation HironakaG10NfN5.hN5 (nonempty_pulledPresentation_of_centre (hpres_of_flattener hfl))

/-! ### With the proved flattener field (lane G10N34) -/

/-- **`hpres` (GL-3b), unconditional: every point of the strict source of every flattening step over the centre has a
pulled torsion presentation** (`HironakaG10FinalAssembly.PresentationsOverCentre`, verbatim). -/
theorem hpres :
    ∀ (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left),
      (stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'') ∈ nonunitLocus c.B c.b →
      Nonempty (PulledPresentation s c y'') :=
  hpres_of_flattener @HironakaG10GlCanonicalFlattener.isFlattenerIdeal_canonical

/-- **Hironaka's (i)** (the `hi` binder of `HironakaG10SbLemma445.hT_of_strictFlat_of_upper`), unconditional. -/
theorem hi :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ (U : Opens (nextWith s c).X.obj.left) (hxU : x' ∈ U)
            (sG : (nextWith s c).X.obj.left.presheaf.obj (op U)),
            IsRegular ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG) →
            Ideal.map ((stepσ s c).hom.left.stalkMap x').hom
                (centreIdeal c ((stepσ s c).hom.left.base x')) =
              Ideal.span {(nextWith s c).X.obj.left.presheaf.germ U x' hxU sG} →
            FlatOverAt (nextWith s c).f x'
              (strictIdeal ((stepσ s c).hom.left.stalkMap x').hom
                (germFlattener s.f ((stepσ s c).hom.left.base x'))
                (centreIdeal c ((stepσ s c).hom.left.base x'))
                ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG)) :=
  hi_of_presentation HironakaG10NfN5.hN5 (nonempty_pulledPresentation_of_centre hpres)

/-- **Hironaka's Lemma 4.4.5 (`hT`, the literal binder of the final splice) from the fibre comparison alone**
(`hfib`, lanes G10H3/G10FI): the presentations and N5 are proved. -/
theorem hT_of_fibreComparison
    (hfib : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            ∀ᶠ y' in 𝓝 x', y' ∈ Z₁.support →
              ∀ y : s.Y.obj.left, s.f.hom.left.base y = (stepσ s c).hom.left.base y' →
                ∃ y'' : (nextWith s c).Y.obj.left, (stepQ s c).hom.left.base y'' = y ∧
                  (nextWith s c).f.hom.left.base y'' = y' ∧
                  Ideal.comap ((stepQ s c).hom.left.stalkMap y'').hom
                      (fibreIdealAt (nextWith s c).f y'') ≤
                    fibreIdealAt s.f ((stepQ s c).hom.left.base y'')) :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z :=
  hT_of_presentation_centre HironakaG10NfN5.hN5 hpres hfib

end

end Hironaka.Analytic.Unibranch.HironakaG10GlPresentationStep
