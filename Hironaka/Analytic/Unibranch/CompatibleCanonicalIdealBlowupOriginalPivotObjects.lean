import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRestrictions
import Hironaka.Analytic.ClosureDifferenceAnalytic
import Hironaka.Analytic.AnalyticSubsetPreimage
import Mathlib.Topology.Compactness.Paracompact

/-! Genuine ORIGINAL objects on SAME literal intrinsic canonical pivot opens.
Blueprint FIRST. Actual strict-chart analyticity and full native Iso transport
prove the original source property; no arbitrary-open paracompactness or incoming
future property/Iso/square packet. Ordinary643 ONCE,336 model helper SAME E.
FIRST UnitA only: no restrictedF_j/monomial square/07c.6 closure. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupOriginalPivotObjects
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka BlowupConstruction BlowupFlatCoordinates BlowupStrictSubmanifold
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  SourceReducedComplexSpace EmbeddedGeometricBlowup OriginalFiniteIdealGraphChart
  CompatibleCanonicalIdealBlowupSquareCharts CompatibleCanonicalIdealBlowupNormalSections
  CompatibleCanonicalIdealBlowupExplicitProductCharts CompatibleCanonicalIdealBlowupMonomialLift
  CompatibleCanonicalIdealBlowupPivotOpenRanges CompatibleCanonicalIdealBlowupPivotOpenRestrictions
open scoped ProductComplexManifold

-- A generic transport helper; main ordinary endpoint supplies its actual Iso internally.
private def nativeIsoHomeomorph {S T : LocallyRingedSpace.{0}} (e : S ≅ T) : S ≃ₜ T where
  toFun := e.hom.base
  invFun := e.inv.base
  left_inv z := by
    have h := congrArg (fun k => k.base z) e.hom_inv_id
    exact h
  right_inv z := by
    have h := congrArg (fun k => k.base z) e.inv_hom_id
    exact h
  continuous_toFun := e.hom.base.hom.continuous
  continuous_invFun := e.inv.base.hom.continuous

theorem original_property_of_native_iso
    (A : SourceReducedComplexSpace) (T : LocallyRingedSpace.{0})
    (qT : T ⟶ complexPoint) (e : A.obj.left ≅ T)
    (he : e.hom ≫ qT = A.obj.hom) :
    sourceReducedComplexSpaceProperty (Over.mk qT) := by
  let : T2Space A.obj.left := A.property.1
  let h := nativeIsoHomeomorph e
  refine ⟨h.symm.isEmbedding.t2Space,h.paracompactSpace_iff.mp A.property.2.1,?_⟩
  intro z
  obtain ⟨n,U,C,hC,i,hi,hip,c,hc⟩ := A.property.2.2 (e.inv.base z)
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  refine ⟨n,U,C,hC,i ≫ e.hom,inferInstance,?_,c,?_⟩
  · change (i ≫ e.hom) ≫ qT = (modelOver U C).hom
    exact (Category.assoc i e.hom qT).trans
      ((congrArg (fun k => i ≫ k) he).trans hip)
  · change e.hom.base (i.base c) = z
    rw [hc]
    exact LocallyRingedSpace.iso_inv_base_hom_base_apply e z

section StrictCharts
variable {n r : ℕ} {P : Type} [TopologicalSpace P]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]

-- PUBLIC closure-difference + analytic preimage + genuine open trace; no private theorem.
theorem strict_chart_analytic (a : ProductNormalCharts n r P) (hr : 0 < r)
    (W : Set (P × ComplexModel r)) (hW : IsComplexAnalyticSubset (n := n+r) W)
    (j : Fin r) :
    IsComplexAnalyticSubset (n := n+r) (strictChartCarrier a W j) := by
  let hπ := explicitProductPredicate (n := n) (P := P) hr
  have hC := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
  have hStrict : IsComplexAnalyticSubset (n := n+r) (actualStrictCarrier (n := n) W) := by
    simpa only [actualStrictCarrier,geoStrictTransform,preimage_sdiff] using
      ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff
        (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff hW)
        (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff hC)
  exact AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hStrict (strictChartAmbientOpen a j)
end StrictCharts

section SameCanonical
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

-- These original objects' native LRS and point maps are DEFINITIONALLY those in336.
def targetStrictOriginal (j : Fin t.rank) : SourceReducedComplexSpace :=
  SourceReducedComplexSpace.ofClosedAnalytic
    (strictChartCarrier E.target.charts (targetGraphSet B b t) j)
    (strict_chart_analytic E.target.charts t.positive (targetGraphSet B b t) t.analytic j)

def sourceStrictOriginal (j : Fin t.rank) : SourceReducedComplexSpace :=
  SourceReducedComplexSpace.ofClosedAnalytic
    (strictChartCarrier E.source.charts (sourceGraphSet B b F x t c) j)
    (strict_chart_analytic E.source.charts t.positive (sourceGraphSet B b F x t c) c.analytic j)

-- Literal maps on the same old quotient-subspace inclusions, bundled using their
-- existing full complex-point triangle. These are definition headers, not new assumptions.
def targetStrictInclusion (j : Fin t.rank) :
    targetStrictOriginal B b F x t c g d E j ⟶ explicitTarget B b t :=
  ObjectProperty.homMk (Over.homMk
    (strictChartInclusion E.target.charts (targetGraphSet B b t) j)
    (actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)))

def sourceStrictInclusion (j : Fin t.rank) :
    sourceStrictOriginal B b F x t c g d E j ⟶ explicitSource B b F x t c :=
  ObjectProperty.homMk (Over.homMk
    (strictChartInclusion E.source.charts (sourceGraphSet B b F x t c) j)
    (actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)))

-- Proof-only properties. They are OUTPUT, derived from actual original strict
-- objects and the same336 Iso; no such property is an ordinary caller input.
structure OriginalPivotSpaceProperties : Prop where
  target : ∀ j : Fin t.rank,
    sourceReducedComplexSpaceProperty (Over.mk
      (targetPivotInclusion B b F x t c g d E j ≫
        (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.hom))
  source : ∀ j : Fin t.rank,
    sourceReducedComplexSpaceProperty (Over.mk
      (sourcePivotInclusion B b F x t c g d E j ≫
        (OriginalFiniteIdealGeometricBlowup.sourceObject
          (nativePulledIdealModule F.hom.left B b)
          (nativePulledIdealInclusion F.hom.left B b)).obj.hom))

def targetOriginalPivot (H : OriginalPivotSpaceProperties B b F x t c g d E)
    (j : Fin t.rank) : SourceReducedComplexSpace :=
  ⟨Over.mk (targetPivotInclusion B b F x t c g d E j ≫
    (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.hom), H.target j⟩

def sourceOriginalPivot (H : OriginalPivotSpaceProperties B b F x t c g d E)
    (j : Fin t.rank) : SourceReducedComplexSpace :=
  ⟨Over.mk (sourcePivotInclusion B b F x t c g d E j ≫
    (OriginalFiniteIdealGeometricBlowup.sourceObject
      (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.hom), H.source j⟩

def targetOriginalInclusion (H : OriginalPivotSpaceProperties B b F x t c g d E)
    (j : Fin t.rank) : targetOriginalPivot B b F x t c g d E H j ⟶
      OriginalFiniteIdealGeometricBlowup.sourceObject B b :=
  ObjectProperty.homMk (Over.homMk (targetPivotInclusion B b F x t c g d E j) rfl)

def sourceOriginalInclusion (H : OriginalPivotSpaceProperties B b F x t c g d E)
    (j : Fin t.rank) : sourceOriginalPivot B b F x t c g d E H j ⟶
      OriginalFiniteIdealGeometricBlowup.sourceObject
        (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b) :=
  ObjectProperty.homMk (Over.homMk (sourcePivotInclusion B b F x t c g d E j) rfl)

-- Actual isomorphism data are Type-valued. Both original objects on the right
-- have LITERALLY the canonical restriction LRS and structural map, by definition.
structure OriginalPivotObjectData where
  restrictions : SameCanonicalPivotLiteralRestrictionData B b F x t c g d E
  properties : OriginalPivotSpaceProperties B b F x t c g d E
  target_iso : ∀ j : Fin t.rank, targetStrictOriginal B b F x t c g d E j ≅
    targetOriginalPivot B b F x t c g d E properties j
  source_iso : ∀ j : Fin t.rank, sourceStrictOriginal B b F x t c g d E j ≅
    sourceOriginalPivot B b F x t c g d E properties j
  target_native_hom : ∀ j : Fin t.rank,
    (target_iso j).hom.hom.left = (restrictions.target j).iso.hom
  target_native_inv : ∀ j : Fin t.rank,
    (target_iso j).inv.hom.left = (restrictions.target j).iso.inv
  source_native_hom : ∀ j : Fin t.rank,
    (source_iso j).hom.hom.left = (restrictions.source j).iso.hom
  source_native_inv : ∀ j : Fin t.rank,
    (source_iso j).inv.hom.left = (restrictions.source j).iso.inv

-- Exact model helper: SAME actual E; derives336 itself, no incoming Iso/property packet.
theorem original_pivot_objects_of_models :
    Nonempty (OriginalPivotObjectData B b F x t c g d E) := by
  classical
  obtain ⟨R⟩ := pivot_literal_restrictions_of_models B b F x t c g d E
  have hT (j : Fin t.rank) : sourceReducedComplexSpaceProperty (Over.mk
      (targetPivotInclusion B b F x t c g d E j ≫
        (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.hom)) :=
    original_property_of_native_iso (targetStrictOriginal B b F x t c g d E j)
      (targetPivotRestriction B b F x t c g d E j) _
      (R.target j).iso (R.target_point j).hom_point
  have hS (j : Fin t.rank) : sourceReducedComplexSpaceProperty (Over.mk
      (sourcePivotInclusion B b F x t c g d E j ≫
        (OriginalFiniteIdealGeometricBlowup.sourceObject
          (nativePulledIdealModule F.hom.left B b)
          (nativePulledIdealInclusion F.hom.left B b)).obj.hom)) :=
    original_property_of_native_iso (sourceStrictOriginal B b F x t c g d E j)
      (sourcePivotRestriction B b F x t c g d E j) _
      (R.source j).iso (R.source_point j).hom_point
  let H : OriginalPivotSpaceProperties B b F x t c g d E := ⟨hT,hS⟩
  let eT (j : Fin t.rank) : targetStrictOriginal B b F x t c g d E j ≅
      targetOriginalPivot B b F x t c g d E H j :=
    ObjectProperty.isoMk sourceReducedComplexSpaceProperty
      (Over.isoMk (R.target j).iso (R.target_point j).hom_point)
  let eS (j : Fin t.rank) : sourceStrictOriginal B b F x t c g d E j ≅
      sourceOriginalPivot B b F x t c g d E H j :=
    ObjectProperty.isoMk sourceReducedComplexSpaceProperty
      (Over.isoMk (R.source j).iso (R.source_point j).hom_point)
  exact ⟨{
    restrictions := R
    properties := H
    target_iso := eT
    source_iso := eS
    target_native_hom := fun _ => rfl
    target_native_inv := fun _ => rfl
    source_native_hom := fun _ => rfl
    source_native_inv := fun _ => rfl }⟩
theorem target_original_iso_inclusion
    (O : OriginalPivotObjectData B b F x t c g d E) (j : Fin t.rank) :
    (O.target_iso j).hom ≫ targetOriginalInclusion B b F x t c g d E O.properties j =
      targetStrictInclusion B b F x t c g d E j ≫ targetCanonicalMap B b t E.target := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change (O.target_iso j).hom.hom.left ≫ targetPivotInclusion B b F x t c g d E j =
    strictChartInclusion E.target.charts (targetGraphSet B b t) j ≫ (targetCanonicalMap B b t E.target).hom.left
  rw [O.target_native_hom j]
  exact (O.restrictions.target j).hom_fac

theorem source_original_iso_inclusion
    (O : OriginalPivotObjectData B b F x t c g d E) (j : Fin t.rank) :
    (O.source_iso j).hom ≫ sourceOriginalInclusion B b F x t c g d E O.properties j =
      sourceStrictInclusion B b F x t c g d E j ≫ sourceCanonicalMap B b F x t c g E.source := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change (O.source_iso j).hom.hom.left ≫ sourcePivotInclusion B b F x t c g d E j =
    strictChartInclusion E.source.charts (sourceGraphSet B b F x t c) j ≫
      (sourceCanonicalMap B b F x t c g E.source).hom.left
  rw [O.source_native_hom j]
  exact (O.restrictions.source j).hom_fac

theorem target_original_inv_inclusion
    (O : OriginalPivotObjectData B b F x t c g d E) (j : Fin t.rank) :
    (O.target_iso j).inv ≫ targetStrictInclusion B b F x t c g d E j ≫
        targetCanonicalMap B b t E.target =
      targetOriginalInclusion B b F x t c g d E O.properties j := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change (O.target_iso j).inv.hom.left ≫
      (strictChartInclusion E.target.charts (targetGraphSet B b t) j ≫
        (targetCanonicalMap B b t E.target).hom.left) = targetPivotInclusion B b F x t c g d E j
  rw [O.target_native_inv j]
  exact (O.restrictions.target j).inv_fac

theorem source_original_inv_inclusion
    (O : OriginalPivotObjectData B b F x t c g d E) (j : Fin t.rank) :
    (O.source_iso j).inv ≫ sourceStrictInclusion B b F x t c g d E j ≫
        sourceCanonicalMap B b F x t c g E.source =
      sourceOriginalInclusion B b F x t c g d E O.properties j := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change (O.source_iso j).inv.hom.left ≫
      (strictChartInclusion E.source.charts (sourceGraphSet B b F x t c) j ≫
        (sourceCanonicalMap B b F x t c g E.source).hom.left) = sourcePivotInclusion B b F x t c g d E j
  rw [O.source_native_inv j]
  exact (O.restrictions.source j).inv_fac

theorem target_original_iso_point
    (O : OriginalPivotObjectData B b F x t c g d E) (j : Fin t.rank) :
    (O.target_iso j).hom.hom.left ≫
        (targetOriginalPivot B b F x t c g d E O.properties j).obj.hom =
      (targetStrictOriginal B b F x t c g d E j).obj.hom :=
  Over.w (O.target_iso j).hom.hom

theorem source_original_iso_point
    (O : OriginalPivotObjectData B b F x t c g d E) (j : Fin t.rank) :
    (O.source_iso j).hom.hom.left ≫
        (sourceOriginalPivot B b F x t c g d E O.properties j).obj.hom =
      (sourceStrictOriginal B b F x t c g d E j).obj.hom :=
  Over.w (O.source_iso j).hom.hom

theorem target_original_inv_point
    (O : OriginalPivotObjectData B b F x t c g d E) (j : Fin t.rank) :
    (O.target_iso j).inv.hom.left ≫ (targetStrictOriginal B b F x t c g d E j).obj.hom =
      (targetOriginalPivot B b F x t c g d E O.properties j).obj.hom :=
  Over.w (O.target_iso j).inv.hom

theorem source_original_inv_point
    (O : OriginalPivotObjectData B b F x t c g d E) (j : Fin t.rank) :
    (O.source_iso j).inv.hom.left ≫ (sourceStrictOriginal B b F x t c g d E j).obj.hom =
      (sourceOriginalPivot B b F x t c g d E O.properties j).obj.hom :=
  Over.w (O.source_iso j).inv.hom

end SameCanonical

section OrdinaryCaller
variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

theorem exists_same_canonical_original_pivot_objects
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (hxy : F.hom.left.base x =
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y) :
    ∃ (t : CanonicalTargetGraph B b y)
      (c : CanonicalCompatibleSourceGraph B b F x t)
      (g : CanonicalSquareGeometry B b F x t c)
      (d : CanonicalNormalSectionData B b F x t c g)
      (E : SameCanonicalExplicitProductModels B b F x t c g d)
      (_M : AllAmbientMonomialLiftData B b F x t c g d E),
      Nonempty (OriginalPivotObjectData B b F x t c g d E) := by
  obtain ⟨t,c,g,d,E,⟨M⟩⟩ := exists_same_canonical_allambient_monomial_lift B b F x y hxy
  exact ⟨t,c,g,d,E,M,original_pivot_objects_of_models B b F x t c g d E⟩
end OrdinaryCaller

end
end Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupOriginalPivotObjects
