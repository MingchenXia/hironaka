import Hironaka.Analytic.Unibranch.HironakaG10CanonicalExceptionalOrigin
import Hironaka.Analytic.Unibranch.HironakaG10NfStalkSquare

/-!
# N5.b (S1/S2): the real-open recentred target chart of the geometric blowup and its projection square

Lane G10N5, run 0081 (steps S1/S2 of the N5.b plan in `G10HT/STATUS.md`; also the target side of G10GL's N2).
Setting: a finite-type ideal `b : B ⟶ 𝒪_X` on a reduced complex space `X`, the geometric blowup `Bl_B X`, canonical
target data `t` at a point of `Bl_B X` with an explicit product geometry `e` (open immersion of the explicit strict
transform, `TargetExplicitMapLaws`).  For a pivot `j` and a point `p` of the pivot strict chart with zero pivot
coordinate, with `v` its chart coordinates:

* `chartMap` — the pivot strict chart `strictChartCarrier → Bl_B X` (= `targetChartMap j`, built from `t, e` only);
* `realOpenIso` — the actual reduced model of the real-open strict transform (recentred at `v`) is the pivot strict
  chart model (`original_strict_carrier_conjugacy`); `targetMap := realOpenIso.hom ≫ chartMap j`, an open immersion
  sending the real-open origin to `p` (`targetMap_origin`);
* `baseMap` — the base open immersion `(t.domain ⊇ C ∩ t.domain) → X` of the graph chart;
* `proj` — the ambient representative `w ↦ π(χ w).1` of the blowup map;
* **`square`** — `actualSubspaceMap proj ≫ baseMap = targetMap ≫ π` (from `TargetExplicitMapLaws.projection`).

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10NfTargetChart

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaFiniteSectionProductGraph
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict HironakaRealOpenGeometricStrictSaturation
  BlowupConstruction BlowupStrictSubmanifold
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
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalExceptionalOrigin

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
  (t : CanonicalTargetGraph B b y) (e : TargetExplicitGeometry B b t)

/-- The graph `Γ = {(u, g(u))}` of the canonical target data. -/
abbrev graph : Set (t.domain × ComplexModel t.rank) :=
  productGraph ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier) t.functions

/-- The open immersion of the explicit strict transform, typed on the actual strict carrier. -/
abbrev nativeMap :
    actualSubspaceLocallyRingedSpace (n := t.embedding.dim+t.rank)
      (actualStrictCarrier (n := t.embedding.dim) (graph B b t)) ⟶
      (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left :=
  (targetCanonicalMap B b t e).hom.left

variable (j : Fin t.rank) (p : strictChartCarrier e.charts (graph B b t) j)

/-- The chart coordinates of `p`. -/
abbrev coords : ComplexModel (t.embedding.dim+t.rank) := productChartCoordinates e.charts j p.val

variable (hvj : coords B b t e j p (j.natAdd t.embedding.dim) = 0)

/-- The recentred real-open target open. -/
abbrev targetOpen' : Opens (ComplexModel (t.embedding.dim+t.rank)) :=
  recenteredTargetOpen t.embedding.dim t.rank j (coords B b t e j p) (canonicalTargetOpen e.charts j)

/-- The real-open chart domain. -/
abbrev domain : Opens (ComplexModel (t.embedding.dim+t.rank)) :=
  realOpenChartDomain t.embedding.dim t.rank j (fun i => coords B b t e j p i) (targetOpen' B b t e j p)

/-- The graph read in the recentred target coordinates. -/
abbrev graph' : Set (targetOpen' B b t e j p) :=
  (arbitraryBaseTargetMap t.embedding.dim t.rank j (coords B b t e j p) (canonicalTargetOpen e.charts j)) ⁻¹'
    (coordinateSubset e.charts j (graph B b t))

/-- The real-open strict transform. -/
abbrev strict : Set (domain B b t e j p) :=
  realOpenStrictTransform t.embedding.dim t.rank j (fun i => coords B b t e j p i) (targetOpen' B b t e j p)
    (graph' B b t e j p)

/-- The recentred chart biholomorphism. -/
abbrev chart : domain B b t e j p ≃ₘ⟮𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank)),
    𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank))⟯ productChartOpen e.charts j :=
  arbitraryCanonicalRecenteredChart e.charts j (coords B b t e j p) hvj

theorem mem_strict_iff (w : domain B b t e j p) :
    w ∈ strict B b t e j p ↔ chart B b t e j p hvj w ∈ strictChartCarrier e.charts (graph B b t) j :=
  Set.ext_iff.mp (original_strict_carrier_conjugacy e.charts j (coords B b t e j p) hvj (graph B b t)) w

theorem origin_mem : (0 : ComplexModel (t.embedding.dim+t.rank)) ∈ targetOpen' B b t e j p := by
  have hz := ((productChartDiffeomorph e.charts j) p.val).property
  change BlowupMonomialCharts.monomial t.embedding.dim (j.natAdd t.embedding.dim)
    (coords B b t e j p) ∈ canonicalTargetOpen e.charts j at hz
  change (0 : ComplexModel (t.embedding.dim+t.rank)) +
    BlowupMonomialCharts.monomial t.embedding.dim (j.natAdd t.embedding.dim)
      (coords B b t e j p) ∈ canonicalTargetOpen e.charts j
  simpa using hz

/-- The real-open origin. -/
abbrev origin : domain B b t e j p :=
  realOpenOrigin t.embedding.dim t.rank j (fun i => coords B b t e j p i) (targetOpen' B b t e j p)
    (origin_mem B b t e j p)

theorem chart_origin : chart B b t e j p hvj (origin B b t e j p) = p.val :=
  arbitrary_canonical_origin_eq e.charts j p.val hvj (origin_mem B b t e j p)

include hvj in
theorem origin_mem_strict : origin B b t e j p ∈ strict B b t e j p := by
  rw [mem_strict_iff B b t e j p hvj, chart_origin]
  exact p.property

/-- **S2.**  The actual model of the real-open strict transform is the pivot strict chart model. -/
def realOpenIso :
    actualSubspaceLocallyRingedSpace (n := t.embedding.dim+t.rank) (strict B b t e j p) ≅
      actualSubspaceLocallyRingedSpace (n := t.embedding.dim+t.rank)
        (strictChartCarrier e.charts (graph B b t) j) :=
  actualSubspaceBiholomorphicIso (chart B b t e j p hvj) _ _ (mem_strict_iff B b t e j p hvj)

/-- The origin as a point of the real-open strict transform. -/
abbrev originPt : strict B b t e j p := ⟨origin B b t e j p, origin_mem_strict B b t e j p hvj⟩

theorem realOpenIso_origin : (realOpenIso B b t e j p hvj).hom.base (originPt B b t e j p hvj) = p :=
  Subtype.ext (chart_origin B b t e j p hvj)

/-! ### The base chart and the projection square -/

/-- The base carrier `C ∩ t.domain`. -/
abbrev baseSet : Set t.domain := (Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier

/-- The base open immersion of the graph chart. -/
def baseMap : actualSubspaceLocallyRingedSpace (n := t.embedding.dim) (baseSet B b t) ⟶ X.obj.left :=
  actualOpenSubspaceMap (n := t.embedding.dim) t.embedding.carrier t.domain ≫ t.embedding.map

instance baseMap_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (baseMap B b t) := by
  have : LocallyRingedSpace.IsOpenImmersion t.embedding.map := t.embedding.isOpenImmersion
  unfold baseMap
  infer_instance

/-- The ambient representative of the blowup map in the real-open chart. -/
def proj : domain B b t e j p → t.domain :=
  Prod.fst ∘ (blowupProj (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2=0} ∘
    (Subtype.val ∘ chart B b t e j p hvj))

theorem proj_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank)) 𝓘(ℂ,ComplexModel t.embedding.dim) ∞
      (proj B b t e j p hvj) :=
  ProductComplexManifold.contMDiff_fst.comp (contMDiff_blowupProj.comp
    (contMDiff_subtype_val.comp (chart B b t e j p hvj).contMDiff))

theorem proj_mem (w : domain B b t e j p) (hw : w ∈ strict B b t e j p) :
    proj B b t e j p hvj w ∈ baseSet B b t := by
  have h1 := (mem_strict_iff B b t e j p hvj w).mp hw
  have h2 := geoStrictTransform_subset_preimage contMDiff_blowupProj.continuous t.analytic.isClosed h1
  exact h2.1

/-- The ambient representative as a morphism of actual models. -/
abbrev projMap :
    actualSubspaceLocallyRingedSpace (n := t.embedding.dim+t.rank) (strict B b t e j p) ⟶
      actualSubspaceLocallyRingedSpace (n := t.embedding.dim) (baseSet B b t) :=
  actualSubspaceMap (proj_contMDiff B b t e j p hvj) (proj_mem B b t e j p hvj)

theorem projMap_eq :
    projMap B b t e j p hvj =
      (realOpenIso B b t e j p hvj).hom ≫ strictChartInclusion e.charts (graph B b t) j ≫
        geometricProjection (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive)
          t.analytic.isClosed ≫ (productGraphIso (baseSet B b t) t.functions t.holomorphic).inv := by
  change _ = actualSubspaceMap _ _ ≫ actualSubspaceMap _ _ ≫ actualSubspaceMap _ _ ≫ actualSubspaceMap _ _
  rw [← actualSubspaceMap_comp, ← actualSubspaceMap_comp, ← actualSubspaceMap_comp]


/-- The pivot strict chart of `Bl_B X` (the map `targetChartMap j` of the canonical machinery). -/
def chartMap (j : Fin t.rank) :
    actualSubspaceLocallyRingedSpace (n := t.embedding.dim+t.rank)
      (strictChartCarrier e.charts (graph B b t) j) ⟶
      (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left :=
  strictChartTo e.charts (graph B b t) (nativeMap B b t e) j

/-- **S2.**  The real-open recentred target chart of `Bl_B X`. -/
def targetMap :
    actualSubspaceLocallyRingedSpace (n := t.embedding.dim+t.rank) (strict B b t e j p) ⟶
      (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left :=
  (realOpenIso B b t e j p hvj).hom ≫ chartMap B b t e j

theorem targetMap_origin :
    (targetMap B b t e j p hvj).base (originPt B b t e j p hvj) = (chartMap B b t e j).base p := by
  change (chartMap B b t e j).base ((realOpenIso B b t e j p hvj).hom.base (originPt B b t e j p hvj)) = _
  rw [realOpenIso_origin]

variable (d : CanonicalTargetNormalSectionData B b t) (hmap : TargetExplicitMapLaws B b t d e)

include hmap in
/-- **S2: the projection square** of the real-open target chart over the base graph chart. -/
theorem square :
    projMap B b t e j p hvj ≫ baseMap B b t =
      targetMap B b t e j p hvj ≫ (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left := by
  have hproj : nativeMap B b t e ≫ (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left =
      geometricProjection (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive)
          t.analytic.isClosed ≫ chartGraphMap t.embedding t.domain t.functions t.holomorphic :=
    congrArg (fun φ => φ.hom.left) hmap.projection
  rw [projMap_eq]
  change ((realOpenIso B b t e j p hvj).hom ≫ strictChartInclusion e.charts (graph B b t) j ≫
      geometricProjection (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive)
        t.analytic.isClosed ≫ (productGraphIso (baseSet B b t) t.functions t.holomorphic).inv) ≫
      (actualOpenSubspaceMap (n := t.embedding.dim) t.embedding.carrier t.domain ≫ t.embedding.map) =
    ((realOpenIso B b t e j p hvj).hom ≫ (strictChartInclusion e.charts (graph B b t) j ≫
      nativeMap B b t e)) ≫ (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left
  rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, Category.assoc, hproj]
  rfl

section Immersion

variable [LocallyRingedSpace.IsOpenImmersion (targetCanonicalMap B b t e).hom.left]

instance chartMap_isOpenImmersion (j : Fin t.rank) :
    LocallyRingedSpace.IsOpenImmersion (chartMap B b t e j) := by
  have : LocallyRingedSpace.IsOpenImmersion (nativeMap B b t e) :=
    (inferInstance : LocallyRingedSpace.IsOpenImmersion (targetCanonicalMap B b t e).hom.left)
  unfold chartMap
  infer_instance

instance targetMap_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (targetMap B b t e j p hvj) := by
  unfold targetMap
  infer_instance

end Immersion

end

end Hironaka.Analytic.Unibranch.HironakaG10NfTargetChart
