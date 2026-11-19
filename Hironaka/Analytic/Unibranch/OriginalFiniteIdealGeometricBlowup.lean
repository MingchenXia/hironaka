import Hironaka.Analytic.Unibranch.OriginalPositiveFiniteIdealGraphChart
import Hironaka.Analytic.Unibranch.EmbeddedGeometricIdealOriginalObject
import Hironaka.Resolution.HironakaProductZeroPlaneBlowup

/-!
# Actual global geometric blowup of any native finite ideal image

Ordinary ORIGINAL X and native finite-type B,b internally select ALL
positive graph/ambient blowup geometry with NO dense-unit locus. Private records
only retain the actual output geometry; no record or chart is an input.
Blueprint FIRST: `original-finite-ideal-geometric-blowup.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGeometricBlowup

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaFiniteSectionProductGraph HironakaProductZeroPlaneBlowup
  SourceReducedComplexSpace OriginalFiniteIdealGraphChart OriginalPositiveFiniteIdealGraphChart

open scoped ProductComplexManifold

noncomputable section

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))

private structure LocalModel (x : X.obj.left) where
  dim : ℕ
  ambient : Type
  [ambientTopology : TopologicalSpace ambient]
  [ambientAtlas : ChartedSpace (ComplexModel dim) ambient]
  [ambientComplex : IsComplexManifold dim ambient]
  carrier : Set ambient
  analytic : IsComplexAnalyticSubset (n := dim) carrier
  centre : Set ambient
  source : Type
  [sourceTopology : TopologicalSpace source]
  [sourceAtlas : ChartedSpace (ComplexModel dim) source]
  [sourceComplex : IsComplexManifold dim source]
  projection : source → ambient
  blowup : IsBlowupAlong dim centre projection
  chart : ofClosedAnalytic carrier analytic ⟶ X
  chartOpen : LocallyRingedSpace.IsOpenImmersion chart.hom.left
  wholeIdeal : ∀ y : carrier,
    Ideal.map ((actualSubspaceInclusion (n := dim) carrier).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := dim) centre) y.val) =
        nativePulledIdealStalkIdeal chart.hom.left B b y
  markedPoint : carrier
  marked_over : chart.hom.left.base markedPoint = x

attribute [instance] LocalModel.ambientTopology LocalModel.ambientAtlas LocalModel.ambientComplex
  LocalModel.sourceTopology LocalModel.sourceAtlas LocalModel.sourceComplex

private theorem localModel_nonempty [B.IsFiniteType]
    (x : X.obj.left) : Nonempty (LocalModel B b x) := by
  obtain ⟨e,O,r,G,hG,hΓ,hJ,hr,z,hz⟩ := exists_positive_graph_chart B b x
  obtain ⟨Y,tY,aY,cY,π,hπ⟩ := exists_product_zero_plane_blowup (n := e.dim) (M := O) hr
  let := tY
  let := aY
  let := cY
  exact ⟨{
    dim := e.dim+r
    ambient := O × ComplexModel r
    ambientTopology := inferInstance
    ambientAtlas := inferInstance
    ambientComplex := inferInstance
    carrier := productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G
    analytic := hΓ
    centre := {q : O × ComplexModel r | q.2 = 0}
    source := Y
    sourceTopology := tY
    sourceAtlas := aY
    sourceComplex := cY
    projection := π
    blowup := hπ
    chart := chartGraphMorphism e O G hG hΓ
    chartOpen := chartGraphMap_isOpenImmersion e O G hG
    wholeIdeal := hJ
    markedPoint := z
    marked_over := hz }⟩

private def model [B.IsFiniteType]
    (x : X.obj.left) : LocalModel B b x := Classical.choice (localModel_nonempty B b x)

variable [B.IsFiniteType]

private theorem familyAnalytic (x : X.obj.left) :
    IsComplexAnalyticSubset (n := (model B b x).dim) (model B b x).carrier :=
  (model B b x).analytic

private theorem familyBlowup (x : X.obj.left) :
    IsBlowupAlong (model B b x).dim (model B b x).centre
      (model B b x).projection := (model B b x).blowup

private def familyChart (x : X.obj.left) :
    ofClosedAnalytic (model B b x).carrier (familyAnalytic B b x) ⟶ X :=
  (model B b x).chart

private instance familyChart_open (x : X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (familyChart B b x).hom.left :=
  (model B b x).chartOpen

private theorem familyIdeal (x : X.obj.left) (y : (model B b x).carrier) :
    Ideal.map ((actualSubspaceInclusion (n := (model B b x).dim)
      (model B b x).carrier).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := (model B b x).dim)
        (model B b x).centre) y.val) =
      nativePulledIdealStalkIdeal (familyChart B b x).hom.left B b y :=
  (model B b x).wholeIdeal y

private theorem familyCover (x : X.obj.left) :
    ∃ (i : X.obj.left) (w : (model B b i).carrier),
      (familyChart B b i).hom.left.base w = x :=
  ⟨x,(model B b x).markedPoint,(model B b x).marked_over⟩

/-- Ordinary ORIGINAL finite-type data internally derive the SAME actual
global geometric source, with no density hypothesis or source packet. -/
@[implicit_reducible]
def sourceObject : SourceReducedComplexSpace :=
  EmbeddedGeometricIdealOriginalObject.sourceObject (familyAnalytic B b)
    (familyBlowup B b) (familyChart B b) B b
    (familyIdeal B b) (familyCover B b)

/-- The actual full original projection from the internally constructed object. -/
def projectionMorphism : sourceObject B b ⟶ X :=
  EmbeddedGeometricIdealOriginalObject.projectionMorphism (familyAnalytic B b)
    (familyBlowup B b) (familyChart B b) B b
    (familyIdeal B b) (familyCover B b)

/-- Properness belongs to the SAME original projection, derived from its
internally selected actual local proper blowup models. -/
theorem projection_isProperMap : IsProperMap (projectionMorphism B b).hom.left.base :=
  EmbeddedGeometricIdealOriginalObject.projection_isProperMap (familyAnalytic B b)
    (familyBlowup B b) (familyChart B b) B b
    (familyIdeal B b) (familyCover B b)

end
end Hironaka.Analytic.Unibranch.OriginalFiniteIdealGeometricBlowup
