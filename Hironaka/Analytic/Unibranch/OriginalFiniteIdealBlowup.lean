import Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphDensity
import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupOriginalObject
import Hironaka.Resolution.HironakaProductZeroPlaneBlowup

/-!
# Actual global blowup of a generically nonzero native finite ideal image

Ordinary ORIGINAL X, native finite-type B,b and EXPLICIT dense unit-image
locus internally select ALL graph/ambient blowup geometry. Private records
only retain the actual output geometry; no record or chart is an input.
Blueprint FIRST: `original-finite-ideal-blowup.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalFiniteIdealBlowup

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaFiniteSectionProductGraph HironakaProductZeroPlaneBlowup
  SourceReducedComplexSpace OriginalFiniteIdealGraphChart OriginalFiniteIdealGraphDensity

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
  density : carrier ⊆ closure (carrier \ centre)
  wholeIdeal : ∀ y : carrier,
    Ideal.map ((actualSubspaceInclusion (n := dim) carrier).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := dim) centre) y.val) =
        nativePulledIdealStalkIdeal chart.hom.left B b y
  markedPoint : carrier
  marked_over : chart.hom.left.base markedPoint = x

attribute [instance] LocalModel.ambientTopology LocalModel.ambientAtlas LocalModel.ambientComplex
  LocalModel.sourceTopology LocalModel.sourceAtlas LocalModel.sourceComplex

private theorem localModel_nonempty [B.IsFiniteType]
    (hDense : Dense {x : X.obj.left |
      LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
    (x : X.obj.left) : Nonempty (LocalModel B b x) := by
  obtain ⟨e,O,r,G,hG,hΓ,hJ,hd,hr,z,hz⟩ := exists_dense_graph_chart B b hDense x
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
    density := hd
    wholeIdeal := hJ
    markedPoint := z
    marked_over := hz }⟩

private def model [B.IsFiniteType]
    (hDense : Dense {x : X.obj.left |
      LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
    (x : X.obj.left) : LocalModel B b x := Classical.choice (localModel_nonempty B b hDense x)

variable [B.IsFiniteType]
  (hDense : Dense {x : X.obj.left |
    LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})

private theorem familyAnalytic (x : X.obj.left) :
    IsComplexAnalyticSubset (n := (model B b hDense x).dim) (model B b hDense x).carrier :=
  (model B b hDense x).analytic

private theorem familyBlowup (x : X.obj.left) :
    IsBlowupAlong (model B b hDense x).dim (model B b hDense x).centre
      (model B b hDense x).projection := (model B b hDense x).blowup

private def familyChart (x : X.obj.left) :
    ofClosedAnalytic (model B b hDense x).carrier (familyAnalytic B b hDense x) ⟶ X :=
  (model B b hDense x).chart

private instance familyChart_open (x : X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (familyChart B b hDense x).hom.left :=
  (model B b hDense x).chartOpen

private theorem familyDensity (x : X.obj.left) :
    (model B b hDense x).carrier ⊆
      closure ((model B b hDense x).carrier \ (model B b hDense x).centre) :=
  (model B b hDense x).density

private theorem familyIdeal (x : X.obj.left) (y : (model B b hDense x).carrier) :
    Ideal.map ((actualSubspaceInclusion (n := (model B b hDense x).dim)
      (model B b hDense x).carrier).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := (model B b hDense x).dim)
        (model B b hDense x).centre) y.val) =
      nativePulledIdealStalkIdeal (familyChart B b hDense x).hom.left B b y :=
  (model B b hDense x).wholeIdeal y

private theorem familyCover (x : X.obj.left) :
    ∃ (i : X.obj.left) (w : (model B b hDense i).carrier),
      (familyChart B b hDense i).hom.left.base w = x :=
  ⟨x,(model B b hDense x).markedPoint,(model B b hDense x).marked_over⟩

/-- Ordinary ORIGINAL finite-type data and EXPLICIT dense unit-image locus
internally derive the SAME actual global original source object. -/
@[implicit_reducible]
def sourceObject : SourceReducedComplexSpace :=
  EmbeddedIdealBlowupOriginalObject.sourceObject (familyAnalytic B b hDense)
    (familyBlowup B b hDense) (familyChart B b hDense) B b
    (familyDensity B b hDense) (familyIdeal B b hDense) (familyCover B b hDense)

/-- The actual full original projection from the internally constructed object. -/
def projectionMorphism : sourceObject B b hDense ⟶ X :=
  EmbeddedIdealBlowupOriginalObject.projectionMorphism (familyAnalytic B b hDense)
    (familyBlowup B b hDense) (familyChart B b hDense) B b
    (familyDensity B b hDense) (familyIdeal B b hDense) (familyCover B b hDense)

/-- Properness belongs to the SAME original projection, derived from its
internally selected actual local proper blowup models. -/
theorem projection_isProperMap : IsProperMap (projectionMorphism B b hDense).hom.left.base :=
  EmbeddedIdealBlowupOriginalObject.projection_isProperMap (familyAnalytic B b hDense)
    (familyBlowup B b hDense) (familyChart B b hDense) B b
    (familyDensity B b hDense) (familyIdeal B b hDense) (familyCover B b hDense)

/-- The internally marked original graph cover and honest local density
derive surjectivity of the SAME actual original projection. -/
theorem projection_surjective : Function.Surjective (projectionMorphism B b hDense).hom.left.base :=
  EmbeddedIdealBlowupOriginalObject.projection_surjective (familyAnalytic B b hDense)
    (familyBlowup B b hDense) (familyChart B b hDense) B b
    (familyDensity B b hDense) (familyIdeal B b hDense) (familyCover B b hDense)

end
end Hironaka.Analytic.Unibranch.OriginalFiniteIdealBlowup
