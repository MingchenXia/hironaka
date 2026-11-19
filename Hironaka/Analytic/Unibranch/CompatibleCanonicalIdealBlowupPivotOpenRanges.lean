import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.Basic


/-! Intrinsic SAME prescribed pivot loci, actual strict-chart OIs and ranges.
BP FIRST; ordinary caller fixes accepted920 ONCE. No supplied range/cover,
raw cancellation, private repivot/analytic helper, sourcepoint from rawpair.
Later literal restrictions/overlap/Qsat/rawfibre remain separate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka BlowupConstruction BlowupFlatCoordinates BlowupStrictSubmanifold
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaSingularIdealInvertibleModule HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces HironakaFiniteSectionProductGraph
  CompatibleCanonicalIdealBlowupPivotChart CompatibleCanonicalIdealBlowupSquareCharts
  CompatibleCanonicalIdealBlowupNormalSections CompatibleCanonicalIdealBlowupExplicitProductCharts
  SourceReducedComplexSpace EmbeddedGeometricBlowup
open scoped ProductComplexManifold

private theorem ideal_generator_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (a : R) :
    I=Ideal.span {a} ↔ Ideal.map e.toRingHom I=Ideal.span {e a} := by
  change I=Ideal.span {a} ↔ Ideal.map (e : R →+* S) I=Ideal.span {e a}
  constructor
  · intro h
    rw [h,Ideal.map_span,Set.image_singleton]
    rfl
  · intro h
    have hi := congrArg (Ideal.map (e.symm : S →+* R)) h
    rw [Ideal.map_of_equiv,Ideal.map_span,Set.image_singleton] at hi
    simpa using hi

private theorem oi_generator_iff {A T : LocallyRingedSpace.{0}}
    (K : A ⟶ T) [LocallyRingedSpace.IsOpenImmersion K] (z : A)
    (I : Ideal (T.presheaf.stalk (K.base z)).carrier)
    (a : (T.presheaf.stalk (K.base z)).carrier) :
    I=Ideal.span {a} ↔ Ideal.map (K.stalkMap z).hom I=Ideal.span {(K.stalkMap z) a} := by
  let : IsIso (K.stalkMap z) := LocallyRingedSpace.IsOpenImmersion.stalk_iso K z
  exact ideal_generator_equiv (asIso (K.stalkMap z)).commRingCatIsoToRingEquiv I a

-- Finite SAME-family coverage from held OWN invertibility, not private repivot.
private theorem exists_same_family_generator {R : Type*} [CommRing R] [IsLocalRing R]
    {ι : Type*} [Fintype ι] (I : Ideal R) (hI : Module.Invertible R I)
    (v : ι → R) (hv : I=Ideal.span (range v)) : ∃i, I=Ideal.span {v i} := by
  classical
  obtain ⟨ε,hε,hSpan,hReg⟩ := exists_regular_generator I hI
  have hm (i : ι) : v i∈Ideal.span {ε} := by
    rw [←hSpan,hv]
    exact Ideal.subset_span ⟨i,rfl⟩
  choose c hc using fun i => Ideal.mem_span_singleton.mp (hm i)
  have he : ε∈Ideal.span (range v) := hv ▸ hε
  obtain ⟨a,ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp he
  have hs : ε*(∑i,a i*c i)=ε*1 := by
    rw [Finset.mul_sum]
    calc
      ∑i,ε*(a i*c i)=∑i,a i*v i := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hc i]
        ring
      _ = ε := ha
      _ = ε*1 := (mul_one ε).symm
  have hu : IsUnit (∑i,a i*c i) := by rw [hReg.left hs];exact isUnit_one
  obtain ⟨i,_hi,hi⟩ := IsLocalRing.exists_of_isUnit_sum hu
  refine ⟨i,?_⟩
  rw [hSpan,hc i]
  exact (Ideal.span_singleton_mul_right_unit (isUnit_of_mul_isUnit_right hi) ε).symm

section StrictCharts
variable {n r : ℕ} {P : Type} [TopologicalSpace P]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]

abbrev actualStrictCarrier (W : Set (P × ComplexModel r)) :=
  geoStrictTransform (blowupProj (n+r) {q : P × ComplexModel r | q.2=0}) {q | q.2=0} W

def strictChartAmbientOpen (a : ProductNormalCharts n r P) (j : Fin r) :
    Opens (BlowupSpace (n+r) {q : P × ComplexModel r | q.2=0}) :=
  ⟨(productNormalChart (n := n) a.base j).source,
    (productNormalChart (n := n) a.base j).isOpen_source⟩

abbrev strictChartCarrier (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r)) (j : Fin r) :=
  (Subtype.val : strictChartAmbientOpen a j → _) ⁻¹' actualStrictCarrier (n := n) W

def strictChartInclusion (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r)) (j : Fin r) :
    actualSubspaceLocallyRingedSpace (n := n+r) (strictChartCarrier a W j) ⟶
      actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) :=
  actualOpenSubspaceMap (n := n+r) (actualStrictCarrier (n := n) W) (strictChartAmbientOpen a j)

instance strictChartInclusion_isOpenImmersion (a : ProductNormalCharts n r P)
    (W : Set (P × ComplexModel r)) (j : Fin r) :
    LocallyRingedSpace.IsOpenImmersion (strictChartInclusion a W j) := by
  unfold strictChartInclusion
  infer_instance

def strictChartTo {A : LocallyRingedSpace.{0}} (a : ProductNormalCharts n r P)
    (W : Set (P × ComplexModel r))
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A) (j : Fin r) :=
  strictChartInclusion a W j ≫ K

/-- Definitional equality of the literal parent point and the full chart image.
No point or equality certificate is supplied by an ordinary caller. -/
private theorem strictChartTo_basepoint {A : LocallyRingedSpace.{0}}
    (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A)
    (j : Fin r) (z : strictChartCarrier a W j) :
    (strictChartTo a W K j).base z=K.base ((strictChartInclusion a W j).base z) := rfl

instance strictChartTo_isOpenImmersion {A : LocallyRingedSpace.{0}}
    (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A)
    [hK : LocallyRingedSpace.IsOpenImmersion K] (j : Fin r) :
    LocallyRingedSpace.IsOpenImmersion (strictChartTo a W K j) := by
  unfold strictChartTo
  infer_instance

private theorem strictChartTo_range {A : LocallyRingedSpace.{0}}
    (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A) (j : Fin r) :
    range (strictChartTo a W K j).base=
      K.base '' {z : actualStrictCarrier (n := n) W | z.val∈strictChartAmbientOpen a j} := by
  ext z
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨⟨u.val.val,u.property⟩,u.val.property,rfl⟩
  · rintro ⟨u,hu,rfl⟩
    exact ⟨⟨⟨u.val,hu⟩,u.property⟩,rfl⟩

private theorem strictChartTo_numerator {A : LocallyRingedSpace.{0}}
    (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A)
    (j : Fin r) (z : strictChartCarrier a W j)
    (s : (A.presheaf.stalk ((strictChartTo a W K j).base z)).carrier) :
    (strictChartTo a W K j).stalkMap z s=
      (strictChartInclusion a W j).stalkMap z
        (K.stalkMap ((strictChartInclusion a W j).base z) s) :=
  ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp (strictChartInclusion a W j) K z) s

private theorem strictChartTo_normal {A : LocallyRingedSpace.{0}}
    (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A)
    (j : Fin r) (z : strictChartCarrier a W j)
    (s : (A.presheaf.stalk (K.base ((strictChartInclusion a W j).base z))).carrier)
    (v : ((actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W)).presheaf.stalk
      ((strictChartInclusion a W j).base z)).carrier)
    (hv : K.stalkMap ((strictChartInclusion a W j).base z) s=v) :
    (strictChartTo a W K j).stalkMap z s=(strictChartInclusion a W j).stalkMap z v :=
  (strictChartTo_numerator a W K j z s).trans (congrArg ((strictChartInclusion a W j).stalkMap z) hv)

/-- Complete native normal-law OUTPUT, retaining every label and point.
The ordinary endpoint constructs this structure; it is never an input packet. -/
structure StrictChartNormalLaws {A : LocallyRingedSpace.{0}}
    (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A)
    (s : ∀ (j _i : Fin r) (z : strictChartCarrier a W j),
      (A.presheaf.stalk (K.base ((strictChartInclusion a W j).base z))).carrier)
    (v : ∀ (j _i : Fin r) (z : strictChartCarrier a W j),
      ((actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W)).presheaf.stalk
        ((strictChartInclusion a W j).base z)).carrier) : Prop where
  normal : ∀ (j i : Fin r) (z : strictChartCarrier a W j),
    (strictChartTo a W K j).stalkMap z (s j i z)=(strictChartInclusion a W j).stalkMap z (v j i z)

private theorem constructedNormalLaws {A : LocallyRingedSpace.{0}}
    (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A)
    (s : ∀ (j _i : Fin r) (z : strictChartCarrier a W j),
      (A.presheaf.stalk (K.base ((strictChartInclusion a W j).base z))).carrier)
    (v : ∀ (j _i : Fin r) (z : strictChartCarrier a W j),
      ((actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W)).presheaf.stalk
        ((strictChartInclusion a W j).base z)).carrier)
    (h : ∀ (j i : Fin r) (z : strictChartCarrier a W j),
      K.stalkMap ((strictChartInclusion a W j).base z) (s j i z)=v j i z) :
    StrictChartNormalLaws a W K s v :=
  ⟨fun j i z => strictChartTo_normal a W K j z (s j i z) (v j i z) (h j i z)⟩

/-- A named, shared precomposition function; no concrete lambda comparison
or new native object is needed at its consumers. -/
private def precomposeParentSection {A : LocallyRingedSpace.{0}}
    (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A)
    (s : ∀ (p : actualStrictCarrier (n := n) W) (_i : Fin r),
      (A.presheaf.stalk (K.base p)).carrier) :
    ∀ (j _i : Fin r) (z : strictChartCarrier a W j),
      (A.presheaf.stalk (K.base ((strictChartInclusion a W j).base z))).carrier :=
  fun j i z => s ((strictChartInclusion a W j).base z) i

private def precomposeParentCoordinate
    (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (v : ∀ (p : actualStrictCarrier (n := n) W) (_j _i : Fin r),
      ((actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W)).presheaf.stalk p).carrier) :
    ∀ (j _i : Fin r) (z : strictChartCarrier a W j),
      ((actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W)).presheaf.stalk
        ((strictChartInclusion a W j).base z)).carrier :=
  fun j i z => v ((strictChartInclusion a W j).base z) j i

/-- Precompose an actual WHOLE parent normal equation only after its pointwise
comparison is established. The coordinate function remains independent. -/
private theorem constructedNormalLawsFromParent {A : LocallyRingedSpace.{0}}
    (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A)
    (s : ∀ (p : actualStrictCarrier (n := n) W) (_i : Fin r),
      (A.presheaf.stalk (K.base p)).carrier)
    (v : ∀ (p : actualStrictCarrier (n := n) W) (_j _i : Fin r),
      ((actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W)).presheaf.stalk p).carrier)
    (h : ∀ (p : actualStrictCarrier (n := n) W) (j i : Fin r), K.stalkMap p (s p i)=v p j i) :
    StrictChartNormalLaws a W K
      (precomposeParentSection a W K s) (precomposeParentCoordinate a W v) :=
  constructedNormalLaws a W K (precomposeParentSection a W K s) (precomposeParentCoordinate a W v)
    (fun j i z => h ((strictChartInclusion a W j).base z) j i)

private theorem strictChartTo_scalar {A : LocallyRingedSpace.{0}}
    (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A)
    (q : A ⟶ complexPoint)
    (hK : K ≫ q=subspacePointMap (n := n+r) (actualStrictCarrier (n := n) W)) (j : Fin r) :
    strictChartTo a W K j ≫ q=subspacePointMap (n := n+r) (strictChartCarrier a W j) := by
  rw [strictChartTo,Category.assoc,hK]
  exact actualSubspaceMap_point contMDiff_subtype_val (fun _ hz => hz)


private theorem strictChartTo_ideal {A : LocallyRingedSpace.{0}}
    (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A)
    (j : Fin r) (z : strictChartCarrier a W j)
    (I : Ideal (A.presheaf.stalk ((strictChartTo a W K j).base z)).carrier) :
    Ideal.map ((strictChartTo a W K j).stalkMap z).hom I=
      Ideal.map ((strictChartInclusion a W j).stalkMap z).hom
        (Ideal.map (K.stalkMap ((strictChartInclusion a W j).base z)).hom I) := by
  let f := (K.stalkMap ((strictChartInclusion a W j).base z)).hom
  let h := ((strictChartInclusion a W j).stalkMap z).hom
  have he : ((strictChartTo a W K j).stalkMap z).hom=h.comp f := by
    ext v
    exact strictChartTo_numerator a W K j z v
  exact (congrArg (fun f => Ideal.map f I) he).trans (Ideal.map_map f h).symm


/-- Entire native composition on all numerators and all ideals, with the
genuine point scalar law. This is OUTPUT, not a sheaf/quotient packet. -/
structure StrictChartNativeLaws {A : LocallyRingedSpace.{0}}
    (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A)
    (q : A ⟶ complexPoint) : Prop where
  scalar : ∀j, strictChartTo a W K j ≫ q=subspacePointMap (n := n+r) (strictChartCarrier a W j)
  all_numerators : ∀ (j : Fin r) (z : strictChartCarrier a W j)
    (s : (A.presheaf.stalk ((strictChartTo a W K j).base z)).carrier),
    (strictChartTo a W K j).stalkMap z s=
      (strictChartInclusion a W j).stalkMap z (K.stalkMap ((strictChartInclusion a W j).base z) s)
  entire_ideal_action : ∀ (j : Fin r) (z : strictChartCarrier a W j)
    (I : Ideal (A.presheaf.stalk ((strictChartTo a W K j).base z)).carrier),
    Ideal.map ((strictChartTo a W K j).stalkMap z).hom I=
      Ideal.map ((strictChartInclusion a W j).stalkMap z).hom
        (Ideal.map (K.stalkMap ((strictChartInclusion a W j).base z)).hom I)


private theorem constructedNativeLaws {A : LocallyRingedSpace.{0}}
    (a : ProductNormalCharts n r P) (W : Set (P × ComplexModel r))
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A)
    (q : A ⟶ complexPoint)
    (hK : K ≫ q=subspacePointMap (n := n+r) (actualStrictCarrier (n := n) W)) :
    StrictChartNativeLaws a W K q where
  scalar := strictChartTo_scalar a W K q hK
  all_numerators := strictChartTo_numerator a W K
  entire_ideal_action := strictChartTo_ideal a W K


private theorem product_domain_mem (a : ProductNormalCharts n r P) (j : Fin r)
    (u : P × ComplexModel r) : u∈(productNormalChart (n := n) a.base j).dom :=
  Eq.mpr (congrArg (fun D : Set (P × ComplexModel r) => u∈D) (a.domain j)) (Set.mem_univ u)

private theorem product_strict_generator_iff (a : ProductNormalCharts n r P) (hr : 0<r)
    (W : Set (P × ComplexModel r)) (hW : IsClosed W) (j : Fin r)
    (z : actualStrictCarrier (n := n) W) :
    strictCentreStalkIdeal W z=Ideal.span {geometricCoordinateClass W
      (productNormalChart (n := n) a.base j) z (by rw [a.domain j];trivial) (j.natAdd n)} ↔
      z.val∈strictChartAmbientOpen a j := by
  let c := productNormalChart (n := n) a.base j
  have he := Set.ext_iff.mp (strict_pivot_generator_locus
    (HironakaProductZeroPlaneBlowup.interior_product_zero_plane_eq_empty hr)
    W hW c (j.natAdd n) (by simp [c,productNormalChart])) z
  change (∃hz : z.val.base∈c.dom,
    strictCentreStalkIdeal W z=Ideal.span {geometricCoordinateClass W c z hz (j.natAdd n)}) ↔
      z.val∈c.source at he
  constructor
  · intro h
    exact he.mp ⟨by rw [a.domain j];trivial,h⟩
  · intro h
    obtain ⟨_hz,hgen⟩ := he.mpr h
    exact hgen

end StrictCharts


section SameCanonical
open OriginalFiniteIdealGraphChart HironakaResolutionSpaceComplex
variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

variable (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t)
  (g : CanonicalSquareGeometry B b F x t c) (d : CanonicalNormalSectionData B b F x t c g)
  (E : SameCanonicalExplicitProductModels B b F x t c g d)

abbrev targetGraphSet := productGraph
  ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier) t.functions

abbrev sourceGraphSet := productGraph
  ((Subtype.val : c.subdomain → c.domain) ⁻¹'
    ((Subtype.val : c.domain → c.embedding.ambient) ⁻¹' c.embedding.carrier)) (t.functions ∘ c.baseMap)

/-- Defined by the ENTIRE ideal and prescribed actual section, before its image. -/
def targetPivotSet (j : Fin t.rank) : Set (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left :=
  nativeWholeGeneratorLocus (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left
    B b d.target.targetOpen (d.target.sections j)

def fullSourcePivotSet (j : Fin t.rank) : Set (OriginalFiniteIdealGeometricBlowup.sourceObject
    (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).obj.left :=
  nativeWholeGeneratorLocus (OriginalFiniteIdealGeometricBlowup.projectionMorphism
    (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left
    (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)
    ((Opens.map (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base).obj d.target.targetOpen)
    (canonicalPulledIdealSection B b F d.target.targetOpen (d.target.sections j))

def sourceModelOpen : Opens (OriginalFiniteIdealGeometricBlowup.sourceObject
    (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).obj.left.toTopCat :=
  ⟨range (sourceCanonicalMap B b F x t c g E.source).hom.left.base,
    E.source_maps.open_immersion.base_open.isOpen_range⟩

def sourcePivotSet (j : Fin t.rank) : Set (OriginalFiniteIdealGeometricBlowup.sourceObject
    (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).obj.left :=
  (sourceModelOpen B b F x t c g d E).1 ∩ fullSourcePivotSet B b F x t c g d j

-- Typed views of the SAME original maps, exposing the literal old quotient
-- source to native OI/range APIs. No new LRS/sheaf or comparison is created.
private abbrev targetNativeMap :
    actualSubspaceLocallyRingedSpace (n := t.embedding.dim+t.rank)
      (actualStrictCarrier (n := t.embedding.dim) (targetGraphSet B b t)) ⟶
      (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left :=
  (targetCanonicalMap B b t E.target).hom.left

private abbrev sourceNativeMap :
    actualSubspaceLocallyRingedSpace (n := c.embedding.dim+t.rank)
      (actualStrictCarrier (n := c.embedding.dim) (sourceGraphSet B b F x t c)) ⟶
      (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.left :=
  (sourceCanonicalMap B b F x t c g E.source).hom.left

def targetChartMap (j : Fin t.rank) :
    actualSubspaceLocallyRingedSpace (n := t.embedding.dim+t.rank)
      (strictChartCarrier E.target.charts (targetGraphSet B b t) j) ⟶
      (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left :=
  strictChartTo E.target.charts (targetGraphSet B b t) (targetNativeMap B b F x t c g d E) j

def sourceChartMap (j : Fin t.rank) :
    actualSubspaceLocallyRingedSpace (n := c.embedding.dim+t.rank)
      (strictChartCarrier E.source.charts (sourceGraphSet B b F x t c) j) ⟶
      (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.left :=
  strictChartTo E.source.charts (sourceGraphSet B b F x t c) (sourceNativeMap B b F x t c g d E) j

/-- Actual prescribed source section at an ABSTRACT parent strict point.
This is a genuine original germ, before any inclusion is substituted. -/
private def sourceParentSectionGerm
    (p : actualStrictCarrier (n := c.embedding.dim) (sourceGraphSet B b F x t c)) (i : Fin t.rank) :
    ((OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.left.presheaf.stalk
      ((sourceNativeMap B b F x t c g d E).base p)).carrier :=
  (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
    (nativePulledIdealInclusion F.hom.left B b)).obj.left.presheaf.germ
    ((Opens.map (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base).obj d.target.targetOpen)
    ((sourceNativeMap B b F x t c g d E).base p) (E.source_normals.geometric_mem p)
    (canonicalPulledIdealSection B b F d.target.targetOpen (d.target.sections i)).val

/-- Independent actual GEOMETRIC coordinate class, never defined as a section
image. In particular it retains the original zero-plane and normal offset. -/
private def sourceParentGeometricCoordinate
    (p : actualStrictCarrier (n := c.embedding.dim) (sourceGraphSet B b F x t c)) (j i : Fin t.rank) :
    ((actualSubspaceLocallyRingedSpace (n := c.embedding.dim+t.rank)
      (actualStrictCarrier (n := c.embedding.dim) (sourceGraphSet B b F x t c))).presheaf.stalk p).carrier :=
  geometricCoordinateClass (n := c.embedding.dim+t.rank)
    (C := {q : c.subdomain × ComplexModel t.rank | q.2=0})
    (sourceGraphSet B b F x t c) (productNormalChart (n := c.embedding.dim) E.source.charts.base j) p
    (product_domain_mem E.source.charts j p.val.base) (i.natAdd c.embedding.dim)

private theorem source_parent_normal
    (p : actualStrictCarrier (n := c.embedding.dim) (sourceGraphSet B b F x t c)) (j i : Fin t.rank) :
    (sourceNativeMap B b F x t c g d E).stalkMap p
      (sourceParentSectionGerm B b F x t c g d E p i)=
      sourceParentGeometricCoordinate B b F x t c g d E p j i := by
  delta sourceParentSectionGerm sourceParentGeometricCoordinate sourceNativeMap sourceGraphSet
  exact E.source_normals.normal p j i

abbrev sourceSectionGerm :=
  precomposeParentSection E.source.charts (sourceGraphSet B b F x t c) (sourceNativeMap B b F x t c g d E)
    (sourceParentSectionGerm B b F x t c g d E)


abbrev sourceCoordinateClass :=
  precomposeParentCoordinate E.source.charts (sourceGraphSet B b F x t c)
    (sourceParentGeometricCoordinate B b F x t c g d E)


private theorem source_normal_composition :
    StrictChartNormalLaws E.source.charts (sourceGraphSet B b F x t c)
      (sourceNativeMap B b F x t c g d E)
      (sourceSectionGerm B b F x t c g d E) (sourceCoordinateClass B b F x t c g d E) := by
  have H := constructedNormalLawsFromParent
    (A := (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.left)
    E.source.charts (sourceGraphSet B b F x t c) (sourceNativeMap B b F x t c g d E)
    (sourceParentSectionGerm B b F x t c g d E) (sourceParentGeometricCoordinate B b F x t c g d E)
    (source_parent_normal B b F x t c g d E)
  delta sourceSectionGerm sourceCoordinateClass
  exact H


/-- The SAME prescribed target section at the actual chart image point. -/
abbrev targetSectionGerm (j i : Fin t.rank)
    (z : strictChartCarrier E.target.charts (targetGraphSet B b t) j) :
    ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.stalk
      ((targetNativeMap B b F x t c g d E).base
        ((strictChartInclusion E.target.charts (targetGraphSet B b t) j).base z))).carrier :=
  (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ d.target.targetOpen
    ((targetNativeMap B b F x t c g d E).base
      ((strictChartInclusion E.target.charts (targetGraphSet B b t) j).base z))
    (E.target_normals.geometric_mem ((strictChartInclusion E.target.charts (targetGraphSet B b t) j).base z))
    (d.target.sections i).val


abbrev targetCoordinateClass (j i : Fin t.rank)
    (z : strictChartCarrier E.target.charts (targetGraphSet B b t) j) :
    ((actualSubspaceLocallyRingedSpace (n := t.embedding.dim+t.rank)
      (actualStrictCarrier (n := t.embedding.dim) (targetGraphSet B b t))).presheaf.stalk
      ((strictChartInclusion E.target.charts (targetGraphSet B b t) j).base z)).carrier :=
  geometricCoordinateClass (n := t.embedding.dim+t.rank)
    (C := {q : t.domain × ComplexModel t.rank | q.2=0})
    (targetGraphSet B b t) (productNormalChart (n := t.embedding.dim) E.target.charts.base j)
    ((strictChartInclusion E.target.charts (targetGraphSet B b t) j).base z)
    (product_domain_mem E.target.charts j _) (i.natAdd t.embedding.dim)


private theorem target_normal_composition :
    StrictChartNormalLaws E.target.charts (targetGraphSet B b t)
      (targetNativeMap B b F x t c g d E)
      (targetSectionGerm B b F x t c g d E) (targetCoordinateClass B b F x t c g d E) := by
  apply constructedNormalLaws
  intro j i z
  let p : (explicitTarget B b t).obj.left :=
    (strictChartInclusion E.target.charts (targetGraphSet B b t) j).base z
  have hn := E.target_normals.normal p j i
  exact hn


private theorem target_generator_iff (j : Fin t.rank) (z : (explicitTarget B b t).obj.left) :
    (targetCanonicalMap B b t E.target).hom.left.base z∈targetPivotSet B b F x t c g d j ↔
      z.val∈strictChartAmbientOpen E.target.charts j := by
  let K := (targetCanonicalMap B b t E.target).hom.left
  let : LocallyRingedSpace.IsOpenImmersion K := E.target_maps.open_immersion
  have hgeom := product_strict_generator_iff E.target.charts t.positive
    (targetGraphSet B b t) t.analytic.isClosed j z
  constructor
  · rintro ⟨hz,hgen⟩
    have hi := (oi_generator_iff K z _
      ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ
        d.target.targetOpen (K.base z) hz (d.target.sections j).val)).mp hgen
    exact hgeom.mp ((E.target_normals.whole_ideal z).symm.trans
      (hi.trans (congrArg (fun a => Ideal.span {a}) (E.target_normals.normal z j j))))
  · intro hz
    refine ⟨E.target_normals.geometric_mem z,?_⟩
    apply (oi_generator_iff K z _ _).mpr
    exact (E.target_normals.whole_ideal z).trans ((hgeom.mpr hz).trans
      (congrArg (fun a => Ideal.span {a}) (E.target_normals.normal z j j).symm))

private theorem source_generator_iff (j : Fin t.rank) (z : (explicitSource B b F x t c).obj.left) :
    (sourceCanonicalMap B b F x t c g E.source).hom.left.base z∈fullSourcePivotSet B b F x t c g d j ↔
      z.val∈strictChartAmbientOpen E.source.charts j := by
  let K := (sourceCanonicalMap B b F x t c g E.source).hom.left
  let : LocallyRingedSpace.IsOpenImmersion K := E.source_maps.open_immersion
  have hgeom := product_strict_generator_iff E.source.charts t.positive
    (sourceGraphSet B b F x t c) c.analytic.isClosed j z
  constructor
  · rintro ⟨hz,hgen⟩
    have hi := (oi_generator_iff K z _
      ((OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.left.presheaf.germ
        ((Opens.map (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base).obj d.target.targetOpen)
        (K.base z) hz (canonicalPulledIdealSection B b F d.target.targetOpen (d.target.sections j)).val)).mp hgen
    exact hgeom.mp ((E.source_normals.whole_ideal z).symm.trans
      (hi.trans (congrArg (fun a => Ideal.span {a}) (E.source_normals.normal z j j))))
  · intro hz
    refine ⟨E.source_normals.geometric_mem z,?_⟩
    apply (oi_generator_iff K z _ _).mpr
    exact (E.source_normals.whole_ideal z).trans ((hgeom.mpr hz).trans
      (congrArg (fun a => Ideal.span {a}) (E.source_normals.normal z j j).symm))

instance targetChartMap_isOpenImmersion (j : Fin t.rank) :
    LocallyRingedSpace.IsOpenImmersion (targetChartMap B b F x t c g d E j) := by
  unfold targetChartMap
  exact strictChartTo_isOpenImmersion E.target.charts (targetGraphSet B b t)
    (targetNativeMap B b F x t c g d E) (hK := E.target_maps.open_immersion) j

instance sourceChartMap_isOpenImmersion (j : Fin t.rank) :
    LocallyRingedSpace.IsOpenImmersion (sourceChartMap B b F x t c g d E j) := by
  unfold sourceChartMap
  exact strictChartTo_isOpenImmersion E.source.charts (sourceGraphSet B b F x t c)
    (sourceNativeMap B b F x t c g d E) (hK := E.source_maps.open_immersion) j

private theorem target_chart_range (j : Fin t.rank) :
    range (targetChartMap B b F x t c g d E j).base=targetPivotSet B b F x t c g d j := by
  change range (strictChartTo E.target.charts (targetGraphSet B b t)
    (targetNativeMap B b F x t c g d E) j).base=_
  rw [strictChartTo_range E.target.charts (targetGraphSet B b t) (targetNativeMap B b F x t c g d E) j]
  ext q
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (target_generator_iff B b F x t c g d E j z).mpr hz
  · intro hq
    have hU : q∈d.target.targetOpen := hq.choose
    have hRange : q∈range (targetNativeMap B b F x t c g d E).base :=
      Eq.mp (congrArg (fun A : Set (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.toTopCat => q∈A)
        E.target_maps.range_eq) hU
    obtain ⟨z,rfl⟩ := hRange
    exact ⟨z,(target_generator_iff B b F x t c g d E j z).mp hq,rfl⟩

private theorem source_chart_range (j : Fin t.rank) :
    range (sourceChartMap B b F x t c g d E j).base=sourcePivotSet B b F x t c g d E j := by
  change range (strictChartTo E.source.charts (sourceGraphSet B b F x t c)
    (sourceNativeMap B b F x t c g d E) j).base=_
  rw [strictChartTo_range E.source.charts (sourceGraphSet B b F x t c) (sourceNativeMap B b F x t c g d E) j]
  ext q
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨⟨z,rfl⟩,(source_generator_iff B b F x t c g d E j z).mpr hz⟩
  · rintro ⟨⟨z,rfl⟩,hz⟩
    exact ⟨z,(source_generator_iff B b F x t c g d E j z).mp hz,rfl⟩

def targetPivotOpen (j : Fin t.rank) : Opens (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.toTopCat :=
  ⟨targetPivotSet B b F x t c g d j,by
    rw [←target_chart_range B b F x t c g d E j]
    exact (targetChartMap_isOpenImmersion B b F x t c g d E j).base_open.isOpen_range⟩

def sourcePivotOpen (j : Fin t.rank) : Opens (OriginalFiniteIdealGeometricBlowup.sourceObject
    (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).obj.left.toTopCat :=
  ⟨sourcePivotSet B b F x t c g d E j,by
    rw [←source_chart_range B b F x t c g d E j]
    exact (sourceChartMap_isOpenImmersion B b F x t c g d E j).base_open.isOpen_range⟩

private theorem full_source_preimage (j : Fin t.rank) :
    fullSourcePivotSet B b F x t c g d j=
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base ⁻¹'
        targetPivotSet B b F x t c g d j :=
  canonicalWholeGeneratorLocus_preimage B b F d.target.targetOpen (d.target.sections j)

private theorem source_range_subset :
    (sourceModelOpen B b F x t c g d E).1 ⊆
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base ⁻¹'
        d.target.targetOpen.1 := by
  rintro q ⟨z,rfl⟩
  exact E.source_normals.geometric_mem z

private theorem source_pivot_preimage (j : Fin t.rank) :
    (sourcePivotOpen B b F x t c g d E j).1=
      (sourceModelOpen B b F x t c g d E).1 ∩
        (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base ⁻¹'
          (targetPivotOpen B b F x t c g d E j).1 :=
  congrArg (fun A => (sourceModelOpen B b F x t c g d E).1 ∩ A)
    (full_source_preimage B b F x t c g d j)

private theorem target_pivot_cover :
    (⋃j : Fin t.rank,(targetPivotOpen B b F x t c g d E j).1)=
      d.target.targetOpen.1 := by
  apply le_antisymm
  · intro q hq
    obtain ⟨j,hj⟩ := mem_iUnion.mp hq
    exact hj.choose
  · intro q hq
    obtain ⟨j,hj⟩ := exists_same_family_generator _
      (OriginalFiniteIdealGeometricBlowupUniversal.projection_ideal_moduleInvertible B b q)
      (fun j : Fin t.rank => (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ
        d.target.targetOpen q hq (d.target.sections j).val) (d.target.target_span q hq)
    exact mem_iUnion.mpr ⟨j,hq,hj⟩

private theorem source_pivot_cover :
    (⋃j : Fin t.rank,(sourcePivotOpen B b F x t c g d E j).1)=
      (sourceModelOpen B b F x t c g d E).1 := by
  ext q
  constructor
  · intro hq
    obtain ⟨j,hj⟩ := mem_iUnion.mp hq
    exact hj.1
  · intro hq
    have hU := source_range_subset B b F x t c g d E hq
    rw [←target_pivot_cover B b F x t c g d E] at hU
    obtain ⟨j,hj⟩ := mem_iUnion.mp hU
    apply mem_iUnion.mpr
    refine ⟨j,?_⟩
    rw [source_pivot_preimage B b F x t c g d E j]
    exact ⟨hq,hj⟩


/-- Exact actual range/native data, derived from the held E; no desired
pivot/range/cover statement is input to this output record. -/
structure PivotChartRangeData : Prop where
  target_open_immersion : ∀j, LocallyRingedSpace.IsOpenImmersion (targetChartMap B b F x t c g d E j)
  source_open_immersion : ∀j, LocallyRingedSpace.IsOpenImmersion (sourceChartMap B b F x t c g d E j)
  target_range : ∀j, range (targetChartMap B b F x t c g d E j).base=(targetPivotOpen B b F x t c g d E j).1
  source_range : ∀j, range (sourceChartMap B b F x t c g d E j).base=(sourcePivotOpen B b F x t c g d E j).1
  target_native : StrictChartNativeLaws E.target.charts (targetGraphSet B b t)
    (targetNativeMap B b F x t c g d E) (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.hom
  source_native : StrictChartNativeLaws E.source.charts (sourceGraphSet B b F x t c)
    (sourceNativeMap B b F x t c g d E)
    (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.hom
  target_normals : StrictChartNormalLaws E.target.charts (targetGraphSet B b t)
    (targetNativeMap B b F x t c g d E)
    (targetSectionGerm B b F x t c g d E) (targetCoordinateClass B b F x t c g d E)
  source_normals : StrictChartNormalLaws E.source.charts (sourceGraphSet B b F x t c)
    (sourceNativeMap B b F x t c g d E)
    (sourceSectionGerm B b F x t c g d E) (sourceCoordinateClass B b F x t c g d E)


/-- The reusable range/native constructor on the SAME already-derived model.
The ordinary caller below obtains that model internally, before ALL j/r/z. -/
theorem pivot_chart_ranges_of_models : Nonempty (PivotChartRangeData B b F x t c g d E) := by
  exact ⟨{
    target_open_immersion := targetChartMap_isOpenImmersion B b F x t c g d E
    source_open_immersion := sourceChartMap_isOpenImmersion B b F x t c g d E
    target_range := target_chart_range B b F x t c g d E
    source_range := source_chart_range B b F x t c g d E
    target_native := constructedNativeLaws E.target.charts (targetGraphSet B b t)
      (targetNativeMap B b F x t c g d E) (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.hom E.target_maps.scalar
    source_native := constructedNativeLaws E.source.charts (sourceGraphSet B b F x t c)
      (sourceNativeMap B b F x t c g d E)
      (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.hom E.source_maps.scalar
    target_normals := target_normal_composition B b F x t c g d E
    source_normals := source_normal_composition B b F x t c g d E }⟩


structure SameCanonicalPivotOpenRangeData : Prop where
  chart_ranges : PivotChartRangeData B b F x t c g d E
  source_subset : (sourceModelOpen B b F x t c g d E).1 ⊆
    (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base ⁻¹' d.target.targetOpen.1
  source_preimage : ∀j, (sourcePivotOpen B b F x t c g d E j).1=
    (sourceModelOpen B b F x t c g d E).1 ∩
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base ⁻¹'
        (targetPivotOpen B b F x t c g d E j).1
  target_cover : (⋃j : Fin t.rank,(targetPivotOpen B b F x t c g d E j).1)=d.target.targetOpen.1
  source_cover : (⋃j : Fin t.rank,(sourcePivotOpen B b F x t c g d E j).1)=
    (sourceModelOpen B b F x t c g d E).1


/-- Entire first ranges/preimage/cover output, still for precisely the same
already-derived E. No new frame choice or desired result packet is supplied. -/
theorem pivot_open_ranges_of_models : Nonempty (SameCanonicalPivotOpenRangeData B b F x t c g d E) := by
  obtain ⟨H⟩ := pivot_chart_ranges_of_models B b F x t c g d E
  exact ⟨⟨H,source_range_subset B b F x t c g d E,source_pivot_preimage B b F x t c g d E,
    target_pivot_cover B b F x t c g d E,source_pivot_cover B b F x t c g d E⟩⟩


end SameCanonical

section OrdinaryCaller
variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  (F : X ⟶ Y) (x : X.obj.left)


private abbrev FullPivotOpenOutput
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left) : Prop :=
  ∃ (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t)
    (g : CanonicalSquareGeometry B b F x t c) (d : CanonicalNormalSectionData B b F x t c g)
    (E : SameCanonicalExplicitProductModels B b F x t c g d),
    Nonempty (SameCanonicalPivotOpenRangeData B b F x t c g d E)

/-- ONLY original BFT/b/F/x/GIVENy/hxy. Accepted920 is called ONCE before ALL
labels, chart points and native numerators. Empty strict source is allowed.
Literal intrinsic restrictions/full restricted square/overlap remain separate. -/
theorem exists_same_canonical_pivot_open_ranges
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (hxy : F.hom.left.base x=(OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y) :
    FullPivotOpenOutput B b F x y := by
  obtain ⟨t,c,g,d,⟨E⟩⟩ := exists_same_canonical_explicit_product_models B b F x y hxy
  exact ⟨t,c,g,d,E,pivot_open_ranges_of_models B b F x t c g d E⟩


end OrdinaryCaller
end
end Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
