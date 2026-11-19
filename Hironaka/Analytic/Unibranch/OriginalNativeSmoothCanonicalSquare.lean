import Hironaka.Analytic.Unibranch.OriginalNativeSmoothThinWindow
import Hironaka.Analytic.Unibranch.OriginalLocalCanonicalStrictResolution

/-! Actual local canonical strict-resolution squares from ordinary native
smooth maps. Independent global canonical assignments are not identified.
Blueprint first: `original-native-smooth-canonical-square.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothCanonicalSquare
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka BlowupTowers HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaSmoothSubmersionContactParameterCharts HironakaSmoothSubmersionHistoricalCompanionMasks
  HironakaOriginalIntrinsicNonpureRecipe HironakaOriginalLocalNonpureCanonicalResolution
  HironakaOriginalNonpureCanonicalSpecializations HironakaSmoothSubmersionCartesianTower
  HironakaResolutionSpace HironakaResolutionSpaceComplex HironakaEmbeddedAnalytic
  HironakaG11IntrinsicRegularOpenImmersion SourceReducedComplexSpace
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothThinWindow

variable {X Y : SourceReducedComplexSpace} {f : X ⟶ Y} {x : X.obj.left}
  {V : Opens X.obj.left} {T : Opens Y.obj.left}

def sourceOpen (w : ThinWindow f x V T) (U : Opens w.target.ambient) : Opens w.sourceAmbient :=
  ⟨w.ambientMap ⁻¹' (U : Set w.target.ambient),U.isOpen.preimage w.submersion.contMDiff.continuous⟩

def baseMap (w : ThinWindow f x V T) (U : Opens w.target.ambient) : sourceOpen w U → U :=
  restrictedOpenMap (X := CMfd.of (n := w.target.dim) w.target.ambient) (Y := w.sourceAmbient)
    (f := w.ambientMap) (sourceOpen w U) U (fun _ hx => hx)

theorem baseMap_submersion (w : ThinWindow f x V T) (U : Opens w.target.ambient) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel w.sourceDim) 𝓘(ℂ,ComplexModel w.target.dim) ∞ (baseMap w U) :=
  restrictedOpenMap_isSubmersion (X := CMfd.of (n := w.target.dim) w.target.ambient)
    (Y := w.sourceAmbient) w.submersion (sourceOpen w U) U (fun _ hx => hx)

def targetCarrier (w : ThinWindow f x V T) (U : Opens w.target.ambient) : Set U :=
  (Subtype.val : U → w.target.ambient) ⁻¹' w.target.carrier

def sourceCarrier (w : ThinWindow f x V T) (U : Opens w.target.ambient) : Set (sourceOpen w U) :=
  baseMap w U ⁻¹' targetCarrier w U

theorem targetCarrier_analytic (w : ThinWindow f x V T) (U : Opens w.target.ambient) :
    IsComplexAnalyticSubset (n := w.target.dim) (targetCarrier w U) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val w.target.analytic

theorem sourceCarrier_analytic (w : ThinWindow f x V T) (U : Opens w.target.ambient) :
    IsComplexAnalyticSubset (n := w.sourceDim) (sourceCarrier w U) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (baseMap_submersion w U).contMDiff
    (targetCarrier_analytic w U)

def targetSpace (w : ThinWindow f x V T) (U : Opens w.target.ambient) : SourceReducedComplexSpace :=
  ofClosedAnalytic (targetCarrier w U) (targetCarrier_analytic w U)

def sourceSpace (w : ThinWindow f x V T) (U : Opens w.target.ambient) : SourceReducedComplexSpace :=
  ofClosedAnalytic (sourceCarrier w U) (sourceCarrier_analytic w U)

def targetInclusion (w : ThinWindow f x V T) (U : Opens w.target.ambient) : targetSpace w U ⟶ Y :=
  OriginalLocalCanonicalStrictResolution.windowMorphism w.target U

def sourceInclusion (w : ThinWindow f x V T) (U : Opens w.target.ambient) : sourceSpace w U ⟶ X := by
  let j : sourceSpace w U ⟶ inverseSpace w.target w.sourceAmbient w.ambientMap w.submersion :=
    ObjectProperty.homMk (Over.homMk
    (actualOpenSubspaceMap (w.ambientMap ⁻¹' w.target.carrier) (sourceOpen w U))
    (actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)))
  exact j ≫ w.sourceInclusion

def baseProjection (w : ThinWindow f x V T) (U : Opens w.target.ambient) : sourceSpace w U ⟶ targetSpace w U :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (baseMap_submersion w U).contMDiff (fun _ hx => hx))
    (actualSubspaceMap_point (baseMap_submersion w U).contMDiff (fun _ hx => hx)))

theorem sourceInclusion_isOpenImmersion (w : ThinWindow f x V T) (U : Opens w.target.ambient) :
    LocallyRingedSpace.IsOpenImmersion (sourceInclusion w U).hom.left :=
  @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    (actualOpenSubspaceMap (w.ambientMap ⁻¹' w.target.carrier) (sourceOpen w U))
    (actualOpenSubspaceMap_isOpenImmersion _ _) w.sourceInclusion.hom.left w.isOpenImmersion

theorem targetInclusion_isOpenImmersion (w : ThinWindow f x V T) (U : Opens w.target.ambient) :
    LocallyRingedSpace.IsOpenImmersion (targetInclusion w U).hom.left :=
  OriginalLocalCanonicalStrictResolution.windowMorphism_isOpenImmersion w.target U

theorem base_square (w : ThinWindow f x V T) (U : Opens w.target.ambient) :
    sourceInclusion w U ≫ f = baseProjection w U ≫ targetInclusion w U := by
  change (_ ≫ w.sourceInclusion) ≫ f = _
  rw [Category.assoc,w.square]
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change actualOpenSubspaceMap (w.ambientMap ⁻¹' w.target.carrier) (sourceOpen w U) ≫
      (actualSubspaceMap w.submersion.contMDiff (fun _ hx => hx) ≫ w.target.map) =
    actualSubspaceMap (baseMap_submersion w U).contMDiff (fun _ hx => hx) ≫
      (actualOpenSubspaceMap w.target.carrier U ≫ w.target.map)
  have hl := actualSubspaceMap_comp (n := w.sourceDim) (m := w.sourceDim) (p := w.target.dim)
    (C := sourceCarrier w U) (D := w.ambientMap ⁻¹' w.target.carrier) (E := w.target.carrier)
    (f := (Subtype.val : sourceOpen w U → w.sourceAmbient)) (g := w.ambientMap)
    contMDiff_subtype_val w.submersion.contMDiff (fun _ hx => hx) (fun _ hx => hx)
  have hr := actualSubspaceMap_comp (n := w.sourceDim) (m := w.target.dim) (p := w.target.dim)
    (C := sourceCarrier w U) (D := targetCarrier w U) (E := w.target.carrier)
    (f := baseMap w U) (g := (Subtype.val : U → w.target.ambient))
    (baseMap_submersion w U).contMDiff contMDiff_subtype_val (fun _ hx => hx) (fun _ hx => hx)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ w.target.map) (hl.symm.trans hr)).trans (Category.assoc _ _ _))

/-- The same original point is retained whenever the actual target coordinate is in U. -/
theorem sourceInclusion_covers (w : ThinWindow f x V T) (U : Opens w.target.ambient)
    (hu : w.ambientMap w.sourcePoint.val ∈ U) :
    x ∈ range (sourceInclusion w U).hom.left.base :=
  ⟨⟨⟨w.sourcePoint.val,hu⟩,w.sourcePoint.property⟩,w.point⟩

theorem sourceInclusion_range (w : ThinWindow f x V T) (U : Opens w.target.ambient) :
    range (sourceInclusion w U).hom.left.base ⊆ (V : Set X.obj.left) := by
  rintro _ ⟨z,rfl⟩
  exact w.source_range ⟨⟨z.val.val,z.property⟩,rfl⟩

theorem targetInclusion_range (w : ThinWindow f x V T) (U : Opens w.target.ambient) :
    range (targetInclusion w U).hom.left.base ⊆ (T : Set Y.obj.left) := by
  rintro _ ⟨z,rfl⟩
  exact w.target_range ⟨⟨z.val.val,z.property⟩,rfl⟩

/-- Whole actual empty-boundary geometry supplies the same strict-resolution predicate. -/
theorem strictResolution_of_geometry {n : ℕ} {A D : CMfd.{0} n} {W : Set A}
    (hW : IsComplexAnalyticSubset (n := n) W) {R : BlowupTower A D} {E : List (Set D)}
    (hGeom : HasElementaryGeometry W [] R E) : IsStrictTransformResolution n W R.proj E := by
  obtain ⟨hExc,hSing⟩ := empty_boundary_geometry_exact hGeom
  obtain ⟨hadm,hsnc,_hExcSub,_hNew,_hBad,hiso,hSM,_rest⟩ := hGeom
  exact isStrictTransformResolution_of_data hW (by simpa using hadm) hsnc hExc hSing
    (by simpa using hiso) hSM (HironakaLocalPrincipalization.isProperMap_proj R).isClosedMap

/-- Any actual base open immersion reads the FULL original regular locus. -/
theorem regular_preimage {Z : SourceReducedComplexSpace} {n : ℕ} {A : CMfd.{0} n}
    {W : Set A} (hW : IsComplexAnalyticSubset (n := n) W)
    (j : ofClosedAnalytic W hW ⟶ Z) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) :
    j.hom.left.base ⁻¹' intrinsicRegularLocus Z.obj = {z : W | z.val ∉ singularSet (n := n) W} := by
  ext z
  have hreg := mem_intrinsicRegularLocus_map_iff j.hom.left hj (Over.w j.hom) z
  have hsing := not_congr (HironakaG11PresPresentation.mem_intrinsicSingularLocus_ofClosedAnalytic_iff hW z)
  change (¬¬z ∈ intrinsicRegularLocus (ofClosedAnalytic W hW).obj) ↔ z.val ∉ singularSet (n := n) W at hsing
  exact hreg.trans (not_not.symm.trans hsing)

/-- Properness, surjectivity and FULL original-Reg protection of the SAME native projection. -/
theorem resolution_original_properties {Z : SourceReducedComplexSpace} {n : ℕ} {A D : CMfd.{0} n}
    {W : Set A} (hW : IsComplexAnalyticSubset (n := n) W)
    {R : BlowupTower A D} {E : List (Set D)} (hGeom : HasElementaryGeometry W [] R E)
    (j : ofClosedAnalytic W hW ⟶ Z) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) :
    let p := resolutionMorphism hW (strictResolution_of_geometry hW hGeom)
    IsResolution p ∧ Function.Surjective p.hom.left.base ∧ IsProperMap p.hom.left.base ∧
      IsIsoOver p (j.hom.left.base ⁻¹' intrinsicRegularLocus Z.obj) := by
  dsimp only
  let h := strictResolution_of_geometry hW hGeom
  have hp := HironakaLocalPrincipalization.isProperMap_proj R
  refine ⟨isResolution_resolutionMorphism_of_isProperMap hW h hp,resolutionMap_surjective h,
    HironakaResolutionSpaceLocal.resolutionMap_isProperMap_of_isProperMap h hp,?_⟩
  rw [regular_preimage hW j hj]
  exact resolutionMap_isIsoOver h hW.isClosed

/-- Actual local canonical OUTPUT with literal source history/boundary, not an assigned global functor. -/
structure LocalCanonicalPullback (f : X ⟶ Y) (x : X.obj.left)
    (V : Opens X.obj.left) (T : Opens Y.obj.left) where
  window : ThinWindow f x V T
  neighbourhood : Opens window.target.ambient
  point_mem : window.ambientMap window.sourcePoint.val ∈ neighbourhood
  targetEnd : CMfd.{0} window.target.dim
  targetTower : BlowupTower (CMfd.of (n := window.target.dim) neighbourhood) targetEnd
  boundary : List (Set targetEnd)
  targetRecipe : IntrinsicOrderedRecipe (targetCarrier window neighbourhood) [] targetTower boundary
  targetGeometry : HasElementaryGeometry (targetCarrier window neighbourhood) [] targetTower boundary
  targetSources : HasIntrinsicSmoothSources (targetCarrier window neighbourhood) [] targetTower boundary
  sourceEnd : CMfd.{0} window.sourceDim
  sourceTower : BlowupTower (CMfd.of (n := window.sourceDim) (sourceOpen window neighbourhood)) sourceEnd
  lift : sourceEnd → targetEnd
  history : IsActualTowerPullback (baseMap window neighbourhood) sourceTower targetTower lift
  sourceRecipe : IntrinsicOrderedRecipe (sourceCarrier window neighbourhood) [] sourceTower (boundary.map (lift ⁻¹' ·))
  sourceGeometry : HasElementaryGeometry (sourceCarrier window neighbourhood) [] sourceTower (boundary.map (lift ⁻¹' ·))
  strict_preimage_eq : strictTransform window.sourceDim sourceTower.proj (sourceCarrier window neighbourhood) =
    lift ⁻¹' strictTransform window.target.dim targetTower.proj (targetCarrier window neighbourhood)

/-- Only ordinary native smooth input and an original singular image are supplied. -/
theorem exists_local_canonical_pullback (f : X ⟶ Y) (x : X.obj.left) (hsm : IsSmoothAt f x)
    (hsing : f.hom.left.base x ∈ intrinsicSingularLocus Y.obj)
    (V : Opens X.obj.left) (T : Opens Y.obj.left) (hxV : x ∈ V) (hfxT : f.hom.left.base x ∈ T) :
    Nonempty (LocalCanonicalPullback f x V T) := by
  obtain ⟨w⟩ := exists_thin_window f x hsm hsing V T hxV hfxT
  let c : w.target.carrier := ⟨w.ambientMap w.sourcePoint.val,w.sourcePoint.property⟩
  obtain ⟨U,hcU,_hCompact,D,R,E,hRecipe,_hover,hGeom,_hExc,_hSing,hSources,_hExact⟩ :=
    exists_original_local_nonpure_empty_boundary_resolution_near_compact
      (X := CMfd.of (n := w.target.dim) w.target.ambient)
      w.target.carrier w.target.analytic w.thin (isCompact_singleton (x := c.val))
  have hu : w.ambientMap w.sourcePoint.val ∈ U := hcU (Set.mem_singleton _)
  obtain ⟨C,Q,g,hRecipeQ,hGeomQ,hActual,hStrict,_hParts,_hg,_hlen,_hcomm,_hcart,_hIndependent⟩ :=
    hSources (CMfd.of (n := w.sourceDim) (sourceOpen w U)) (baseMap w U) (baseMap_submersion w U)
  exact ⟨⟨w,U,hu,D,R,E,hRecipe,hGeom,hSources,C,Q,g,hActual,hRecipeQ,hGeomQ,hStrict⟩⟩

namespace LocalCanonicalPullback
variable (a : LocalCanonicalPullback f x V T)

def targetStrictSpace : SourceReducedComplexSpace :=
  ofClosedAnalytic (strictTransform a.window.target.dim a.targetTower.proj
    (targetCarrier a.window a.neighbourhood))
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (strictResolution_of_geometry (targetCarrier_analytic a.window a.neighbourhood) a.targetGeometry).isClosedSubmanifold)

def sourceStrictSpace : SourceReducedComplexSpace :=
  ofClosedAnalytic (strictTransform a.window.sourceDim a.sourceTower.proj
    (sourceCarrier a.window a.neighbourhood))
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (strictResolution_of_geometry (sourceCarrier_analytic a.window a.neighbourhood) a.sourceGeometry).isClosedSubmanifold)

def targetResolution : targetStrictSpace a ⟶ targetSpace a.window a.neighbourhood :=
  resolutionMorphism (targetCarrier_analytic a.window a.neighbourhood)
    (strictResolution_of_geometry (targetCarrier_analytic a.window a.neighbourhood) a.targetGeometry)

def sourceResolution : sourceStrictSpace a ⟶ sourceSpace a.window a.neighbourhood :=
  resolutionMorphism (sourceCarrier_analytic a.window a.neighbourhood)
    (strictResolution_of_geometry (sourceCarrier_analytic a.window a.neighbourhood) a.sourceGeometry)

private theorem lift_mapsTo : ∀ z ∈ strictTransform a.window.sourceDim a.sourceTower.proj
    (sourceCarrier a.window a.neighbourhood),
    a.lift z ∈ strictTransform a.window.target.dim a.targetTower.proj (targetCarrier a.window a.neighbourhood) := by
  intro z hz
  exact Set.ext_iff.mp a.strict_preimage_eq z |>.mp hz

/-- Genuine original quotient morphism of the SAME two whole strict carriers. -/
def nativeLift : sourceStrictSpace a ⟶ targetStrictSpace a :=
  ObjectProperty.homMk (Over.homMk (actualSubspaceMap a.history.isSubmersion.contMDiff (lift_mapsTo a))
    (actualSubspaceMap_point a.history.isSubmersion.contMDiff (lift_mapsTo a)))

/-- Full native resolution square, derived from actual chronological history. -/
theorem native_square :
    sourceResolution a ≫ baseProjection a.window a.neighbourhood = nativeLift a ≫ targetResolution a := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change actualSubspaceMap
      (strictResolution_of_geometry (sourceCarrier_analytic a.window a.neighbourhood) a.sourceGeometry).contMDiff _ ≫
      actualSubspaceMap (baseMap_submersion a.window a.neighbourhood).contMDiff _ =
    actualSubspaceMap a.history.isSubmersion.contMDiff (lift_mapsTo a) ≫
      actualSubspaceMap
        (strictResolution_of_geometry (targetCarrier_analytic a.window a.neighbourhood) a.targetGeometry).contMDiff _
  let hS := strictResolution_of_geometry (sourceCarrier_analytic a.window a.neighbourhood) a.sourceGeometry
  let hT := strictResolution_of_geometry (targetCarrier_analytic a.window a.neighbourhood) a.targetGeometry
  have hl := actualSubspaceMap_comp (n := a.window.sourceDim) (m := a.window.sourceDim) (p := a.window.target.dim)
    (C := strictTransform a.window.sourceDim a.sourceTower.proj (sourceCarrier a.window a.neighbourhood))
    (D := sourceCarrier a.window a.neighbourhood) (E := targetCarrier a.window a.neighbourhood)
    (f := a.sourceTower.proj) (g := baseMap a.window a.neighbourhood)
    hS.contMDiff (baseMap_submersion a.window a.neighbourhood).contMDiff
    (fun _ hz => hS.strictTransform_subset_preimage hz) (fun _ hx => hx)
  have hr := actualSubspaceMap_comp (n := a.window.sourceDim) (m := a.window.target.dim) (p := a.window.target.dim)
    (C := strictTransform a.window.sourceDim a.sourceTower.proj (sourceCarrier a.window a.neighbourhood))
    (D := strictTransform a.window.target.dim a.targetTower.proj (targetCarrier a.window a.neighbourhood))
    (E := targetCarrier a.window a.neighbourhood) (f := a.lift) (g := a.targetTower.proj)
    a.history.isSubmersion.contMDiff hT.contMDiff (lift_mapsTo a)
    (fun _ hz => hT.strictTransform_subset_preimage hz)
  exact hl.symm.trans ((actualSubspaceMap_congr (n := a.window.sourceDim) (m := a.window.target.dim)
    (M := a.sourceEnd) (N := a.neighbourhood)
    (funext fun z => (a.history.proj_comm z).symm) _ _ _ _).trans hr)

/-- The SAME full native equation lies over the ORIGINAL ordinary smooth map. -/
theorem original_square :
    sourceResolution a ≫ (sourceInclusion a.window a.neighbourhood ≫ f) =
      nativeLift a ≫ (targetResolution a ≫ targetInclusion a.window a.neighbourhood) := by
  rw [base_square,← Category.assoc,native_square,Category.assoc]

theorem target_properties :
    IsResolution (targetResolution a) ∧ Function.Surjective (targetResolution a).hom.left.base ∧
      IsProperMap (targetResolution a).hom.left.base ∧
      IsIsoOver (targetResolution a)
        ((targetInclusion a.window a.neighbourhood).hom.left.base ⁻¹' intrinsicRegularLocus Y.obj) :=
  resolution_original_properties (targetCarrier_analytic a.window a.neighbourhood) a.targetGeometry
    (targetInclusion a.window a.neighbourhood) (targetInclusion_isOpenImmersion a.window a.neighbourhood)

theorem source_properties :
    IsResolution (sourceResolution a) ∧ Function.Surjective (sourceResolution a).hom.left.base ∧
      IsProperMap (sourceResolution a).hom.left.base ∧
      IsIsoOver (sourceResolution a)
        ((sourceInclusion a.window a.neighbourhood).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) :=
  resolution_original_properties (sourceCarrier_analytic a.window a.neighbourhood) a.sourceGeometry
    (sourceInclusion a.window a.neighbourhood) (sourceInclusion_isOpenImmersion a.window a.neighbourhood)

end LocalCanonicalPullback

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothCanonicalSquare
