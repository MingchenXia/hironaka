import Hironaka.Analytic.Unibranch.OriginalIntrinsicSingularLocus
import Hironaka.Analytic.Unibranch.ResolutionLocal
import Hironaka.Resolution.HironakaOriginalNonpureCanonicalSpecializations

/-!
# Actual canonical strict-resolution windows of original singular points

Only the original reduced analytic space, a singular point, and an original
open neighbourhood are inputs. The actual ambient canonical recipe and its
entire smooth-source conclusions are retained for the SAME native strict-space
projection. No global dimension bound, compactness, schedule, or comparison
packet is supplied. This is a local producer, not global embedding descent.

Blueprint FIRST: `original-local-canonical-strict-resolution.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalLocalCanonicalStrictResolution

noncomputable section

open Hironaka Hironaka.BlowupSequences
  Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaResolutionSpace
  HironakaResolutionSpaceComplex HironakaEmbeddedAnalytic
  HironakaOriginalIntrinsicNonpureRecipe HironakaOriginalLocalNonpureCanonicalResolution
  HironakaOriginalNonpureCanonicalSpecializations SourceReducedComplexSpace BlowupTowers

/-- Singularity of the ORIGINAL point internally makes a connected local
analytic carrier thin. No analytic extension outside its domain is used. -/
theorem exists_thin_localEmbedding_of_singular (X : SourceReducedComplexSpace)
    (x : X.obj.left) (hx : x ∈ intrinsicSingularLocus X.obj)
    (O : Opens X.obj.left) (hxO : x ∈ O) :
    ∃ (e : LocalEmbedding X) (c : e.carrier),
      e.toPoint c = x ∧ range e.toPoint ⊆ O ∧ interior e.carrier = ∅ := by
  obtain ⟨e, hxe, heO, heconn⟩ := LocalEmbedding.exists_domain x O.isOpen hxO
  obtain ⟨c, hcx⟩ := hxe
  let : ConnectedSpace e.ambient := isConnected_iff_connectedSpace.mp heconn
  refine ⟨e, c, hcx, heO, ?_⟩
  by_contra hthin
  have heall : e.carrier = univ :=
    e.analytic.eq_univ_of_interior_nonempty (Set.nonempty_iff_ne_empty.mpr hthin)
  have hreg : RegularAtDim (n := e.dim) e.carrier c.val e.dim := by
    simpa only [heall] using AnalyticIrreducibleComponents.regularAtDim_univ (n := e.dim) c.val
  apply hx
  refine ⟨e.dim, ?_⟩
  rw [← hcx]
  exact (OriginalIntrinsicSingularLocus.intrinsicRegularAtDim_localEmbedding_iff X e c e.dim).mpr hreg

/-- The actual analytic carrier on a restricted ambient open. -/
abbrev windowCarrier {X : SourceReducedComplexSpace} (e : LocalEmbedding X)
    (U : Opens e.ambient) : Set U :=
  (Subtype.val : U → e.ambient) ⁻¹' e.carrier

theorem windowCarrier_analytic {X : SourceReducedComplexSpace} (e : LocalEmbedding X)
    (U : Opens e.ambient) : IsComplexAnalyticSubset (n := e.dim) (windowCarrier e U) :=
  AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val e.analytic U

/-- The SAME actual reduced quotient model of the restricted original carrier. -/
def windowSpace {X : SourceReducedComplexSpace} (e : LocalEmbedding X)
    (U : Opens e.ambient) : SourceReducedComplexSpace :=
  ofClosedAnalytic (windowCarrier e U) (windowCarrier_analytic e U)

/-- Its full native open immersion into the ORIGINAL space. -/
def windowMorphism {X : SourceReducedComplexSpace} (e : LocalEmbedding X)
    (U : Opens e.ambient) : windowSpace e U ⟶ X := by
  refine ObjectProperty.homMk (Over.homMk
    (actualOpenSubspaceMap (n := e.dim) e.carrier U ≫ e.map) ?_)
  rw [Category.assoc, e.overPoint]
  exact actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)

theorem windowMorphism_isOpenImmersion {X : SourceReducedComplexSpace}
    (e : LocalEmbedding X) (U : Opens e.ambient) :
    LocallyRingedSpace.IsOpenImmersion (windowMorphism e U).hom.left := by
  let := e.isOpenImmersion
  change LocallyRingedSpace.IsOpenImmersion
    (actualOpenSubspaceMap (n := e.dim) e.carrier U ≫ e.map)
  infer_instance

@[simp] theorem windowMorphism_base {X : SourceReducedComplexSpace}
    (e : LocalEmbedding X) (U : Opens e.ambient) (v : windowCarrier e U) :
    (windowMorphism e U).hom.left.base v = e.toPoint ⟨v.val.val, v.property⟩ := rfl

/-- The restricted model sees the full ORIGINAL regular locus, in every
intrinsic dimension, on the same literal carrier. -/
theorem windowMorphism_regular_preimage {X : SourceReducedComplexSpace}
    (e : LocalEmbedding X) (U : Opens e.ambient) :
    (windowMorphism e U).hom.left.base ⁻¹' intrinsicRegularLocus X.obj =
      {v : windowCarrier e U | v.val ∉ singularSet (n := e.dim) (windowCarrier e U)} := by
  ext v
  have he := Set.ext_iff.mp
    (OriginalIntrinsicSingularLocus.intrinsicSingularLocus_localEmbedding_preimage X e)
    (⟨v.val.val, v.property⟩ : e.carrier)
  rw [HironakaResolutionSpaceLocal.singularSet_preimage_val U]
  change e.toPoint ⟨v.val.val, v.property⟩ ∈ intrinsicRegularLocus X.obj ↔
    v.val.val ∉ singularSet (n := e.dim) e.carrier
  simpa only [Set.mem_preimage, intrinsicSingularLocus, Set.mem_compl_iff, not_not] using not_congr he

/-- The SAME full native strict-space projection is an isomorphism over
the inverse image of the ORIGINAL regular locus in the original window. -/
theorem resolutionMorphism_isIsoOver_originalRegularLocus
    {X : SourceReducedComplexSpace} (e : LocalEmbedding X) (U : Opens e.ambient)
    {D : CMfd.{0} e.dim} {T : BlowupTowers.BlowupTower (CMfd.of (n := e.dim) U) D}
    {Ef : List (Set D)}
    (h : IsStrictTransformResolution e.dim (windowCarrier e U) T.proj Ef) :
    IsIsoOver (resolutionMorphism (windowCarrier_analytic e U) h)
      ((windowMorphism e U).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) := by
  rw [windowMorphism_regular_preimage]
  exact resolutionMap_isIsoOver h (windowCarrier_analytic e U).isClosed

/-- Ordinary original singular-point data internally produces one canonical
ambient tower, its full smooth-source family, and the SAME native strict
resolution with properness, surjectivity and original-Reg inverse. -/
theorem exists_original_local_canonical_strict_resolution
    (X : SourceReducedComplexSpace) (x : X.obj.left)
    (hx : x ∈ intrinsicSingularLocus X.obj) (O : Opens X.obj.left) (hxO : x ∈ O) :
    ∃ (e : LocalEmbedding X) (U : Opens e.ambient)
      (D : CMfd.{0} e.dim) (T : BlowupTowers.BlowupTower (CMfd.of (n := e.dim) U) D)
      (Ef : List (Set D))
      (h : IsStrictTransformResolution e.dim (windowCarrier e U) T.proj Ef),
      x ∈ range (windowMorphism e U).hom.left.base ∧
      range (windowMorphism e U).hom.left.base ⊆ (O : Set X.obj.left) ∧
      IntrinsicOrderedRecipe (windowCarrier e U) [] T Ef ∧
      HasElementaryGeometry (windowCarrier e U) [] T Ef ∧
      RestrictEmptyTower.CentresOver (singularSet (n := e.dim) (windowCarrier e U)) T ∧
      HasIntrinsicSmoothSources (windowCarrier e U) [] T Ef ∧
      HasExactEmptyBoundarySmoothSources (windowCarrier e U) T Ef ∧
      IsResolution (resolutionMorphism (windowCarrier_analytic e U) h) ∧
      Function.Surjective (resolutionMorphism (windowCarrier_analytic e U) h).hom.left.base ∧
      IsProperMap (resolutionMorphism (windowCarrier_analytic e U) h).hom.left.base ∧
      IsIsoOver (resolutionMorphism (windowCarrier_analytic e U) h)
        ((windowMorphism e U).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) ∧
      ∀ y : strictTransform e.dim T.proj (windowCarrier e U),
        ((resolutionMorphism (windowCarrier_analytic e U) h).hom.left.base y).val = T.proj y.val := by
  obtain ⟨e, c, hcx, heO, hthin⟩ := exists_thin_localEmbedding_of_singular X x hx O hxO
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.ambient.isOpen c.val.val c.val.property
  have hr : 0 < ε / 2 := half_pos hε
  have hcl : Metric.closedBall c.val.val (ε / 2) ⊆ e.ambient :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  let U : Opens e.ambient :=
    ⟨(Subtype.val : e.ambient → ComplexModel e.dim) ⁻¹' Metric.ball c.val.val (ε / 2),
      Metric.isOpen_ball.preimage continuous_subtype_val⟩
  let K : Set e.ambient :=
    (Subtype.val : e.ambient → ComplexModel e.dim) ⁻¹' Metric.closedBall c.val.val (ε / 2)
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff]
    have himg : (Subtype.val : e.ambient → ComplexModel e.dim) '' K =
        Metric.closedBall c.val.val (ε / 2) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z, hcl hz⟩, hz, rfl⟩
    rw [himg]
    exact isCompact_closedBall _ _
  have hUK : (U : Set e.ambient) ⊆ K := preimage_mono Metric.ball_subset_closedBall
  obtain ⟨D, T, Ef, hRecipe, hover, hGeom, hExc, hSing, hSources, hExact⟩ :=
    exists_original_local_nonpure_empty_boundary_resolution
      (X := CMfd.of (n := e.dim) e.ambient)
      e.carrier e.analytic hthin U hK hUK
  have hProper : IsProperMap T.proj := HironakaLocalPrincipalization.isProperMap_proj T
  have hGeomSave := hGeom
  obtain ⟨hadm, hsnc, _hExcSub, _hNew, _hBad, hiso, hSM, _hParts⟩ := hGeom
  have hadm' : HironakaAdmissibleSequence.IsAdmissibleBlowupSequence
      e.dim U [] (singularSet (n := e.dim) (windowCarrier e U)) D T.proj Ef := by
    simpa using hadm
  have hiso' : IsIsomorphismOver e.dim T.proj
      (singularSet (n := e.dim) (windowCarrier e U))ᶜ := by
    simpa using hiso
  let h : IsStrictTransformResolution e.dim (windowCarrier e U) T.proj Ef :=
    isStrictTransformResolution_of_data (windowCarrier_analytic e U)
      hadm' hsnc hExc hSing hiso' hSM hProper.isClosedMap
  refine ⟨e, U, D, T, Ef, h, ?_, ?_, hRecipe, hGeomSave, hover, hSources, hExact,
    isResolution_resolutionMorphism_of_isProperMap (windowCarrier_analytic e U) h hProper,
    resolutionMap_surjective h, HironakaResolutionSpaceLocal.resolutionMap_isProperMap_of_isProperMap h hProper,
    resolutionMorphism_isIsoOver_originalRegularLocus e U h, fun _ => rfl⟩
  · have hcU : c.val ∈ U := Metric.mem_ball_self hr
    refine ⟨⟨⟨c.val, hcU⟩, c.property⟩, ?_⟩
    exact hcx
  · rintro _ ⟨v, rfl⟩
    exact heO ⟨⟨v.val.val, v.property⟩, rfl⟩

end
end Hironaka.Analytic.Unibranch.OriginalLocalCanonicalStrictResolution
