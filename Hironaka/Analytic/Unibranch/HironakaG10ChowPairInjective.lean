import Hironaka.Analytic.Unibranch.EmbeddedGeometricIdealOriginalObject
import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupOriginalObject
import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
import Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
import Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
import Hironaka.Resolution.HironakaG10ChowPairRelations
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalAmbientLifting
import Hironaka.Resolution.HironakaNativePulledIdealComposition

/-!
# Pair-injectivity of the one-step strict transform (global flattening, route step N2)

For a proper `f : Y ⟶ X` of reduced complex spaces and a finite-type ideal `b : B ⟶ 𝒪_X` with
dense unit locus, the one-step strict transform of the global flattening algorithm
(`HironakaG10ChowOneStepStrictTransform`: `σ : Bl_B X ⟶ X`, `q : Bl_{f*B} Y ⟶ Y` the geometric
blowup of the pulled ideal, `p` from the universal property) is pair-injective: `(p, q)` is
injective (`strict_pairInjective`).  Hence it satisfies all six fields of `IsStrictTransform`
(`isStrictTransform_step`) and is flattening data (`isFlatteningData_step`), and the pair-injectivity
hypothesis of `HironakaG10ChowFlatteningDriver.exists_flattening_of_rule` is discharged
(`stage_pairInjective`, `exists_flattening_of_rule'`).

Over the unit locus this is `strict_pairInjective_of_mem`.  Over the nonunit locus
(`eq_of_pair_model`, for ARBITRARY local model data of the two glued blowups, so no private chart
structure is used): both points lie in one Y-side chart, a strict transform in a manifold blowup
`π' : Z' → M'` of a carrier `W'`, over one point `w₀ ∈ C'`; their common image lies in one X-side
chart.  The composite `J' ≫ f`, restricted to the part of `W'` mapped into the X-side chart, lifts
through the open immersion `J` and has a local ambient holomorphic representative `G`
(`exists_local_ambient_representative`).  The model equations of both charts, the composition of
native pulled ideals and the ideal dictionary for ambient maps give the equality of the two
restricted pulled centre ideals at `w₀`; the chart-level theorem
`HironakaG10ChowPairRelations.eq_of_pair_of_ideal_eq` concludes.
-/

set_option autoImplicit false

open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowPairInjective

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces HironakaSingularSubspaceBlowupLift
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  SourceReducedComplexSpace EmbeddedIdealBlowupNonunitLocus BlowupStrictSubmanifold
  HironakaActualAnalyticSubspaceLocalFunctions

noncomputable section

section Model

variable {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  {ι : Type} {n : ι → ℕ} {M Z : ι → Type} [∀ i, TopologicalSpace (M i)] [∀ i, TopologicalSpace (Z i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (M i)] [∀ i, IsComplexManifold (n i) (M i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (Z i)] [∀ i, IsComplexManifold (n i) (Z i)]
  {C W : ∀ i, Set (M i)} {π : ∀ i, Z i → M i}
  (hW : ∀ i, IsComplexAnalyticSubset (n := n i) (W i))
  (hπ : ∀ i, IsBlowupAlong (n i) (C i) (π i))
  (J : ∀ i, ofClosedAnalytic (W i) (hW i) ⟶ X)
  [hJopen : ∀ i, LocallyRingedSpace.IsOpenImmersion (J i).hom.left]
  (hd : ∀ i, W i ⊆ closure (W i \ C i))
  (hJ : ∀ i (y : W i),
    Ideal.map ((actualSubspaceInclusion (n := n i) (W i)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n i) (C i)) y.val) =
        nativePulledIdealStalkIdeal (J i).hom.left B b y)
  (hcover : ∀ x : X.obj.left, ∃ (i : ι) (w : W i), (J i).hom.left.base w = x)
  {κ : Type} {n' : κ → ℕ} {M' Z' : κ → Type} [∀ j, TopologicalSpace (M' j)]
  [∀ j, TopologicalSpace (Z' j)]
  [∀ j, ChartedSpace (ComplexModel (n' j)) (M' j)] [∀ j, IsComplexManifold (n' j) (M' j)]
  [∀ j, ChartedSpace (ComplexModel (n' j)) (Z' j)] [∀ j, IsComplexManifold (n' j) (Z' j)]
  {C' W' : ∀ j, Set (M' j)} {π' : ∀ j, Z' j → M' j}
  (hW' : ∀ j, IsComplexAnalyticSubset (n := n' j) (W' j))
  (hπ' : ∀ j, IsBlowupAlong (n' j) (C' j) (π' j))
  (J' : ∀ j, ofClosedAnalytic (W' j) (hW' j) ⟶ Y)
  [hJ'open : ∀ j, LocallyRingedSpace.IsOpenImmersion (J' j).hom.left]
  (hJ' : ∀ j (y : W' j),
    Ideal.map ((actualSubspaceInclusion (n := n' j) (W' j)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n' j) (C' j)) y.val) =
        nativePulledIdealStalkIdeal (J' j).hom.left (nativePulledIdealModule f.hom.left B b)
          (nativePulledIdealInclusion f.hom.left B b) y)
  (hcover' : ∀ y : Y.obj.left, ∃ (j : κ) (w : W' j), (J' j).hom.left.base w = y)

/-- The glued strict transform (geometric blowup of the pulled ideal). -/
abbrev strictObj : SourceReducedComplexSpace :=
  EmbeddedGeometricIdealOriginalObject.sourceObject hW' hπ' J'
    (nativePulledIdealModule f.hom.left B b) (nativePulledIdealInclusion f.hom.left B b) hJ' hcover'

/-- The glued blowup of `X`. -/
abbrev blowObj : SourceReducedComplexSpace :=
  EmbeddedIdealBlowupOriginalObject.sourceObject hW hπ J B b hd hJ hcover

include hJ hJ' in
/-- **Pair-injectivity over the nonunit locus, for arbitrary model data.** -/
theorem eq_of_pair_model
    (P : strictObj f B b hW' hπ' J' hJ' hcover' ⟶ blowObj B b hW hπ J hd hJ hcover)
    (hP : P ≫ EmbeddedIdealBlowupOriginalObject.projectionMorphism hW hπ J B b hd hJ hcover =
      EmbeddedGeometricIdealOriginalObject.projectionMorphism hW' hπ' J'
        (nativePulledIdealModule f.hom.left B b) (nativePulledIdealInclusion f.hom.left B b)
          hJ' hcover' ≫ f)
    (a c : (strictObj f B b hW' hπ' J' hJ' hcover').obj.left)
    (hpac : P.hom.left.base a = P.hom.left.base c)
    (hqac : (EmbeddedGeometricIdealOriginalObject.projectionMorphism hW' hπ' J'
        (nativePulledIdealModule f.hom.left B b) (nativePulledIdealInclusion f.hom.left B b)
          hJ' hcover').hom.left.base a =
      (EmbeddedGeometricIdealOriginalObject.projectionMorphism hW' hπ' J'
        (nativePulledIdealModule f.hom.left B b) (nativePulledIdealInclusion f.hom.left B b)
          hJ' hcover').hom.left.base c)
    (hnu : f.hom.left.base ((EmbeddedGeometricIdealOriginalObject.projectionMorphism hW' hπ' J'
        (nativePulledIdealModule f.hom.left B b) (nativePulledIdealInclusion f.hom.left B b)
          hJ' hcover').hom.left.base a) ∈ nonunitLocus B b) :
    a = c := by
  classical
  set qg := EmbeddedGeometricIdealObjectGluing.projection hW' hπ' J'
    (nativePulledIdealModule f.hom.left B b) (nativePulledIdealInclusion f.hom.left B b) hJ'
    with hqg
  set σg := EmbeddedIdealBlowupObjectGluing.projection hW hπ J B b hd hJ with hσg
  have hq : ∀ u, (EmbeddedGeometricIdealOriginalObject.projectionMorphism hW' hπ' J'
      (nativePulledIdealModule f.hom.left B b) (nativePulledIdealInclusion f.hom.left B b)
      hJ' hcover').hom.left.base u = qg.base u := fun _ => rfl
  simp only [hq] at hqac hnu
  -- the Y-side chart through the common image point
  obtain ⟨j, w, hw⟩ := hcover' (qg.base a)
  have hrngY : ∀ u, qg.base u = qg.base a →
      u ∈ range (EmbeddedGeometricIdealObjectGluing.inclusion hW' hπ' J'
        (nativePulledIdealModule f.hom.left B b) (nativePulledIdealInclusion f.hom.left B b) hJ' j).base := by
    intro u hu
    rw [← EmbeddedGeometricIdealObjectGluing.preimage_chart_range]
    show qg.base u ∈ range (J' j).hom.left.base
    rw [hu, ← hw]
    exact mem_range_self _
  have hlocY : ∀ u, qg.base ((EmbeddedGeometricIdealObjectGluing.inclusion hW' hπ' J'
        (nativePulledIdealModule f.hom.left B b) (nativePulledIdealInclusion f.hom.left B b) hJ' j).base u) =
      (J' j).hom.left.base
        ((EmbeddedGeometricBlowup.geometricProjection (hπ' j) (hW' j).isClosed).base u) :=
    fun u => congrArg (fun H => H.base u)
      (EmbeddedGeometricIdealObjectGluing.inclusion_projection hW' hπ' J'
        (nativePulledIdealModule f.hom.left B b) (nativePulledIdealInclusion f.hom.left B b) hJ' j)
  obtain ⟨a0, ha0⟩ := hrngY a rfl
  obtain ⟨c0, hc0⟩ := hrngY c hqac.symm
  subst ha0 hc0
  -- the common base point `w₀` of the Y-side chart
  have hw0 : (EmbeddedGeometricBlowup.geometricProjection (hπ' j) (hW' j).isClosed).base a0 =
      (EmbeddedGeometricBlowup.geometricProjection (hπ' j) (hW' j).isClosed).base c0 := by
    have h := hqac
    simp only [hlocY] at h
    exact (hJ'open j).base_open.isEmbedding.injective h
  -- the X-side chart through `f y`
  have hPb : ∀ u, σg.base (P.hom.left.base u) = f.hom.left.base (qg.base u) :=
    fun u => congrArg (fun H => H.hom.left.base u) hP
  have hlocX : ∀ i u, σg.base ((EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i).base u) =
      (J i).hom.left.base ((strictTransformProjection (hπ i) (hW i).isClosed).base u) :=
    fun i u => congrArg (fun H => H.base u)
      (EmbeddedIdealBlowupObjectGluing.inclusion_projection hW hπ J B b hd hJ i)
  set inclY := EmbeddedGeometricIdealObjectGluing.inclusion hW' hπ' J'
    (nativePulledIdealModule f.hom.left B b) (nativePulledIdealInclusion f.hom.left B b) hJ' j
    with hinclY
  set gp := EmbeddedGeometricBlowup.geometricProjection (hπ' j) (hW' j).isClosed with hgp
  obtain ⟨i, v, hv⟩ := hcover (f.hom.left.base (qg.base (inclY.base a0)))
  set inclX := EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ i with hinclX
  have hrngX : P.hom.left.base (inclY.base a0) ∈ range inclX.base := by
    rw [hinclX, ← EmbeddedIdealBlowupObjectGluing.preimage_chart_range]
    show σg.base (P.hom.left.base (inclY.base a0)) ∈ range (J i).hom.left.base
    rw [hPb, ← hv]
    exact mem_range_self _
  obtain ⟨x0, hx0⟩ := hrngX
  -- the open part of the Y-side carrier mapped into the X-side chart
  have hVopen : IsOpen ((f.hom.left.base ∘ (J' j).hom.left.base) ⁻¹'
      range (J i).hom.left.base : Set (W' j)) :=
    (hJopen i).base_open.isOpen_range.preimage
      (f.hom.left.base.hom.continuous.comp (J' j).hom.left.base.hom.continuous)
  obtain ⟨U0s, hU0o, hU0⟩ := isOpen_induced_iff.mp hVopen
  let U0 : Opens (M' j) := ⟨U0s, hU0o⟩
  let S : Set U0 := (Subtype.val : U0 → M' j) ⁻¹' W' j
  let e1 : actualSubspaceLocallyRingedSpace (n := n' j) S ⟶ (ofClosedAnalytic (W' j) (hW' j)).obj.left :=
    actualOpenSubspaceMap (n := n' j) (W' j) U0
  let g : actualSubspaceLocallyRingedSpace (n := n' j) S ⟶ X.obj.left :=
    e1 ≫ (J' j).hom.left ≫ f.hom.left
  have hgr : range g.base ⊆ range (J i).hom.left.base := by
    rintro _ ⟨s, rfl⟩
    have h1 : (⟨s.val.val, s.property⟩ : W' j) ∈ (Subtype.val : W' j → M' j) ⁻¹' U0s :=
      s.val.property
    rw [hU0] at h1
    exact h1
  have hJi : LocallyRingedSpace.IsOpenImmersion (J i).hom.left := hJopen i
  let F := LocallyRingedSpace.IsOpenImmersion.lift (J i).hom.left g hgr
  have hFJ : F ≫ (J i).hom.left = g := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  have hJpt : (J i).hom.left ≫ X.obj.hom = subspacePointMap (n := n i) (W i) := Over.w (J i).hom
  have hJ'pt : (J' j).hom.left ≫ Y.obj.hom = subspacePointMap (n := n' j) (W' j) :=
    Over.w (J' j).hom
  have hfpt : f.hom.left ≫ X.obj.hom = Y.obj.hom := Over.w f.hom
  have hF : F ≫ subspacePointMap (n := n i) (W i) = subspacePointMap (n := n' j) S := by
    have h1 : F ≫ subspacePointMap (n := n i) (W i) = g ≫ X.obj.hom := by
      rw [← hJpt, ← Category.assoc, hFJ]
    have h2 : g ≫ X.obj.hom = e1 ≫ ((J' j).hom.left ≫ Y.obj.hom) := by
      simp only [g, Category.assoc, hfpt]
    have h3 : e1 ≫ ((J' j).hom.left ≫ Y.obj.hom) = e1 ≫ subspacePointMap (n := n' j) (W' j) :=
      congrArg (e1 ≫ ·) hJ'pt
    exact h1.trans (h2.trans (h3.trans (actualSubspaceMap_point _ _)))
  -- the base point in the restricted carrier and the ambient representative of `F`
  have hw0V : (gp.base a0 : W' j) ∈ (Subtype.val : W' j → M' j) ⁻¹' U0s := by
    rw [hU0]
    show f.hom.left.base ((J' j).hom.left.base (gp.base a0)) ∈ range (J i).hom.left.base
    rw [← hlocY a0, ← hv]
    exact mem_range_self _
  let s0 : S := ⟨⟨(gp.base a0).val, hw0V⟩, (gp.base a0).property⟩
  obtain ⟨T, hxT, O, hxO, G, hG, hSW, hrep⟩ :=
    HironakaSingularSubspaceBlowupCartierUniversalAmbientLifting.exists_local_ambient_representative
      (S := S) (W := W i) F hF s0
  let ιf : O → M' j := fun o => o.val.val.val
  have hι : ContMDiff 𝓘(ℂ, ComplexModel (n' j)) 𝓘(ℂ, ComplexModel (n' j)) ∞ ιf :=
    contMDiff_subtype_val.comp (contMDiff_subtype_val.comp contMDiff_subtype_val)
  have hιe : IsOpenEmbedding ιf :=
    U0.isOpen.isOpenEmbedding_subtypeVal.comp
      (T.isOpen.isOpenEmbedding_subtypeVal.comp O.isOpen.isOpenEmbedding_subtypeVal)
  let S₀ : Set O := (Subtype.val : O → T) ⁻¹' ((Subtype.val : T → U0) ⁻¹' S)
  have hSWι : ∀ o ∈ S₀, ιf o ∈ W' j := fun _ h => h
  let Ea : actualSubspaceLocallyRingedSpace (n := n' j) S₀ ⟶
      actualSubspaceLocallyRingedSpace (n := n' j) (W' j) := actualSubspaceMap hι hSWι
  let j0a := actualOpenSubspaceMap (n := n' j) ((Subtype.val : T → U0) ⁻¹' S) O
  let j0b := actualOpenSubspaceMap (n := n' j) S T
  let e1a := actualOpenSubspaceMap (n := n' j) (W' j) U0
  have hE : j0a ≫ j0b ≫ e1a = Ea := by
    apply actualSubspaceMap_eq_of_base_eq
    · have hp1 : e1a ≫ subspacePointMap (n := n' j) (W' j) =
          subspacePointMap (n := n' j) S := actualSubspaceMap_point _ _
      have hp2 : j0b ≫ subspacePointMap (n := n' j) S =
          subspacePointMap (n := n' j) ((Subtype.val : T → U0) ⁻¹' S) := actualSubspaceMap_point _ _
      have hp3 : j0a ≫ subspacePointMap (n := n' j) ((Subtype.val : T → U0) ⁻¹' S) =
          subspacePointMap (n := n' j) S₀ := actualSubspaceMap_point _ _
      rw [Category.assoc, Category.assoc, hp1, hp2, hp3]
    · exact actualSubspaceMap_point _ _
    · rfl
  let Hm : actualSubspaceLocallyRingedSpace (n := n' j) S₀ ⟶
      (ofClosedAnalytic (W i) (hW i)).obj.left := actualSubspaceMap hG hSW
  let Eo : actualSubspaceLocallyRingedSpace (n := n' j) S₀ ⟶
      (ofClosedAnalytic (W' j) (hW' j)).obj.left := Ea
  have hrep' : Hm = j0a ≫ j0b ≫ F := hrep
  have hE' : j0a ≫ j0b ≫ e1 = Eo := hE
  -- the two composites into `X` agree on the restricted carrier
  have hcomp : Hm ≫ (J i).hom.left = Eo ≫ (J' j).hom.left ≫ f.hom.left := by
    rw [hrep', Category.assoc, Category.assoc, hFJ, ← hE']
    simp only [g, Category.assoc]
  -- the equality of the two restricted pulled centre ideals at the base point
  let z₀ : S₀ := ⟨⟨⟨s0.val, hxT⟩, hxO⟩, s0.property⟩
  have heq : Ideal.map ((actualSubspaceInclusion (n := n' j) S₀).stalkMap z₀).hom
        (actualWholeSheafStalkIdeal
          (GermIdeal.pullback (m := n' j) G (vanishingIdeal (n := n i) (C i))) z₀.val) =
      Ideal.map ((actualSubspaceInclusion (n := n' j) S₀).stalkMap z₀).hom
        (actualWholeSheafStalkIdeal
          (GermIdeal.pullback (m := n' j) ιf (vanishingIdeal (n := n' j) (C' j))) z₀.val) := by
    have hL := HironakaSingularSubspaceBlowupCartier.map_actualSubspace_stalk_ideal_pullback hG hSW
      (vanishingIdeal (n := n i) (C i))
      (VanishingIdealCoherent.isCoherent_vanishingIdeal (hπ i).1) z₀
    have hR := HironakaSingularSubspaceBlowupCartier.map_actualSubspace_stalk_ideal_pullback hι hSWι
      (vanishingIdeal (n := n' j) (C' j))
      (VanishingIdealCoherent.isCoherent_vanishingIdeal (hπ' j).1) z₀
    have h1 : Ideal.map ((actualSubspaceMap hG hSW).stalkMap z₀).hom
        (Ideal.map ((actualSubspaceInclusion (n := n i) (W i)).stalkMap
          (actualSubspaceMapTop hG hSW z₀)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n i) (C i)) (G z₀.val))) =
        nativePulledIdealStalkIdeal (Hm ≫ (J i).hom.left) B b z₀ := by
      rw [HironakaG10ChowGermIdealDictionary.nativePulledIdealStalkIdeal_comp B b Hm (J i).hom.left z₀]
      exact congrArg (Ideal.map (Hm.stalkMap z₀).hom) (hJ i (Hm.base z₀))
    have h2 : Ideal.map ((actualSubspaceMap hι hSWι).stalkMap z₀).hom
        (Ideal.map ((actualSubspaceInclusion (n := n' j) (W' j)).stalkMap
          (actualSubspaceMapTop hι hSWι z₀)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n' j) (C' j)) (ιf z₀.val))) =
        nativePulledIdealStalkIdeal (Eo ≫ (J' j).hom.left ≫ f.hom.left) B b z₀ := by
      rw [HironakaG10ChowGermIdealDictionary.nativePulledIdealStalkIdeal_comp B b Eo
        ((J' j).hom.left ≫ f.hom.left) z₀,
        ← HironakaNativePulledIdealComposition.stalkIdeal_comp f.hom.left (J' j).hom.left B b]
      exact congrArg (Ideal.map (Eo.stalkMap z₀).hom) (hJ' j (Eo.base z₀))
    have hc : nativePulledIdealStalkIdeal (Hm ≫ (J i).hom.left) B b z₀ =
        nativePulledIdealStalkIdeal (Eo ≫ (J' j).hom.left ≫ f.hom.left) B b z₀ :=
      congrArg (fun H : actualSubspaceLocallyRingedSpace (n := n' j) S₀ ⟶ X.obj.left =>
        nativePulledIdealStalkIdeal H B b z₀) hcomp
    exact hL.symm.trans (h1.trans (hc.trans (h2.symm.trans hR)))
  -- the map `Q` from the Y-side strict transform to the X-side blowup manifold
  have hixe : IsOpenEmbedding inclX.base :=
    (EmbeddedIdealBlowupObjectGluing.inclusion_isOpenImmersion hW hπ J B b hd hJ i).base_open
  let inv := @Function.invFun _ _ ⟨x0⟩ inclX.base
  have hinvc : ContinuousAt inv (inclX.base x0) := by
    rw [← hixe.continuousAt_iff]
    have hid : inv ∘ inclX.base = id :=
      funext fun u => @Function.leftInverse_invFun _ _ ⟨x0⟩ _ hixe.injective u
    rw [hid]
    exact continuousAt_id
  let Q : geoStrictTransform (π' j) (C' j) (W' j) → Z i := fun z =>
    (show strictTransform (n i) (π i) (W i) from inv (P.hom.left.base (inclY.base z))).val
  have hPc : Continuous fun z : geoStrictTransform (π' j) (C' j) (W' j) =>
      P.hom.left.base (inclY.base z) :=
    P.hom.left.base.hom.continuous.comp inclY.base.hom.continuous
  have hQcont : ∀ z, P.hom.left.base (inclY.base z) = inclX.base x0 → ContinuousAt Q z := by
    intro z hz
    have h1 : ContinuousAt inv (P.hom.left.base (inclY.base z)) := hz ▸ hinvc
    have h2 : ContinuousAt (fun z => inv (P.hom.left.base (inclY.base z))) z :=
      ContinuousAt.comp (f := fun z => P.hom.left.base (inclY.base z)) h1 hPc.continuousAt
    exact ContinuousAt.comp (g := (Subtype.val : strictTransform (n i) (π i) (W i) → Z i))
      (f := fun z => inv (P.hom.left.base (inclY.base z))) continuous_subtype_val.continuousAt h2
  have hQa : ContinuousAt Q a0 := hQcont a0 hx0.symm
  have hQc : ContinuousAt Q c0 := hQcont c0 (hpac.symm.trans hx0.symm)
  -- `π ∘ Q = G ∘ ι⁻¹ ∘ π'` near the two points
  have hkey : ∀ (z : geoStrictTransform (π' j) (C' j) (W' j))
      (u : EmbeddedIdealBlowupObjectGluing.localObject hW hπ i),
      inclX.base u = P.hom.left.base (inclY.base z) →
      ∀ o : O, ιf o = π' j z.val →
        π i (show strictTransform (n i) (π i) (W i) from u).val = G o := by
    intro z u hu o ho
    have hoS : o ∈ S₀ := by
      show ιf o ∈ W' j
      rw [ho]
      exact geoStrictTransform_subset_preimage (hπ' j).contMDiff.continuous (hW' j).isClosed
        z.property
    have hEo : Eo.base ⟨o, hoS⟩ = gp.base z := Subtype.ext ho
    have h1 : (J i).hom.left.base (Hm.base ⟨o, hoS⟩) =
        f.hom.left.base ((J' j).hom.left.base (gp.base z)) := by
      have h := congrArg (fun H : actualSubspaceLocallyRingedSpace (n := n' j) S₀ ⟶ X.obj.left =>
        H.base (⟨o, hoS⟩ : S₀)) hcomp
      rw [← hEo]
      exact h
    have h2 : (J i).hom.left.base ((strictTransformProjection (hπ i) (hW i).isClosed).base u) =
        f.hom.left.base ((J' j).hom.left.base (gp.base z)) := by
      rw [← hlocX i u, hu, hPb, hlocY z]
    have h3 := (hJopen i).base_open.isEmbedding.injective (h2.trans h1.symm)
    exact congrArg Subtype.val h3
  have hGev : ∀ b0 : geoStrictTransform (π' j) (C' j) (W' j),
      P.hom.left.base (inclY.base b0) = inclX.base x0 →
      ∀ᶠ z in 𝓝 b0, ∀ o : O, ιf o = π' j z.val → π i (Q z) = G o := by
    intro b0 hb0
    have hmem : P.hom.left.base (inclY.base b0) ∈ range inclX.base := ⟨x0, hb0.symm⟩
    have hopen : ∀ᶠ z in 𝓝 b0, P.hom.left.base (inclY.base z) ∈ range inclX.base :=
      hPc.continuousAt.eventually (hixe.isOpen_range.mem_nhds hmem)
    filter_upwards [hopen] with z hz o ho
    exact hkey z _ (@Function.invFun_eq _ _ ⟨x0⟩ _ _ hz) o ho
  have hGa := hGev a0 hx0.symm
  have hGc := hGev c0 (hpac.symm.trans hx0.symm)
  -- the base points lie in the centres
  have hy_nu : qg.base (inclY.base a0) ∈ nonunitLocus (nativePulledIdealModule f.hom.left B b)
      (nativePulledIdealInclusion f.hom.left B b) := by
    by_contra h
    exact ((HironakaG10ChowOneStepStrictTransform.mem_pulledUnitLocus_iff B b f _).mp h) hnu
  have hz₀C' : ιf z₀.val ∈ C' j := by
    have h := (EmbeddedIdealBlowupNonunitLocus.chart_mem_nonunitLocus
      (nativePulledIdealModule f.hom.left B b) (nativePulledIdealInclusion f.hom.left B b)
      hW' hπ' J' hJ' j (gp.base a0)).mpr (by rw [← hlocY a0]; exact hy_nu)
    exact h
  have hJz : (J i).hom.left.base (Hm.base z₀) = f.hom.left.base (qg.base (inclY.base a0)) := by
    have h := congrArg (fun H : actualSubspaceLocallyRingedSpace (n := n' j) S₀ ⟶ X.obj.left =>
      H.base z₀) hcomp
    rw [hlocY a0]
    exact h
  have hz₀C : G z₀.val ∈ C i := by
    have h := (EmbeddedIdealBlowupNonunitLocus.chart_mem_nonunitLocus B b hW hπ J hJ i
      (Hm.base z₀)).mpr (by rw [hJz]; exact hnu)
    exact h
  have hc : π' j c0.val = ιf z₀.val := (congrArg Subtype.val hw0).symm
  have hQ : Q a0 = Q c0 := by
    simp only [Q, hpac]
  have hac := HironakaG10ChowPairRelations.eq_of_pair_of_ideal_eq (hπ i) (hπ' j) (hW' j).isClosed
    hG hι hιe z₀ hz₀C' hz₀C heq Q a0 c0 rfl hc hQ hQa hQc hGa hGc
  rw [hac]

end Model

/-! ### The one-step strict transform of the global flattening algorithm -/

section Step

open HironakaG10ChowOneStepStrictTransform HironakaG10ChowFlatteningReduction
  HironakaG10ChowStrictTransformCalculus

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType]
  (hDense : Dense {x : X.obj.left |
    LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
  (f : Y ⟶ X)

/-- **Pair-injectivity of the one-step strict transform.**  The map
`(p, q) : Bl_{f*B} Y → Bl_B X × Y` is injective (route step N2). -/
theorem strict_pairInjective (a c : (strictSource B b f).obj.left)
    (hp : (strictP B b hDense f).hom.left.base a = (strictP B b hDense f).hom.left.base c)
    (hq : (strictQ B b f).hom.left.base a = (strictQ B b f).hom.left.base c) : a = c := by
  by_cases hnu : f.hom.left.base ((strictQ B b f).hom.left.base a) ∈ nonunitLocus B b
  · exact eq_of_pair_model f B b _ _ _ _ _ _ _ _ _ _ _ (strictP B b hDense f)
      (strictP_comp B b hDense f) a c hp hq hnu
  · have hmem : ∀ u, (strictQ B b f).hom.left.base u = (strictQ B b f).hom.left.base a →
        u ∈ (strictP B b hDense f).hom.left.base ⁻¹' (stepExcep B b hDense)ᶜ := by
      intro u hu
      change (stepProj B b hDense).hom.left.base ((strictP B b hDense f).hom.left.base u) ∉
        nonunitLocus B b
      rw [strictP_comp_apply B b hDense f u, hu]
      exact hnu
    exact strict_pairInjective_of_mem B b hDense f a c (hmem a rfl) (hmem c hq.symm) hq

/-- **The one-step strict transform** (all six fields of `IsStrictTransform`). -/
theorem isStrictTransform_step (hf : IsProperMap f.hom.left.base) :
    IsStrictTransform f (stepProj B b hDense) (stepExcep B b hDense) (strictP B b hDense f)
      (strictQ B b f) :=
  isStrictTransform_of_pairInjective B b hDense f hf (strict_pairInjective B b hDense f)

/-- **One blowup step with its strict transform is flattening data.** -/
theorem isFlatteningData_step (hf : IsProperMap f.hom.left.base) :
    IsFlatteningData f (stepProj B b hDense) (stepExcep B b hDense) (strictP B b hDense f)
      (strictQ B b f) :=
  isFlatteningData_of_pairInjective B b hDense f hf (strict_pairInjective B b hDense f)

end Step

section Driver

open HironakaG10ChowFlatteningDriver HironakaG10ChowFlatteningReduction
  HironakaG10ChowTowerDomination HironakaG10ChowCompactBranch HironakaG10ChowFlatBimeromorphicIso
  HironakaG10ChowStrictFlatLocus

/-- Every step of the algorithm has a pair-injective strict transform. -/
theorem stage_pairInjective (rule : ∀ s : Stage, AdmissibleCentre s.f) (s : Stage) :
    Stage.PairInjective rule s := by
  let c := rule s
  let _ := c.finiteType
  exact strict_pairInjective c.B c.b c.dense s.f

/-- **Flattening by an admissible centre rule**, with pair-injectivity discharged: for compact `X`
and proper `f`, the conclusion of `HironakaFlattening` for `f` follows from closed non-flat images and
the absence of an infinite compatible branch of non-flat points. -/
theorem exists_flattening_of_rule' (rule : ∀ s : Stage, AdmissibleCentre s.f) (s₀ : Stage)
    (hX : CompactSpace s₀.X.obj.left)
    (hf : IsProperMap s₀.f.hom.left.base)
    (hclosed : ∀ n, IsClosed (nonflatImage (stage rule s₀ n).f))
    (hno : ∀ s : ∀ n, (stage rule s₀ n).X.obj.left,
      ¬ IsBranch (fun n => (Stage.σ rule (stage rule s₀ n)).hom.left.base)
        (fun n => nonflatImage (stage rule s₀ n).f) s) :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ s₀.X) (E : Set X'.obj.left),
      IsNativeBlowupTower s₀.X X' σ ∧ IsClosed E ∧ interior E = ∅ ∧ IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ s₀.Y),
        IsStrictTransform s₀.f σ E p q ∧ IsFlatMorphism p :=
  exists_flattening_of_rule rule s₀ hX hf (fun _ => stage_pairInjective rule _) hclosed hno

end Driver

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowPairInjective
