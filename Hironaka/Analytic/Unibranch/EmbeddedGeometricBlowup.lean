import Hironaka.Analytic.Unibranch.Resolution
import Hironaka.Resolution.HironakaSingularSubspaceBlowupLift
import Hironaka.Analytic.ClosureDifferenceAnalytic

/-!
# Actual ORIGINAL geometric blowup source and full projection, with NO hd

The source is literally closure(pi⁻¹(W minus C)), including codimension-one
and whole-zero carrier components. The entire original centre ideal remains
unchanged. Generic analytic/subspace/properness mothers are reused0credit.
Blueprint FIRST: `embedded-geometric-blowup.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowup

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  BlowupStrictSubmanifold HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaSingularSubspaceBlowupLift HironakaResolutionSpaceComplex
  SourceReducedComplexSpace

noncomputable section

private theorem ideal_stalk_comp {A B D : LocallyRingedSpace} (f : A ⟶ B) (g : B ⟶ D)
    (x : A) (I : Ideal (D.presheaf.stalk (g.base (f.base x))).carrier) :
    Ideal.map ((f ≫ g).stalkMap x).hom I =
      Ideal.map (f.stalkMap x).hom (Ideal.map (g.stalkMap (f.base x)).hom I) := by
  rw [LocallyRingedSpace.stalkMap_comp,Ideal.map_map]
  rfl

variable {n : ℕ} {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) M] [hMC : IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [hYC : IsComplexManifold n Y]
  {C W : Set M} {π : Y → M}

private theorem geometric_analytic (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) :
    IsComplexAnalyticSubset (n := n) (geoStrictTransform π C W) := by
  have hC := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
  simpa only [geoStrictTransform,preimage_sdiff] using
    ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff hW)
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff hC)

/-- The SAME geometric carrier with its actual quotient sheaf is an
EXISTING original reduced complex space, without any target-density input. -/
def geometricSource (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) : SourceReducedComplexSpace :=
  ofClosedAnalytic (geoStrictTransform π C W) (geometric_analytic hπ hW)

/-- The SAME ambient pi induces the ENTIRE actual quotient-sheaf projection. -/
def geometricProjection (hπ : IsBlowupAlong n C π) (hW : IsClosed W) :
    actualSubspaceLocallyRingedSpace (n := n) (geoStrictTransform π C W) ⟶
      actualSubspaceLocallyRingedSpace (n := n) W :=
  actualSubspaceMap hπ.contMDiff (fun _ hy =>
    geoStrictTransform_subset_preimage hπ.contMDiff.continuous hW hy)

/-- The exact full scalar triangle of the SAME raw projection. -/
theorem geometricProjection_point (hπ : IsBlowupAlong n C π) (hW : IsClosed W) :
    geometricProjection hπ hW ≫ subspacePointMap (n := n) W =
      subspacePointMap (n := n) (geoStrictTransform π C W) := actualSubspaceMap_point _ _

/-- The actual underlying point map remains literally the original pi. -/
theorem geometricProjection_base_val (hπ : IsBlowupAlong n C π) (hW : IsClosed W)
    (y : geoStrictTransform π C W) : ((geometricProjection hπ hW).base y).val = π y.val := rfl

/-- The full original morphism retains the SAME raw p and scalar map. -/
def geometricProjectionMorphism (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) : geometricSource hπ hW ⟶ ofClosedAnalytic W hW :=
  ObjectProperty.homMk (Over.homMk (geometricProjection hπ hW.isClosed)
    (geometricProjection_point hπ hW.isClosed))

/-- Exact underlying FULL LRS morphism, not just its original point map. -/
theorem geometricProjectionMorphism_left (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) :
    (geometricProjectionMorphism hπ hW).hom.left = geometricProjection hπ hW.isClosed := rfl

/-- The WHOLE ambient inclusion square for the SAME actual projection. -/
theorem geometricProjection_inclusion (hπ : IsBlowupAlong n C π) (hW : IsClosed W) :
    actualSubspaceInclusion (n := n) (geoStrictTransform π C W) ≫
        ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff =
      geometricProjection hπ hW ≫ actualSubspaceInclusion (n := n) W :=
  actualSubspaceMap_inclusion hπ.contMDiff _

/-- The literal ENTIRE original ambient centre ideal maps through the SAME
full projection/inclusion composite, with no radical or ideal certificate. -/
theorem geometricProjection_wholeCentreIdeal (hπ : IsBlowupAlong n C π) (hW : IsClosed W)
    (y : geoStrictTransform π C W) :
    Ideal.map ((geometricProjection hπ hW ≫ actualSubspaceInclusion (n := n) W).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (π y.val)) =
    Ideal.map ((geometricProjection hπ hW).stalkMap y).hom
      (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap
        ((geometricProjection hπ hW).base y)).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (π y.val))) :=
  ideal_stalk_comp _ _ _ _

/-- Properness of the SAME geometric projection; no surjectivity is assumed. -/
theorem geometricProjection_isProperMap (hπ : IsBlowupAlong n C π) (hW : IsClosed W) :
    IsProperMap (geometricProjection hπ hW).base := by
  change IsProperMap (fun y : geoStrictTransform π C W => (⟨π y.val, _⟩ : W))
  refine isProperMap_of_comp_of_t2 (g := (Subtype.val : W → M))
    ((hπ.contMDiff.continuous.comp continuous_subtype_val).subtype_mk _)
    continuous_subtype_val ?_
  exact (HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ).comp
    isClosed_closure.isClosedEmbedding_subtypeVal.isProperMap

/-- Closure-defined geometric source good points are ALWAYS dense, even
when the original target has entire components inside the centre. -/
theorem geometricProjection_dense_compl_centre (hπ : IsBlowupAlong n C π) (hW : IsClosed W) :
    Dense ((geometricProjection hπ hW).base ⁻¹' {x : W | x.val ∉ C}) := by
  rw [dense_iff_closure_eq,eq_univ_iff_forall]
  intro y
  rw [closure_subtype]
  have hy : y.val ∈ closure (π ⁻¹' (W \ C)) := y.property
  refine closure_mono ?_ hy
  intro z hz
  exact ⟨⟨z,subset_closure hz⟩,hz.2,rfl⟩

/-- The actual centre-complement biholomorphism restricts to the SAME
geometric quotient subspaces, including the complete structure sheaves. -/
def geometricOffCentreIso (hπ : IsBlowupAlong n C π) (hW : IsClosed W) :
    actualSubspaceLocallyRingedSpace (n := n)
      ((Subtype.val : centreComplementPreimage hπ → Y) ⁻¹' geoStrictTransform π C W) ≅
    actualSubspaceLocallyRingedSpace (n := n)
      ((Subtype.val : centreComplement hπ → M) ⁻¹' W) :=
  actualSubspaceBiholomorphicIso (offCentreBiholomorphism hπ) _ _
    (fun y => mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hW y.property)

/-- Exact WHOLE off-centre LRS square with the SAME raw projection. -/
theorem geometricOffCentreIso_comm (hπ : IsBlowupAlong n C π) (hW : IsClosed W) :
    actualOpenSubspaceMap (n := n) (geoStrictTransform π C W) (centreComplementPreimage hπ) ≫
        geometricProjection hπ hW =
      (geometricOffCentreIso hπ hW).hom ≫ actualOpenSubspaceMap (n := n) W (centreComplement hπ) := by
  unfold actualOpenSubspaceMap geometricProjection geometricOffCentreIso actualSubspaceBiholomorphicIso
  dsimp only
  rw [← actualSubspaceMap_comp,← actualSubspaceMap_comp]
  rfl

/-- The ORIGINAL complement-isomorphism predicate is derived from actual
native OIs and the full square, without any target-density input. -/
theorem geometricProjectionMorphism_isIsoOver_compl_centre (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) :
    IsIsoOver (geometricProjectionMorphism hπ hW) (((Subtype.val : W → M) ⁻¹' C)ᶜ) := by
  refine ⟨_,actualOpenSubspaceMap (n := n) (geoStrictTransform π C W)
    (centreComplementPreimage hπ),
    actualOpenSubspaceMap_isOpenImmersion (n := n) (geoStrictTransform π C W) (centreComplementPreimage hπ),?_,?_,?_⟩
  · change range (actualOpenSubspaceMap (n := n) (geoStrictTransform π C W)
        (centreComplementPreimage hπ)).base =
      (geometricProjection hπ hW.isClosed).base ⁻¹' (((Subtype.val : W → M) ⁻¹' C)ᶜ)
    rw [range_actualOpenSubspaceMap]
    rfl
  · change LocallyRingedSpace.IsOpenImmersion
      (actualOpenSubspaceMap (n := n) (geoStrictTransform π C W) (centreComplementPreimage hπ) ≫
        geometricProjection hπ hW.isClosed)
    rw [geometricOffCentreIso_comm hπ hW.isClosed]
    infer_instance
  · change range (actualOpenSubspaceMap (n := n) (geoStrictTransform π C W)
        (centreComplementPreimage hπ) ≫ geometricProjection hπ hW.isClosed).base = _
    rw [geometricOffCentreIso_comm hπ hW.isClosed,range_iso_hom_comp_base,range_actualOpenSubspaceMap]
    rfl

/-- Exact support image: closure of W minus C, without a surjectivity assertion onto W. -/
theorem image_geometricSource (hπ : IsBlowupAlong n C π) :
    π '' geoStrictTransform π C W = closure (W \ C) := by
  have hi : π '' (π ⁻¹' (W \ C)) = W \ C := by
    apply Subset.antisymm
    · rintro _ ⟨y,hy,rfl⟩
      exact hy
    · rintro x ⟨hxW,hxC⟩
      have hiso := BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ
      obtain ⟨y,_hy,hyx⟩ := hiso.1.surjOn hxC
      refine ⟨y,?_,hyx⟩
      change π y ∈ W \ C
      rw [hyx]
      exact ⟨hxW,hxC⟩
  unfold geoStrictTransform
  rw [← (HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ).isClosedMap.closure_image_eq_of_continuous
    hπ.contMDiff.continuous (π ⁻¹' (W \ C)),hi]

/-- Entire zero carrier components yield the ACTUAL empty original source,
including codimension-one identity ambient blowups. -/
theorem geometricSource_isEmpty_of_subset_centre (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) (hWC : W ⊆ C) :
    IsEmpty (geometricSource hπ hW).obj.left := by
  change IsEmpty (geoStrictTransform π C W)
  refine ⟨fun y => ?_⟩
  have hy : y.val ∈ closure (π ⁻¹' (W \ C)) := y.property
  rw [sdiff_eq_empty.mpr hWC,preimage_empty,closure_empty] at hy
  exact hy

/-- Elementary actual carrier facts for the auxiliary closure, not a
changed original target or incoming target-density certificate. -/
theorem prunedCarrier_facts {T : Type} [TopologicalSpace T] {A D : Set T} (hA : IsClosed A) :
    closure (A \ D) ⊆ A ∧ closure (A \ D) \ D = A \ D ∧
      closure (A \ D) ⊆ closure (closure (A \ D) \ D) := by
  have hs : closure (A \ D) ⊆ A := closure_minimal sdiff_subset hA
  have he : closure (A \ D) \ D = A \ D := by
    apply Subset.antisymm
    · exact fun x hx => ⟨hs hx.1,hx.2⟩
    · exact fun x hx => ⟨subset_closure hx,hx.2⟩
  refine ⟨hs,he,?_⟩
  rw [he]

/-- The actual geometric source equals the EXISTING dense-engine source
for DERIVED W0=closure(W minus C); the actual projection still targets W. -/
theorem geometricTransform_eq_pruned_strictTransform (hπ : IsBlowupAlong n C π) (hW : IsClosed W) :
    geoStrictTransform π C W = strictTransform n π (closure (W \ C)) := by
  obtain ⟨_hs,he,hd⟩ := prunedCarrier_facts (D := C) hW
  calc
    _ = geoStrictTransform π C (closure (W \ C)) := by simp only [geoStrictTransform,he]
    _ = _ := BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hd

end
end Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowup
