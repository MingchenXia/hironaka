import Hironaka.Analytic.Unibranch.EmbeddedBlowup
import Hironaka.Resolution.HironakaIntrinsicMorphismGluingAnalytic
import Hironaka.Blowup.BlowupBiholomorphismLift
import Hironaka.Resolution.HironakaBaseChange

/-!
# ORIGINAL open restriction of the SAME literal embedded blowup

The objects are actual LRS restrictions on the original open point sets. Their
original complex-space property and all full comparison maps are derived.
No desired comparison, isomorphism witness or substitute source category is input.
Blueprint: `embedded-blowup-open-restriction.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedBlowupOpenRestriction

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualAnalyticSubspaceLocalFunctions
  HironakaReducedComplexAnalyticSpaces HironakaResolutionSpaceComplex
  HironakaIntrinsicMorphismGluingAnalytic HironakaSingularSubspaceBlowupLift
  SourceReducedComplexSpace EmbeddedBlowup

noncomputable section

private def sameRangeIso {X Y Z : LocallyRingedSpace} (f : X ⟶ Z) (g : Y ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (h : range f.base = range g.base) : X ≅ Y where
  hom := LocallyRingedSpace.IsOpenImmersion.lift g f h.subset
  inv := LocallyRingedSpace.IsOpenImmersion.lift f g h.symm.subset
  hom_inv_id := by
    apply (cancel_mono f).mp
    rw [Category.assoc, LocallyRingedSpace.IsOpenImmersion.lift_fac,
      LocallyRingedSpace.IsOpenImmersion.lift_fac, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono g).mp
    rw [Category.assoc, LocallyRingedSpace.IsOpenImmersion.lift_fac,
      LocallyRingedSpace.IsOpenImmersion.lift_fac, Category.id_comp]

private theorem sameRangeIso_fac {X Y Z : LocallyRingedSpace}
    (f : X ⟶ Z) (g : Y ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (h : range f.base = range g.base) : (sameRangeIso f g h).hom ≫ g = f :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac g f h.subset

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Every ORIGINAL relatively open set is the trace of an internally produced
ambient open set. -/
theorem exists_ambient_open (W : Set M) (V : Opens W) :
    ∃ O : Opens M, (Subtype.val : W → M) ⁻¹' (O : Set M) = (V : Set W) := by
  obtain ⟨O, hO, hOV⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp V.isOpen
  exact ⟨⟨O, hO⟩, hOV⟩

/-- The SAME literal LRS restriction is an object of the ORIGINAL category.
Its full local-model property is derived, not supplied. -/
@[implicit_reducible]
def restrictedClosedAnalytic {W : Set M} (hW : IsComplexAnalyticSubset (n := n) W)
    (V : Opens W) : SourceReducedComplexSpace := by
  let X := actualSubspaceLocallyRingedSpace (n := n) W
  let j := X.ofRestrict (Opens.isOpenEmbedding V)
  have hX : hasAnalyticCharts (Over.mk (subspacePointMap (n := n) W)) := by
    refine ⟨?_, ?_, fun x => ⟨n, exists_model_chart hW x⟩⟩
    · change T2Space W
      infer_instance
    · change SecondCountableTopology W
      infer_instance
  have hV := hasAnalyticCharts_of_openImmersion _ _ hX j rfl
  refine ⟨Over.mk (j ≫ subspacePointMap (n := n) W), hV.1, ?_, hV.2.2⟩
  change ParacompactSpace V
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel n) M
  let : LocallyCompactSpace W := hW.isClosed.locallyCompactSpace
  let : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  infer_instance

/-- The original restriction inclusion retains its entire native sheaf map. -/
def restrictionInclusion {W : Set M} (hW : IsComplexAnalyticSubset (n := n) W)
    (V : Opens W) : restrictedClosedAnalytic hW V ⟶ ofClosedAnalytic W hW := by
  apply ObjectProperty.homMk
  refine Over.homMk ?_ ?_
  · change (actualSubspaceLocallyRingedSpace (n := n) W).restrict
      (Opens.isOpenEmbedding V) ⟶ actualSubspaceLocallyRingedSpace (n := n) W
    exact (actualSubspaceLocallyRingedSpace (n := n) W).ofRestrict (Opens.isOpenEmbedding V)
  · rfl

instance restrictionInclusion_isOpenImmersion {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) (V : Opens W) :
    LocallyRingedSpace.IsOpenImmersion (restrictionInclusion hW V).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion
    ((actualSubspaceLocallyRingedSpace (n := n) W).ofRestrict (Opens.isOpenEmbedding V))
  infer_instance

private theorem restrictionInclusion_range {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) (V : Opens W) :
    range (restrictionInclusion hW V).hom.left.base = (V : Set W) := by
  change range (Subtype.val : V → W) = _
  exact Subtype.range_coe

/-- The original ambient open inclusion of the SAME quotient model. -/
def ambientOpenInclusion {W : Set M} (hW : IsComplexAnalyticSubset (n := n) W)
    (O : Opens M) :
    ofClosedAnalytic ((Subtype.val : O → M) ⁻¹' W)
        (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O) ⟶
      ofClosedAnalytic W hW :=
  ObjectProperty.homMk (Over.homMk (actualOpenSubspaceMap (n := n) W O)
    (actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)))

/-- An internally constructed ORIGINAL iso from the concrete quotient-open
model to the literal original restriction on V. -/
def openRestrictionIso {W : Set M} (hW : IsComplexAnalyticSubset (n := n) W)
    (V : Opens W) (O : Opens M)
    (hOV : (Subtype.val : W → M) ⁻¹' (O : Set M) = (V : Set W)) :
    ofClosedAnalytic ((Subtype.val : O → M) ⁻¹' W)
        (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O) ≅
      restrictedClosedAnalytic hW V := by
  let f := actualOpenSubspaceMap (n := n) W O
  let g := (restrictionInclusion hW V).hom.left
  let : LocallyRingedSpace.IsOpenImmersion g := restrictionInclusion_isOpenImmersion hW V
  have hr : range f.base = range g.base := by
    rw [restrictionInclusion_range, range_actualOpenSubspaceMap]
    exact hOV
  let E := sameRangeIso f g hr
  refine ObjectProperty.isoMk sourceReducedComplexSpaceProperty (Over.isoMk E ?_)
  change E.hom ≫ (g ≫ subspacePointMap (n := n) W) = _
  rw [← Category.assoc, sameRangeIso_fac]
  exact actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)

/-- The full original restriction inclusion square is exact. -/
theorem openRestrictionIso_inclusion {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) (V : Opens W) (O : Opens M)
    (hOV : (Subtype.val : W → M) ⁻¹' (O : Set M) = (V : Set W)) :
    (openRestrictionIso hW V O hOV).hom ≫ restrictionInclusion hW V =
      ambientOpenInclusion hW O := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact sameRangeIso_fac (actualOpenSubspaceMap (n := n) W O)
    (restrictionInclusion hW V).hom.left
    ((range_actualOpenSubspaceMap (n := n) W O).trans
      (hOV.trans (restrictionInclusion_range hW V).symm))

variable {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C W : Set M} {π : Y → M}

/-- The original open preimage uses the SAME original projection point map. -/
def projectionOpen (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) (V : Opens W) :
    Opens (strictTransform n π W) :=
  ⟨(strictTransformProjection hπ hW.isClosed).base ⁻¹' (V : Set W),
    V.isOpen.preimage (strictTransformProjection hπ hW.isClosed).base.hom.continuous⟩

/-- The full original projection between the literal original restrictions. -/
def restrictionProjection (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) (V : Opens W) :
    restrictedClosedAnalytic
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
          hπ hW) (projectionOpen hπ hW V) ⟶ restrictedClosedAnalytic hW V := by
  let hS := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
    hπ hW
  let j := (restrictionInclusion hW V).hom.left
  let k := (restrictionInclusion hS (projectionOpen hπ hW V)).hom.left
  let p := strictTransformProjection hπ hW.isClosed
  have hr : range (k ≫ p).base ⊆ range j.base := by
    rw [restrictionInclusion_range]
    rintro _ ⟨x, rfl⟩
    exact x.property
  let L := LocallyRingedSpace.IsOpenImmersion.lift j (k ≫ p) hr
  have hL : L ≫ j = k ≫ p := LocallyRingedSpace.IsOpenImmersion.lift_fac j (k ≫ p) hr
  apply ObjectProperty.homMk
  refine Over.homMk L ?_
  change L ≫ (j ≫ subspacePointMap (n := n) W) =
    k ≫ subspacePointMap (n := n) (strictTransform n π W)
  rw [← Category.assoc, hL, Category.assoc, strictTransformProjection_point]

/-- The restricted projection retains the full original inclusion square. -/
theorem restrictionProjection_inclusion (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) (V : Opens W) :
    restrictionProjection hπ hW V ≫ restrictionInclusion hW V =
      restrictionInclusion
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            hπ hW) (projectionOpen hπ hW V) ≫ strictTransformMorphism hπ hW := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac
    (restrictionInclusion hW V).hom.left
    ((restrictionInclusion
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
        hπ hW) (projectionOpen hπ hW V)).hom.left ≫ strictTransformProjection hπ hW.isClosed)
    (by
      rw [restrictionInclusion_range]
      rintro _ ⟨x, rfl⟩
      exact x.property)

/-- The whole literal strict transform commutes with SAME ambient open
restriction; no comparison or set-equality certificate is input. -/
theorem strictTransform_open_eq (hπ : IsBlowupAlong n C π) (O : Opens M) :
    strictTransform n (BlowupBiholomorphismLift.restrictMap hπ O)
        ((Subtype.val : O → M) ⁻¹' W) =
      (Subtype.val : BlowupBiholomorphismLift.preOpen hπ O → Y) ⁻¹' strictTransform n π W :=
  HironakaBaseChange.strictTransform_preimage_eq hπ.contMDiff
    (BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ O).contMDiff
    (HironakaBaseChange.isOpenHoloEmbedding_val O)
    (HironakaBaseChange.isOpenHoloEmbedding_val (BlowupBiholomorphismLift.preOpen hπ O))
    (fun _ => rfl) W

private def strictTransformTraceIso (hπ : IsBlowupAlong n C π) (O : Opens M) :
    actualSubspaceLocallyRingedSpace (n := n)
        (strictTransform n (BlowupBiholomorphismLift.restrictMap hπ O)
          ((Subtype.val : O → M) ⁻¹' W)) ≅
      actualSubspaceLocallyRingedSpace (n := n)
        ((Subtype.val : BlowupBiholomorphismLift.preOpen hπ O → Y) ⁻¹' strictTransform n π W) :=
  actualSubspaceBiholomorphicIso
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (BlowupBiholomorphismLift.preOpen hπ O) ∞) _ _
    (fun z => by rw [strictTransform_open_eq hπ O]; rfl)

/-- The actual source-open inclusion from the SAME literal strict transform
of the genuinely restricted ambient blowup, in the ORIGINAL category. -/
def strictTransformOpenInclusion (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) (O : Opens M) :
    ofClosedAnalytic
        (strictTransform n (BlowupBiholomorphismLift.restrictMap hπ O)
          ((Subtype.val : O → M) ⁻¹' W))
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
          (BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ O)
          (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O)) ⟶
      ofClosedAnalytic (strictTransform n π W)
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
          hπ hW) := by
  let E := strictTransformTraceIso (W := W) hπ O
  let J := actualOpenSubspaceMap (n := n) (strictTransform n π W)
    (BlowupBiholomorphismLift.preOpen hπ O)
  apply ObjectProperty.homMk
  refine Over.homMk (E.hom ≫ J) ?_
  change (E.hom ≫ J) ≫ subspacePointMap (n := n) (strictTransform n π W) =
    subspacePointMap (n := n)
      (strictTransform n (BlowupBiholomorphismLift.restrictMap hπ O)
        ((Subtype.val : O → M) ⁻¹' W))
  have hpJ : J ≫ subspacePointMap (n := n) (strictTransform n π W) =
      subspacePointMap (n := n)
        ((Subtype.val : BlowupBiholomorphismLift.preOpen hπ O → Y) ⁻¹'
          strictTransform n π W) :=
    actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)
  rw [Category.assoc, hpJ]
  exact actualSubspaceMap_point _ _

instance strictTransformOpenInclusion_isOpenImmersion (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) (O : Opens M) :
    LocallyRingedSpace.IsOpenImmersion (strictTransformOpenInclusion hπ hW O).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion ((strictTransformTraceIso (W := W) hπ O).hom ≫
    actualOpenSubspaceMap (n := n) (strictTransform n π W)
      (BlowupBiholomorphismLift.preOpen hπ O))
  infer_instance

private theorem strictTransformOpenInclusion_range (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) (V : Opens W) (O : Opens M)
    (hOV : (Subtype.val : W → M) ⁻¹' (O : Set M) = (V : Set W)) :
    range (strictTransformOpenInclusion hπ hW O).hom.left.base =
      (projectionOpen hπ hW V : Set (strictTransform n π W)) := by
  change range ((strictTransformTraceIso (W := W) hπ O).hom ≫
    actualOpenSubspaceMap (n := n) (strictTransform n π W)
      (BlowupBiholomorphismLift.preOpen hπ O)).base = _
  rw [range_iso_hom_comp_base, range_actualOpenSubspaceMap]
  ext z
  change π z.val ∈ O ↔ (strictTransformProjection hπ hW.isClosed).base z ∈ V
  exact Set.ext_iff.mp hOV ((strictTransformProjection hπ hW.isClosed).base z)

/-- The actual open inclusion and SAME original projections commute as FULL
original morphisms, not only at points. -/
theorem strictTransformOpenInclusion_projection (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) (O : Opens M) :
    strictTransformOpenInclusion hπ hW O ≫ strictTransformMorphism hπ hW =
      strictTransformMorphism (BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ O)
          (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O) ≫
        ambientOpenInclusion hW O := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply actualSubspaceMap_eq_of_base_eq _ _
    (Over.w (strictTransformOpenInclusion hπ hW O ≫ strictTransformMorphism hπ hW).hom)
    (Over.w (strictTransformMorphism (BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ O)
      (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O) ≫ ambientOpenInclusion hW O).hom)
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The derived actual source open immersion gives a canonical ORIGINAL iso
onto the literal original p-preimage(V), internally and with full sheaf maps. -/
def strictTransformRestrictionIso (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) (V : Opens W) (O : Opens M)
    (hOV : (Subtype.val : W → M) ⁻¹' (O : Set M) = (V : Set W)) :
    ofClosedAnalytic
        (strictTransform n (BlowupBiholomorphismLift.restrictMap hπ O)
          ((Subtype.val : O → M) ⁻¹' W))
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
          (BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ O)
          (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O)) ≅
      restrictedClosedAnalytic
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
          hπ hW) (projectionOpen hπ hW V) := by
  let f := (strictTransformOpenInclusion hπ hW O).hom.left
  let g := (restrictionInclusion
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
      hπ hW) (projectionOpen hπ hW V)).hom.left
  have hr : range f.base = range g.base := by
    rw [restrictionInclusion_range]
    exact strictTransformOpenInclusion_range hπ hW V O hOV
  let E := sameRangeIso f g hr
  refine ObjectProperty.isoMk sourceReducedComplexSpaceProperty (Over.isoMk E ?_)
  change E.hom ≫ (g ≫ subspacePointMap (n := n) (strictTransform n π W)) = _
  rw [← Category.assoc, sameRangeIso_fac]
  exact Over.w (strictTransformOpenInclusion hπ hW O).hom

/-- The source iso followed by the literal original restriction inclusion
is exactly the actual holomorphic strict-transform inclusion. -/
theorem strictTransformRestrictionIso_inclusion (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) (V : Opens W) (O : Opens M)
    (hOV : (Subtype.val : W → M) ⁻¹' (O : Set M) = (V : Set W)) :
    (strictTransformRestrictionIso hπ hW V O hOV).hom ≫
        restrictionInclusion
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            hπ hW) (projectionOpen hπ hW V) = strictTransformOpenInclusion hπ hW O := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact sameRangeIso_fac (strictTransformOpenInclusion hπ hW O).hom.left
    (restrictionInclusion
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
        hπ hW) (projectionOpen hπ hW V)).hom.left (by
      rw [restrictionInclusion_range]
      exact strictTransformOpenInclusion_range hπ hW V O hOV)

/-- The comparison of literal source restrictions gives the entire ORIGINAL
projection square over the internally identified original base restriction. -/
theorem strictTransformRestrictionIso_projection (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) (V : Opens W) (O : Opens M)
    (hOV : (Subtype.val : W → M) ⁻¹' (O : Set M) = (V : Set W)) :
    (strictTransformRestrictionIso hπ hW V O hOV).hom ≫ restrictionProjection hπ hW V =
      strictTransformMorphism (BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ O)
          (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O) ≫
        (openRestrictionIso hW V O hOV).hom := by
  let E := strictTransformRestrictionIso hπ hW V O hOV
  let B := openRestrictionIso hW V O hOV
  let q := restrictionProjection hπ hW V
  let pO := strictTransformMorphism (BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ O)
    (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O)
  let i := restrictionInclusion hW V
  have hq := restrictionProjection_inclusion hπ hW V
  have hE := strictTransformRestrictionIso_inclusion hπ hW V O hOV
  have hB := openRestrictionIso_inclusion hW V O hOV
  have hj := strictTransformOpenInclusion_projection hπ hW O
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono i.hom.left).mp
  calc
    _ = E.hom.hom.left ≫ (q.hom.left ≫ i.hom.left) := Category.assoc _ _ _
    _ = E.hom.hom.left ≫
        ((restrictionInclusion
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            hπ hW) (projectionOpen hπ hW V)).hom.left ≫
          (strictTransformMorphism hπ hW).hom.left) :=
      congrArg (fun t => E.hom.hom.left ≫ t) (congrArg (fun H => H.hom.left) hq)
    _ = ((E.hom ≫ restrictionInclusion
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            hπ hW) (projectionOpen hπ hW V)).hom.left) ≫
          (strictTransformMorphism hπ hW).hom.left := (Category.assoc _ _ _).symm
    _ = (strictTransformOpenInclusion hπ hW O).hom.left ≫
          (strictTransformMorphism hπ hW).hom.left :=
      congrArg (fun t => t.hom.left ≫ (strictTransformMorphism hπ hW).hom.left) hE
    _ = pO.hom.left ≫ (ambientOpenInclusion hW O).hom.left :=
      congrArg (fun H => H.hom.left) hj
    _ = pO.hom.left ≫ (B.hom.hom.left ≫ i.hom.left) :=
      congrArg (fun t => pO.hom.left ≫ t.hom.left) hB.symm
    _ = _ := (Category.assoc _ _ _).symm

/-- Every genuine original base open has an internally produced ambient
representative and a unique ORIGINAL source-restriction comparison, including
the full projection square. No comparison/iso witness is supplied. -/
theorem exists_open_restriction_comparison (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) (V : Opens W) :
    ∃ (O : Opens M) (hOV : (Subtype.val : W → M) ⁻¹' (O : Set M) = (V : Set W)),
      ∃! E : ofClosedAnalytic
          (strictTransform n (BlowupBiholomorphismLift.restrictMap hπ O)
            ((Subtype.val : O → M) ⁻¹' W))
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            (BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ O)
            (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O)) ≅
        restrictedClosedAnalytic
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            hπ hW) (projectionOpen hπ hW V),
        E.hom ≫ restrictionInclusion
            (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
              hπ hW) (projectionOpen hπ hW V) = strictTransformOpenInclusion hπ hW O ∧
          E.hom ≫ restrictionProjection hπ hW V =
            strictTransformMorphism (BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ O)
                (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O) ≫
              (openRestrictionIso hW V O hOV).hom := by
  obtain ⟨O, hOV⟩ := exists_ambient_open W V
  refine ⟨O, hOV, strictTransformRestrictionIso hπ hW V O hOV,
    ⟨strictTransformRestrictionIso_inclusion hπ hW V O hOV,
      strictTransformRestrictionIso_projection hπ hW V O hOV⟩, ?_⟩
  intro E hE
  apply Iso.ext
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (restrictionInclusion
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
      hπ hW) (projectionOpen hπ hW V)).hom.left).mp
  exact congrArg (fun H => H.hom.left)
    (hE.1.trans (strictTransformRestrictionIso_inclusion hπ hW V O hOV).symm)

end

end Hironaka.Analytic.Unibranch.EmbeddedBlowupOpenRestriction
