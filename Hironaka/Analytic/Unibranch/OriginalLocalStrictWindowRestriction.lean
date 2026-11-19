import Hironaka.Analytic.Unibranch.OriginalLocalCanonicalResolutionCover

/-!
# Full native projection squares for literal restrictions of the same history

The literal restricted tower, entire strict carrier, actual quotient models,
full native morphisms and original-Reg trace are derived from the chosen
actual window. No comparison of independently chosen histories is assumed.

Blueprint FIRST: `original-local-strict-window-restriction.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalLocalStrictWindowRestriction

noncomputable section

open Hironaka Hironaka.BlowupSequences
  Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaResolutionSpace
  HironakaResolutionSpaceComplex HironakaEmbeddedAnalytic HironakaBaseChange
  SourceReducedComplexSpace BlowupTowers BlowupTowerTransforms
  OriginalLocalCanonicalStrictResolution

variable {X : SourceReducedComplexSpace} (e : LocalEmbedding X) (U : Opens e.ambient)
  {D : CMfd.{0} e.dim} (T : BlowupTower (CMfd.of (n := e.dim) U) D)
  {Ef : List (Set D)}
  (h : IsStrictTransformResolution e.dim (windowCarrier e U) T.proj Ef)

/-- The actual strict carrier of the literal restricted tower. -/
abbrev restrictedStrictCarrier (P : Opens U) : Set (openPreimage T P) :=
  strictTransform e.dim (restrict P T).proj
    ((Subtype.val : P → U) ⁻¹' windowCarrier e U)

/-- Held strict-transform open base change identifies the ENTIRE actual
restricted strict carrier, with no equality supplied by a caller. -/
theorem restrictedStrictCarrier_eq (P : Opens U) :
    restrictedStrictCarrier e U T P =
      (Subtype.val : openPreimage T P → D) ⁻¹' strictTransform e.dim T.proj (windowCarrier e U) :=
  strictTransform_preimage_eq T.contMDiff_proj (restrict P T).contMDiff_proj
    (isOpenHoloEmbedding_val P) (isOpenHoloEmbedding_val (openPreimage T P))
    (fun y => (proj_restrict P T y).symm) (windowCarrier e U)

include h in
theorem restrictedStrictCarrier_isClosedSubmanifold (P : Opens U) :
    IsClosedSubmanifold e.dim (restrictedStrictCarrier e U T P) := by
  rw [restrictedStrictCarrier_eq]
  refine ⟨h.isClosedSubmanifold.1.preimage continuous_subtype_val, ?_⟩
  intro y hy
  obtain ⟨d, hd⟩ := h.isClosedSubmanifold.2 y.val hy
  exact ⟨d, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hd⟩

/-- The independently formed native reduced base model on P. -/
def baseSpace (P : Opens U) : SourceReducedComplexSpace :=
  ofClosedAnalytic ((Subtype.val : P → U) ⁻¹' windowCarrier e U)
    (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val (windowCarrier_analytic e U) P)

/-- The original native strict model of the chosen actual tower. -/
abbrev originalStrictSpace : SourceReducedComplexSpace :=
  ofClosedAnalytic (strictTransform e.dim T.proj (windowCarrier e U))
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold h.isClosedSubmanifold)

/-- The independently formed actual strict quotient model of restricted T. -/
def strictSpace (P : Opens U) : SourceReducedComplexSpace :=
  ofClosedAnalytic (restrictedStrictCarrier e U T P)
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (restrictedStrictCarrier_isClosedSubmanifold e U T h P))

/-- The genuine full native base open inclusion. -/
def baseInclusion (P : Opens U) : baseSpace e U P ⟶ windowSpace e U :=
  ObjectProperty.homMk (Over.homMk
    (actualOpenSubspaceMap (n := e.dim) (windowCarrier e U) P)
    (actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)))

theorem baseInclusion_isOpenImmersion (P : Opens U) :
    LocallyRingedSpace.IsOpenImmersion (baseInclusion e U P).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion
    (actualOpenSubspaceMap (n := e.dim) (windowCarrier e U) P)
  infer_instance

theorem baseInclusion_range (P : Opens U) :
    range (baseInclusion e U P).hom.left.base =
      {v : windowCarrier e U | v.val ∈ P} :=
  range_actualOpenSubspaceMap (windowCarrier e U) P

/-- The full native endpoint inclusion uses the derived whole strict trace. -/
def strictInclusion (P : Opens U) : strictSpace e U T h P ⟶ originalStrictSpace e U T h :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap contMDiff_subtype_val
      (fun y hy => (Set.ext_iff.mp (restrictedStrictCarrier_eq e U T P) y).mp hy))
    (actualSubspaceMap_point contMDiff_subtype_val _))

theorem strictInclusion_isOpenImmersion (P : Opens U) :
    LocallyRingedSpace.IsOpenImmersion (strictInclusion e U T h P).hom.left := by
  let E := actualSubspaceBiholomorphicIso
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel e.dim) (openPreimage T P) ∞)
    (restrictedStrictCarrier e U T P)
    ((Subtype.val : openPreimage T P → D) ⁻¹' strictTransform e.dim T.proj (windowCarrier e U))
    (fun y => Set.ext_iff.mp (restrictedStrictCarrier_eq e U T P) y)
  have heq : (strictInclusion e U T h P).hom.left = E.hom ≫
      actualOpenSubspaceMap (n := e.dim) (strictTransform e.dim T.proj (windowCarrier e U))
        (openPreimage T P) := by
    change actualSubspaceMap _ _ = E.hom ≫ _
    dsimp only [E, actualSubspaceBiholomorphicIso, actualOpenSubspaceMap]
    rw [← actualSubspaceMap_comp]
  rw [heq]
  infer_instance

include h in
private theorem projection_mapsTo (P : Opens U) :
    ∀ y ∈ restrictedStrictCarrier e U T P,
      (restrict P T).proj y ∈ (Subtype.val : P → U) ⁻¹' windowCarrier e U := by
  intro y hy
  have hold : y.val ∈ strictTransform e.dim T.proj (windowCarrier e U) :=
    (Set.ext_iff.mp (restrictedStrictCarrier_eq e U T P) y).mp hy
  change ((restrict P T).proj y).val ∈ windowCarrier e U
  rw [proj_restrict]
  exact h.strictTransform_subset_preimage hold

/-- The full native strict projection of the SAME literal restricted tower. -/
def projection (P : Opens U) : strictSpace e U T h P ⟶ baseSpace e U P :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (n := e.dim) (m := e.dim)
      (M := openPreimage T P) (N := P) (f := (restrict P T).proj)
      (C := restrictedStrictCarrier e U T P)
      (D := (Subtype.val : P → U) ⁻¹' windowCarrier e U)
      (restrict P T).contMDiff_proj (projection_mapsTo e U T h P))
    (actualSubspaceMap_point (restrict P T).contMDiff_proj (projection_mapsTo e U T h P)))

/-- The entire native endpoint inclusion lands in precisely the true inverse
image of the base-window range. -/
theorem strictInclusion_range (P : Opens U) :
    range (strictInclusion e U T h P).hom.left.base =
      (resolutionMorphism (windowCarrier_analytic e U) h).hom.left.base ⁻¹'
        range (baseInclusion e U P).hom.left.base := by
  rw [baseInclusion_range]
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact z.val.property
  · intro hy
    let z : openPreimage T P := ⟨y.val, hy⟩
    have hz : z ∈ restrictedStrictCarrier e U T P := by
      rw [restrictedStrictCarrier_eq]
      exact y.property
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- Equality of FULL original locally ringed maps, by actual subspace-map
composition and the literal restricted-tower projection square. -/
theorem projection_square (P : Opens U) :
    projection e U T h P ≫ baseInclusion e U P =
      strictInclusion e U T h P ≫ resolutionMorphism (windowCarrier_analytic e U) h := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change actualSubspaceMap (restrict P T).contMDiff_proj (projection_mapsTo e U T h P) ≫
      actualOpenSubspaceMap (n := e.dim) (windowCarrier e U) P =
    actualSubspaceMap (n := e.dim) (m := e.dim)
      (f := (Subtype.val : openPreimage T P → D)) contMDiff_subtype_val _ ≫
      actualSubspaceMap T.contMDiff_proj (fun _ hy => h.strictTransform_subset_preimage hy)
  rw [actualOpenSubspaceMap, ← actualSubspaceMap_comp, ← actualSubspaceMap_comp]
  exact actualSubspaceMap_congr (n := e.dim) (m := e.dim)
    (M := openPreimage T P) (N := U) (funext (proj_restrict P T)) _ _ _ _

/-- The SAME full projection square lies over the actual ORIGINAL space. -/
theorem projection_original_square (P : Opens U) :
    projection e U T h P ≫ (baseInclusion e U P ≫ windowMorphism e U) =
      strictInclusion e U T h P ≫
        (resolutionMorphism (windowCarrier_analytic e U) h ≫ windowMorphism e U) := by
  rw [← Category.assoc, projection_square, Category.assoc]

theorem projection_isProperMap (P : Opens U) :
    IsProperMap (projection e U T h P).hom.left.base := by
  change IsProperMap (fun y : restrictedStrictCarrier e U T P =>
    (⟨(restrict P T).proj y.val, projection_mapsTo e U T h P y.val y.property⟩ :
      (Subtype.val : P → U) ⁻¹' windowCarrier e U))
  refine isProperMap_of_comp_of_t2
    (g := (Subtype.val : ((Subtype.val : P → U) ⁻¹' windowCarrier e U) → P))
    (projection e U T h P).hom.left.base.hom.continuous continuous_subtype_val ?_
  exact (HironakaLocalPrincipalization.isProperMap_proj (restrict P T)).comp
    isClosed_closure.isClosedEmbedding_subtypeVal.isProperMap

theorem projection_surjective (P : Opens U) :
    Function.Surjective (projection e U T h P).hom.left.base := by
  intro v
  obtain ⟨y, hy⟩ := resolutionMap_surjective h ⟨v.val.val, v.property⟩
  have hTy : T.proj y.val = v.val.val := congrArg Subtype.val hy
  let z : openPreimage T P := ⟨y.val, by
    change T.proj y.val ∈ P
    rw [hTy]
    exact v.val.property⟩
  have hz : z ∈ restrictedStrictCarrier e U T P := by
    rw [restrictedStrictCarrier_eq]
    exact y.property
  refine ⟨⟨z, hz⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (proj_restrict P T z).trans hTy

theorem strictSpace_isSmooth (P : Opens U) : (strictSpace e U T h P).IsSmooth :=
  isSmooth_ofClosedAnalytic_of_isClosedSubmanifold
    (restrictedStrictCarrier_isClosedSubmanifold e U T h P)

/-- The full ORIGINAL regular locus on every literal refined base model. -/
theorem originalRegular_preimage (P : Opens U) :
    (baseInclusion e U P ≫ windowMorphism e U).hom.left.base ⁻¹' intrinsicRegularLocus X.obj =
      {v : ((Subtype.val : P → U) ⁻¹' windowCarrier e U) |
        v.val ∉ singularSet (n := e.dim) ((Subtype.val : P → U) ⁻¹' windowCarrier e U)} := by
  ext v
  rw [HironakaResolutionSpaceLocal.singularSet_preimage_val P]
  exact Set.ext_iff.mp (windowMorphism_regular_preimage e U) ⟨v.val.val, v.property⟩

end
end Hironaka.Analytic.Unibranch.OriginalLocalStrictWindowRestriction
