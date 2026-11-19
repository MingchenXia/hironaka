import Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspace
import Hironaka.Analytic.Unibranch.OriginalSmoothCentreBlowup
import Hironaka.Analytic.Unibranch.HironakaG11BlowupLocality
import Hironaka.Analytic.Unibranch.OriginalBimeromorphicSourceIso

/-! # Genuine empty-centre blowups and finite native modification transport

An ordinary full native isomorphism is realized by the actual empty analytic
centre, ENTIRE pulled unit ideal/rank-one data, original universal property
and proper-bimeromorphic geometry. No isomorphism is replaced by literal id.
Blueprint first; no initial resolution or compactness is assumed.
-/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeModificationIsoTransport

open Hironaka HironakaSingularModuleSheafStalk
  HironakaIntrinsicReducedCentreIdealSheaf HironakaNativePulledIdealSheaf
  SourceReducedComplexSpace SmoothCentreModification HironakaG11BlowupLocality

noncomputable section

variable {X Y Z X' Y' : SourceReducedComplexSpace}

/-- The ACTUAL native analytic empty-subspace factory. -/
def emptyCentre (X : SourceReducedComplexSpace) : SourceReducedComplexSpace :=
  OriginalAnalyticClosedSubspace.sourceObject X ∅ isAnalyticSubset_empty

/-- Its full original inclusion, including the original complex scalar map. -/
def emptyCentreInclusion (X : SourceReducedComplexSpace) : emptyCentre X ⟶ X :=
  OriginalAnalyticClosedSubspace.inclusion X ∅ isAnalyticSubset_empty

/-- Its entire actual point image is empty. -/
theorem emptyCentreInclusion_range (X : SourceReducedComplexSpace) :
    range (emptyCentreInclusion X).hom.left.base = ∅ :=
  OriginalAnalyticClosedSubspace.inclusion_range X ∅ isAnalyticSubset_empty

/-- Actual empty range derives native smoothness on the SAME source. -/
theorem emptyCentre_isSmooth (X : SourceReducedComplexSpace) : (emptyCentre X).IsSmooth := by
  intro z
  have hz : (emptyCentreInclusion X).hom.left.base z ∈ range (emptyCentreInclusion X).hom.left.base :=
    ⟨z, rfl⟩
  rw [emptyCentreInclusion_range] at hz
  exact hz.elim

/-- Every ENTIRE pulled empty-centre stalk ideal is the actual unit ideal. -/
theorem pulledEmpty_stalk_eq_top (X : SourceReducedComplexSpace) {A : LocallyRingedSpace.{0}}
    (F : A ⟶ X.obj.left) (a : A) :
    nativePulledIdealStalkIdeal F
      (intrinsicReducedCentreIdealModule X.obj.left ∅)
      (intrinsicReducedCentreIdealInclusion X.obj.left ∅) a = ⊤ := by
  have hunit := Set.ext_iff.mp
    (OriginalSmoothCentreBlowup.intrinsic_ideal_unitLocus_eq_compl X ∅ isAnalyticSubset_empty) (F.base a)
  have hr : LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf
      (intrinsicReducedCentreIdealModule X.obj.left ∅)
      (intrinsicReducedCentreIdealInclusion X.obj.left ∅) (F.base a)) = ⊤ :=
    hunit.mpr (by simp)
  change Ideal.map (F.stalkMap a).hom _ = ⊤
  rw [hr]
  exact Ideal.map_top _

/-- The LITERAL section 1 derives actual rank-one locally free module data. -/
theorem pulledEmpty_hasRankOneData (X : SourceReducedComplexSpace) {A : LocallyRingedSpace.{0}}
    (F : A ⟶ X.obj.left) :
    HasRankOneData (nativePulledIdealModule F
      (intrinsicReducedCentreIdealModule X.obj.left ∅)
      (intrinsicReducedCentreIdealInclusion X.obj.left ∅)) := by
  apply (hasRankOneData_iff F _ _).mpr
  intro a
  refine ⟨⊤, trivial, 1, ?_⟩
  intro y hy
  constructor
  · simpa only [map_one, Ideal.span_singleton_one] using pulledEmpty_stalk_eq_top X F y
  · simpa only [map_one] using (isRegular_one : IsRegular (1 : (A.presheaf.stalk y).carrier))

/-- Ordinary native E supplies its own Cartier data and FULL original ideal-blowup UP. -/
theorem isIdealBlowup_iso (E : Y ≅ X) :
    IsIdealBlowup E.hom (intrinsicReducedCentreIdealModule X.obj.left ∅)
      (intrinsicReducedCentreIdealInclusion X.obj.left ∅) := by
  refine ⟨pulledEmpty_hasRankOneData X E.hom.hom.left, ?_⟩
  intro A F _
  refine ⟨F ≫ E.inv, by simp, ?_⟩
  intro L hL
  calc
    L = (L ≫ E.hom) ≫ E.inv := by simp
    _ = F ≫ E.inv := congrArg (fun f => f ≫ E.inv) hL

private theorem iso_properBimeromorphic (E : Y ≅ X) : IsProperBimeromorphic E.hom := by
  have hid : IsProperBimeromorphic (𝟙 X) := by
    refine ⟨isProperMap_id, ∅, isAnalyticSubset_empty, by simp, by simp, ?_⟩
    exact IsIsoOver.id_of_isOpen X (by simp)
  simpa only [Category.comp_id] using hid.precomp_iso E

/-- Every full original native isomorphism is a REAL empty-centre smooth blowup. -/
theorem isSmoothCentreBlowup_iso (E : Y ≅ X) :
    IsSmoothCentreBlowup E.hom (emptyCentreInclusion X) := by
  refine ⟨emptyCentre_isSmooth X,
    OriginalAnalyticClosedSubspace.inclusion_isClosedEmbedding X ∅ isAnalyticSubset_empty,
    OriginalAnalyticClosedSubspace.inclusion_stalk_surjective X ∅ isAnalyticSubset_empty,
    ?_, ?_, ?_, iso_properBimeromorphic E⟩
  · rw [emptyCentreInclusion_range]
    exact isAnalyticSubset_empty
  · rw [emptyCentreInclusion_range]
    simp
  · rw [emptyCentreInclusion_range]
    exact isIdealBlowup_iso E

/-- A genuine one-step witness handles arbitrary isos, including zero-history comparisons. -/
theorem isModification_iso (E : Y ≅ X) : IsModification E.hom :=
  IsModification.of_step ⟨emptyCentre X, emptyCentreInclusion X, isSmoothCentreBlowup_iso E⟩

/-- Actual source-isomorphism transport retains the SAME full composite. -/
theorem isModification_precomp_iso {p : Y ⟶ X} (hp : IsModification p) (E : Z ≅ Y) :
    IsModification (E.hom ≫ p) :=
  (isModification_iso E).comp hp

/-- Actual base-isomorphism transport retains the SAME full composite. -/
theorem isModification_postcomp_iso {p : Y ⟶ X} (hp : IsModification p) (E : X ≅ Z) :
    IsModification (p ≫ E.hom) :=
  hp.comp (isModification_iso E)

/-- Both independent native isomorphisms transport a real finite modification. -/
theorem isModification_conjugate {p : Y ⟶ X} (hp : IsModification p)
    (E : Y' ≅ Y) (F : X ≅ X') : IsModification (E.hom ≫ p ≫ F.hom) :=
  (isModification_iso E).comp (hp.comp (isModification_iso F))

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeModificationIsoTransport
