import Hironaka.Analytic.Unibranch.OriginalNativePhysicalHistoryRestriction
import Hironaka.Analytic.Unibranch.HironakaG1NativeModificationIsoTransport

/-! Extract ONE given actual finite history to the PRESCRIBED literal original
relatively compact open. Real same-range native iso/empty-centre step joins
the genuine restriction; no extra neighbourhood or phase supplier is chosen.
Blueprint FIRST: original-native-prescribed-open-history.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativePrescribedOpenHistory
noncomputable section
open Hironaka HironakaEmbeddedNativeMorphism
  SourceReducedComplexSpace HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaG11SingularCentreModification OriginalNativeHSOuterHistory
  OriginalRelativelyCompactRestriction

variable {X B Y : SourceReducedComplexSpace} (j : B ⟶ X)
  (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (U : Opens X.obj.left)
  (hU : IsCompact (closure (U : Set X.obj.left)))
  (hRange : closure (U : Set X.obj.left) ⊆ range j.hom.left.base)

/-- The literal prescribed inverse open, without an additional neighbourhood choice. -/
def pullbackOpen : Opens B.obj.left :=
  ⟨j.hom.left.base ⁻¹' (U : Set X.obj.left), U.isOpen.preimage j.hom.left.base.hom.continuous⟩

include hj hU hRange in
theorem pullbackOpen_compactClosure : IsCompact (closure (pullbackOpen j U : Set B.obj.left)) := by
  have hInv := hj.base_open.isEmbedding.isInducing.isCompact_preimage' hU hRange
  apply hInv.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · intro b hb
    exact subset_closure hb
  · exact isClosed_closure.preimage j.hom.left.base.hom.continuous

abbrev baseRestriction : SourceReducedComplexSpace :=
  restriction B (pullbackOpen j U) (pullbackOpen_compactClosure j hj U hU hRange)

abbrev baseInclusion : baseRestriction j hj U hU hRange ⟶ B :=
  inclusion B (pullbackOpen j U) (pullbackOpen_compactClosure j hj U hU hRange)

private theorem comparisonRange :
    range ((baseInclusion j hj U hU hRange).hom.left ≫ j.hom.left).base =
      range (inclusion X U hU).hom.left.base := by
  change range (fun b : pullbackOpen j U => j.hom.left.base b.val) =
    range (Subtype.val : U → X.obj.left)
  rw [Subtype.range_coe]
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact b.property
  · intro hx
    obtain ⟨b, rfl⟩ := hRange (subset_closure hx)
    exact ⟨⟨b, hx⟩, rfl⟩

private def rawComparison : (baseRestriction j hj U hU hRange).obj.left ≅ (restriction X U hU).obj.left := by
  let : LocallyRingedSpace.IsOpenImmersion j.hom.left := hj
  let : LocallyRingedSpace.IsOpenImmersion (baseInclusion j hj U hU hRange).hom.left :=
    inclusion_isOpenImmersion _ _ _
  exact openImmersionIsoOfRangeEq ((baseInclusion j hj U hU hRange).hom.left ≫ j.hom.left)
    (inclusion X U hU).hom.left (comparisonRange j hj U hU hRange)

private theorem rawComparison_square : (rawComparison j hj U hU hRange).hom ≫
    (inclusion X U hU).hom.left = (baseInclusion j hj U hU hRange).hom.left ≫ j.hom.left := by
  let : LocallyRingedSpace.IsOpenImmersion j.hom.left := hj
  let : LocallyRingedSpace.IsOpenImmersion (baseInclusion j hj U hU hRange).hom.left :=
    inclusion_isOpenImmersion _ _ _
  exact openImmersionIsoOfRangeEq_hom_fac _ _ (comparisonRange j hj U hU hRange)

/-- Full original native isomorphism onto the LITERAL prescribed X|U. -/
def comparison : baseRestriction j hj U hU hRange ≅ restriction X U hU := by
  let E := rawComparison j hj U hU hRange
  have hp : E.hom ≫ (restriction X U hU).obj.hom = (baseRestriction j hj U hU hRange).obj.hom := by
    calc
      _ = E.hom ≫ ((inclusion X U hU).hom.left ≫ X.obj.hom) := rfl
      _ = (E.hom ≫ (inclusion X U hU).hom.left) ≫ X.obj.hom := (Category.assoc _ _ _).symm
      _ = ((baseInclusion j hj U hU hRange).hom.left ≫ j.hom.left) ≫ X.obj.hom :=
        congrArg (fun a => a ≫ X.obj.hom) (rawComparison_square j hj U hU hRange)
      _ = _ := by
        rw [Category.assoc, Over.w j.hom]
        exact Over.w (baseInclusion j hj U hU hRange).hom
  exact ObjectProperty.isoMk sourceReducedComplexSpaceProperty (Over.isoMk E hp)

theorem comparison_square : (comparison j hj U hU hRange).hom ≫ inclusion X U hU =
    baseInclusion j hj U hU hRange ≫ j := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact rawComparison_square j hj U hU hRange

theorem comparison_scalar : (comparison j hj U hU hRange).hom.hom.left ≫
    (restriction X U hU).obj.hom = (baseRestriction j hj U hU hRange).obj.hom :=
  Over.w (comparison j hj U hU hRange).hom.hom

/-- A genuine empty-centre singular blowup, including the empty/zero-history cases. -/
theorem comparison_singularStep : IsSingularCentreStep (comparison j hj U hU hRange).hom := by
  refine ⟨HironakaG1NativeModificationIsoTransport.emptyCentre _,
    HironakaG1NativeModificationIsoTransport.emptyCentreInclusion _,
    HironakaG1NativeModificationIsoTransport.isSmoothCentreBlowup_iso (comparison j hj U hU hRange), ?_⟩
  rw [HironakaG1NativeModificationIsoTransport.emptyCentreInclusion_range]
  exact empty_subset _

variable (h : PhysicalHistory B Y)

/-- Literal endpoint of the SAME history restricted to the prescribed inverse open. -/
abbrev source : SourceReducedComplexSpace := preimageRestriction (pullbackOpen j U) h.projection
  (pullbackOpen_compactClosure j hj U hU hRange) h.singularModification.isProperMap

def sourceInclusion : source j hj U hU hRange h ⟶ Y :=
  inclusion Y (preimageOpen (pullbackOpen j U) h.projection)
    (isCompact_closure_preimage _ _ (pullbackOpen_compactClosure j hj U hU hRange)
      h.singularModification.isProperMap)

theorem sourceInclusion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (sourceInclusion j hj U hU hRange h).hom.left :=
  inclusion_isOpenImmersion _ _ _

/-- Real nil/snoc/append history over the LITERAL prescribed original X|U. -/
def history : PhysicalHistory (restriction X U hU) (source j hj U hU hRange h) :=
  ((PhysicalHistory.nil (restriction X U hU)).snoc (comparison j hj U hU hRange).hom
    (comparison_singularStep j hj U hU hRange)).append
      (OriginalNativePhysicalHistoryRestriction.restrict h (pullbackOpen j U)
        (pullbackOpen_compactClosure j hj U hU hRange))

theorem history_length : (history j hj U hU hRange h).length = h.length + 1 := by
  rw [history, PhysicalHistory.length_append]
  change 1 + (OriginalNativePhysicalHistoryRestriction.restrict h (pullbackOpen j U)
    (pullbackOpen_compactClosure j hj U hU hRange)).length = h.length + 1
  rw [OriginalNativePhysicalHistoryRestriction.length_restrict]
  exact Nat.add_comm _ _

theorem projection_formula : (history j hj U hU hRange h).projection =
    (OriginalNativePhysicalHistoryRestriction.restrict h (pullbackOpen j U)
      (pullbackOpen_compactClosure j hj U hU hRange)).projection ≫ (comparison j hj U hU hRange).hom := by
  simp only [history, PhysicalHistory.projection_append, PhysicalHistory.projection, Category.comp_id]

theorem projection_square : (history j hj U hU hRange h).projection ≫ inclusion X U hU =
    sourceInclusion j hj U hU hRange h ≫ h.projection ≫ j := by
  calc
    _ = ((OriginalNativePhysicalHistoryRestriction.restrict h (pullbackOpen j U)
        (pullbackOpen_compactClosure j hj U hU hRange)).projection ≫
        (comparison j hj U hU hRange).hom) ≫ inclusion X U hU :=
      congrArg (fun a => a ≫ inclusion X U hU) (projection_formula j hj U hU hRange h)
    _ = (OriginalNativePhysicalHistoryRestriction.restrict h (pullbackOpen j U)
        (pullbackOpen_compactClosure j hj U hU hRange)).projection ≫
        ((comparison j hj U hU hRange).hom ≫ inclusion X U hU) := Category.assoc _ _ _
    _ = (OriginalNativePhysicalHistoryRestriction.restrict h (pullbackOpen j U)
        (pullbackOpen_compactClosure j hj U hU hRange)).projection ≫
        (baseInclusion j hj U hU hRange ≫ j) :=
      congrArg (fun a => (OriginalNativePhysicalHistoryRestriction.restrict h (pullbackOpen j U)
        (pullbackOpen_compactClosure j hj U hU hRange)).projection ≫ a)
        (comparison_square j hj U hU hRange)
    _ = ((OriginalNativePhysicalHistoryRestriction.restrict h (pullbackOpen j U)
        (pullbackOpen_compactClosure j hj U hU hRange)).projection ≫
        baseInclusion j hj U hU hRange) ≫ j := (Category.assoc _ _ _).symm
    _ = (sourceInclusion j hj U hU hRange h ≫ h.projection) ≫ j :=
      congrArg (fun a => a ≫ j) (OriginalNativePhysicalHistoryRestriction.projection_square h
        (pullbackOpen j U) (pullbackOpen_compactClosure j hj U hU hRange))
    _ = _ := Category.assoc _ _ _

theorem scalar : (history j hj U hU hRange h).projection.hom.left ≫ (restriction X U hU).obj.hom =
    (source j hj U hU hRange h).obj.hom := Over.w (history j hj U hU hRange h).projection.hom

theorem singularModification : IsSingularCentreModification (history j hj U hU hRange h).projection :=
  (history j hj U hU hRange h).singularModification

theorem isModification : SmoothCentreModification.IsModification (history j hj U hU hRange h).projection :=
  (singularModification j hj U hU hRange h).toIsModification

theorem proper : IsProperMap (history j hj U hU hRange h).projection.hom.left.base :=
  (singularModification j hj U hU hRange h).isProperMap

theorem surjective : Function.Surjective (history j hj U hU hRange h).projection.hom.left.base :=
  (singularModification j hj U hU hRange h).surjective

theorem originalReg : IsIsoOver (history j hj U hU hRange h).projection
    (intrinsicRegularLocus (restriction X U hU).obj) :=
  (singularModification j hj U hU hRange h).isIsoOver_intrinsicRegularLocus

theorem source_smooth (hY : Y.IsSmooth) : (source j hj U hU hRange h).IsSmooth := by
  apply (OriginalIntrinsicSingularLocus.isSmooth_iff_intrinsicSingularLocus_eq_empty _).mpr
  have hOld := (OriginalIntrinsicSingularLocus.isSmooth_iff_intrinsicSingularLocus_eq_empty Y).mp hY
  exact (inclusion_preimage_intrinsicSingularLocus Y
    (preimageOpen (pullbackOpen j U) h.projection)
    (isCompact_closure_preimage _ _ (pullbackOpen_compactClosure j hj U hU hRange)
      h.singularModification.isProperMap)).symm.trans (by rw [hOld, preimage_empty]; rfl)

theorem resolution (hY : Y.IsSmooth) : IsResolution (history j hj U hU hRange h).projection :=
  (singularModification j hj U hU hRange h).isResolution (source_smooth j hj U hU hRange h hY)

end
end Hironaka.Analytic.Unibranch.OriginalNativePrescribedOpenHistory
