import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterHistory
import Hironaka.Analytic.Unibranch.OriginalNativeBlowupOpenRestriction

/-! The SAME finite physical native history restricts chronologically to
the literal inverse open. Every native step is retained, including empty
and Cartier steps; properness is to the actual restricted base only.
Blueprint FIRST: original-native-physical-history-restriction.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativePhysicalHistoryRestriction
noncomputable section
open Hironaka Hironaka
  SourceReducedComplexSpace HironakaG11SingularCentreModification
  HironakaIntrinsicComplexAnalyticRegularLocus OriginalNativeHSOuterHistory
  OriginalRelativelyCompactRestriction

private theorem step_restrict {X Y : SourceReducedComplexSpace} (p : Y ⟶ X)
    (hp : IsSingularCentreStep p) (U : Opens X.obj.left)
    (hU : IsCompact (closure (U : Set X.obj.left))) :
    IsSingularCentreStep (restrictionProjection U p hU hp.isSingularCentreModification.isProperMap) := by
  obtain ⟨S,j,hj,hsing⟩ := hp
  exact OriginalNativeBlowupOpenRestriction.restriction_isSingularCentreStep p j hj U hU hsing

/-- Literal nil/snoc restriction of the actual finite chronological
history. No endpoint comparison or finite-step certificate is an input. -/
def restrict {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :
    PhysicalHistory (restriction X U hU)
      (preimageRestriction U h.projection hU h.singularModification.isProperMap) :=
  match Y,h with
  | _,.nil _ => .nil (restriction X U hU)
  | _,.snoc k p hp =>
      .snoc (restrict k U hU)
        (restrictionProjection (preimageOpen U k.projection) p
          (isCompact_closure_preimage U k.projection hU k.singularModification.isProperMap)
          hp.isSingularCentreModification.isProperMap)
        (step_restrict p hp (preimageOpen U k.projection)
          (isCompact_closure_preimage U k.projection hU k.singularModification.isProperMap))
termination_by structural h

theorem restrict_nil (X : SourceReducedComplexSpace) (U : Opens X.obj.left)
    (hU : IsCompact (closure (U : Set X.obj.left))) :
    restrict (.nil X) U hU = .nil (restriction X U hU) := rfl

theorem restrict_snoc {X Y Z : SourceReducedComplexSpace} (h : PhysicalHistory X Y)
    (p : Z ⟶ Y) (hp : IsSingularCentreStep p) (U : Opens X.obj.left)
    (hU : IsCompact (closure (U : Set X.obj.left))) :
    restrict (.snoc h p hp) U hU =
      .snoc (restrict h U hU)
        (restrictionProjection (preimageOpen U h.projection) p
          (isCompact_closure_preimage U h.projection hU h.singularModification.isProperMap)
          hp.isSingularCentreModification.isProperMap)
        (step_restrict p hp (preimageOpen U h.projection)
          (isCompact_closure_preimage U h.projection hU h.singularModification.isProperMap)) := rfl

theorem length_restrict {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :
    (restrict h U hU).length = h.length := by
  induction h with
  | nil => rfl
  | snoc h p hp ih => exact congrArg (fun n => n+1) ih

private theorem projection_formula {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :
    ∀ y : (preimageRestriction U h.projection hU h.singularModification.isProperMap).obj.left,
      ((restrict h U hU).projection.hom.left.base y).val = h.projection.hom.left.base y.val := by
  induction h with
  | nil => intro y; rfl
  | @snoc Y Z h p hp ih =>
      intro y
      let pU := restrictionProjection (preimageOpen U h.projection) p
        (isCompact_closure_preimage U h.projection hU h.singularModification.isProperMap)
        hp.isSingularCentreModification.isProperMap
      exact (ih (pU.hom.left.base y)).trans
        (congrArg h.projection.hom.left.base
          (restrictionProjection_base (preimageOpen U h.projection) p
            (isCompact_closure_preimage U h.projection hU h.singularModification.isProperMap)
            hp.isSingularCentreModification.isProperMap y))

theorem projection_restrict {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :
    (restrict h U hU).projection =
      restrictionProjection U h.projection hU h.singularModification.isProperMap := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro y
  apply Subtype.ext
  exact (projection_formula h U hU y).trans
    (restrictionProjection_base U h.projection hU h.singularModification.isProperMap y).symm

theorem projection_square {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :
    (restrict h U hU).projection ≫ inclusion X U hU =
      inclusion Y (preimageOpen U h.projection)
        (isCompact_closure_preimage U h.projection hU h.singularModification.isProperMap) ≫ h.projection :=
  (congrArg (fun a => a ≫ inclusion X U hU) (projection_restrict h U hU)).trans
    (restrictionProjection_inclusion U h.projection hU h.singularModification.isProperMap)

theorem projection_point {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left)))
    (y : (preimageRestriction U h.projection hU h.singularModification.isProperMap).obj.left) :
    ((restrict h U hU).projection.hom.left.base y).val = h.projection.hom.left.base y.val :=
  congrArg (fun k => k.hom.left.base y) (projection_square h U hU)

theorem scalar {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :
    (restrict h U hU).projection.hom.left ≫ (restriction X U hU).obj.hom =
      (preimageRestriction U h.projection hU h.singularModification.isProperMap).obj.hom :=
  Over.w (restrict h U hU).projection.hom

theorem singularModification {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :
    IsSingularCentreModification (restrict h U hU).projection :=
  (restrict h U hU).singularModification

theorem proper {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :
    IsProperMap (restrict h U hU).projection.hom.left.base :=
  (singularModification h U hU).isProperMap

theorem surjective {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :
    Function.Surjective (restrict h U hU).projection.hom.left.base :=
  (singularModification h U hU).surjective

theorem originalReg {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :
    IsIsoOver (restrict h U hU).projection (intrinsicRegularLocus (restriction X U hU).obj) :=
  (singularModification h U hU).isIsoOver_intrinsicRegularLocus

end
end Hironaka.Analytic.Unibranch.OriginalNativePhysicalHistoryRestriction
