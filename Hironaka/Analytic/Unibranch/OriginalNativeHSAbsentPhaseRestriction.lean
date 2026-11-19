import Hironaka.Analytic.Unibranch.OriginalNativePrecompactNeighbourhood
import Hironaka.Analytic.Unibranch.OriginalNativePhysicalHistoryRestriction
import Hironaka.Analytic.Unibranch.OriginalNativeHSThresholdIsomorphism

/-! A genuine present phase absent on a smaller compact overlap restricts
to a FULL native iso, retaining its SAME finite physical history/length.
Blueprint FIRST: original-native-hs-absent-phase-restriction.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSAbsentPhaseRestriction
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSOuterHistory OriginalIntrinsicHSSuperlevels
  OriginalRelativelyCompactRestriction

variable {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y) (H : ℕ → ℕ)
  (K : Set X.obj.left) (hK : IsCompact K)
  (hOff : IsIsoOver h.projection (originalSingularHSThreshold X H)ᶜ)
  (hEmpty : K ∩ originalSingularHSThreshold X H=∅)

/-- Ordinary compactness and the actual full off-threshold inverse derive
ONE genuine neighbourhood, retaining the whole original compact overlap. -/
def neighbourhood : OriginalNativePrecompactNeighbourhood.Neighbourhood X K
    ⟨(originalSingularHSThreshold X H)ᶜ,hOff.isOpen⟩ :=
  OriginalNativePrecompactNeighbourhood.neighbourhood X K hK
    ⟨(originalSingularHSThreshold X H)ᶜ,hOff.isOpen⟩ (fun x hx hxD =>
      Set.notMem_empty x (hEmpty ▸ (show x ∈ K ∩ originalSingularHSThreshold X H from ⟨hx,hxD⟩)))

local notation "N" => neighbourhood h H K hK hOff hEmpty

theorem threshold_empty : originalSingularHSThreshold (N).source H=∅ := by
  rw [← (N).preimage_threshold H]
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (N).closure_subset (subset_closure x.property) hx

/-- The SAME literal finite history; no step, birth or clock is removed. -/
def history : PhysicalHistory (N).source
    (preimageRestriction (N).openSet h.projection (N).compactClosure h.singularModification.isProperMap) :=
  OriginalNativePhysicalHistoryRestriction.restrict h (N).openSet (N).compactClosure

theorem history_length : (history h H K hK hOff hEmpty).length=h.length :=
  OriginalNativePhysicalHistoryRestriction.length_restrict h (N).openSet (N).compactClosure

theorem projection_isIso : IsIso (history h H K hK hOff hEmpty).projection := by
  have hi := OriginalNativeHSThresholdIsomorphism.isIsoOver_restrictionProjection_threshold_compl H
    h.projection h.singularModification.isProperMap (N).openSet (N).compactClosure hOff
  have hAbsent : originalSingularHSThreshold (restriction X (N).openSet (N).compactClosure) H=∅ :=
    threshold_empty h H K hK hOff hEmpty
  rw [hAbsent,compl_empty] at hi
  have hi' : IsIsoOver (history h H K hK hOff hEmpty).projection univ := by
    change IsIsoOver (OriginalNativePhysicalHistoryRestriction.restrict h (N).openSet (N).compactClosure).projection univ
    rw [OriginalNativePhysicalHistoryRestriction.projection_restrict]
    exact hi
  obtain ⟨V,j,hj,hjr,hcomp,hcompr⟩ := hi'
  let : LocallyRingedSpace.IsOpenImmersion j := hj
  have hjs : Function.Surjective j.base := range_eq_univ.mp (by simpa only [preimage_univ] using hjr)
  let : Epi j.base := (TopCat.epi_iff_surjective _).mpr hjs
  let : IsIso j := LocallyRingedSpace.IsOpenImmersion.to_iso j
  let : LocallyRingedSpace.IsOpenImmersion
      (j ≫ (history h H K hK hOff hEmpty).projection.hom.left) := hcomp
  have hcs : Function.Surjective (j ≫ (history h H K hK hOff hEmpty).projection.hom.left).base :=
    range_eq_univ.mp hcompr
  let : Epi (j ≫ (history h H K hK hOff hEmpty).projection.hom.left).base :=
    (TopCat.epi_iff_surjective _).mpr hcs
  let : IsIso (j ≫ (history h H K hK hOff hEmpty).projection.hom.left) :=
    LocallyRingedSpace.IsOpenImmersion.to_iso _
  have : IsIso (history h H K hK hOff hEmpty).projection.hom.left := IsIso.of_isIso_comp_left j _
  have : IsIso ((Over.forget _).map (history h H K hK hOff hEmpty).projection.hom) := this
  have : IsIso (history h H K hK hOff hEmpty).projection.hom :=
    isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso ((ObjectProperty.ι _).map (history h H K hK hOff hEmpty).projection) := this
  exact isIso_of_reflects_iso _ (ObjectProperty.ι _)

/-- This iso's forward map is literally the restricted physical projection. -/
def comparison :
    preimageRestriction (N).openSet h.projection (N).compactClosure h.singularModification.isProperMap ≅
      (N).source := by
  let : IsIso (history h H K hK hOff hEmpty).projection := projection_isIso h H K hK hOff hEmpty
  exact asIso (history h H K hK hOff hEmpty).projection

theorem comparison_projection : (comparison h H K hK hOff hEmpty).hom=
    (history h H K hK hOff hEmpty).projection := rfl

theorem comparison_square : (comparison h H K hK hOff hEmpty).hom ≫ (N).inclusion =
    inclusion Y (preimageOpen (N).openSet h.projection)
      (isCompact_closure_preimage (N).openSet h.projection (N).compactClosure h.singularModification.isProperMap) ≫
      h.projection :=
  OriginalNativePhysicalHistoryRestriction.projection_square h (N).openSet (N).compactClosure

theorem comparison_inverse_square :
    (comparison h H K hK hOff hEmpty).inv ≫
      inclusion Y (preimageOpen (N).openSet h.projection)
        (isCompact_closure_preimage (N).openSet h.projection (N).compactClosure h.singularModification.isProperMap) ≫
        h.projection = (N).inclusion := by
  let E := comparison h H K hK hOff hEmpty
  have hh := congrArg (fun f : (preimageRestriction (N).openSet h.projection (N).compactClosure
    h.singularModification.isProperMap) ⟶ X => E.inv ≫ f)
    (comparison_square h H K hK hOff hEmpty)
  dsimp only [E] at hh
  exact hh.symm.trans ((comparison h H K hK hOff hEmpty).inv_hom_id_assoc (N).inclusion)

theorem comparison_scalar : (comparison h H K hK hOff hEmpty).hom.hom.left ≫ (N).source.obj.hom =
    (preimageRestriction (N).openSet h.projection (N).compactClosure
      h.singularModification.isProperMap).obj.hom :=
  Over.w (comparison h H K hK hOff hEmpty).hom.hom

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSAbsentPhaseRestriction
