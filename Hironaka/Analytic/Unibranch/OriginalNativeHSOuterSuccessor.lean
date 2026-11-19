import Hironaka.Analytic.Unibranch.OriginalNativeCompactShadowRank
import Hironaka.Analytic.Unibranch.OriginalNativePhysicalHistoryResaturation
import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowFactoryGeometry

/-! ONE concrete outer successor from ordinary present history/compact
shadow, using the actual native phase factory and whole-fibre resaturation.
Blueprint FIRST: original-native-resaturated-phase-rank.tex.
The rank map is proper TO the actual restricted old source, never the
phase composite through an open immersion into the larger old source. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSOuterSuccessor
noncomputable section
open Hironaka Hironaka
  SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11CompatibleAnalyticCover
  HironakaG11HSPhaseInduction
  OriginalNativeHSOuterHistory OriginalRelativelyCompactRestriction
  OriginalNativeCompactShadowRank OriginalNativeHSThresholdIsomorphism

variable {B Y : SourceReducedComplexSpace} (h : PhysicalHistory B Y) (K : Set B.obj.left)

def shadow : Set Y.obj.left := h.projection.hom.left.base ⁻¹' K

theorem shadow_isCompact (hK : IsCompact K) : IsCompact (shadow h K) :=
  h.singularModification.isProperMap.isCompact_preimage hK

private theorem phaseNonempty
    (hne : (intrinsicSingularLocus Y.obj ∩ shadow h K).Nonempty) :
    (shadow h K ∩ intrinsicSingularLocus Y.obj).Nonempty := by
  simpa only [inter_comm] using hne

variable (hK : IsCompact K) (hne : (intrinsicSingularLocus Y.obj ∩ shadow h K).Nonempty)

private abbrev phaseBase := OriginalNativeHSShadowPhaseFactory.base Y (shadow h K)
  (shadow_isCompact h K hK) (phaseNonempty h K hne)
private abbrev phaseSource := OriginalNativeHSShadowPhaseFactory.source Y (shadow h K)
  (shadow_isCompact h K hK) (phaseNonempty h K hne)
private abbrev phaseHistory : PhysicalHistory (phaseBase h K hK hne) (phaseSource h K hK hne) :=
  OriginalNativeHSShadowPhaseFactory.history Y (shadow h K)
    (shadow_isCompact h K hK) (phaseNonempty h K hne)
private abbrev phaseInclusion : phaseBase h K hK hne ⟶ Y :=
  OriginalNativeHSShadowPhaseFactory.baseInclusion Y (shadow h K)
    (shadow_isCompact h K hK) (phaseNonempty h K hne)
private theorem phaseInclusion_open :
    LocallyRingedSpace.IsOpenImmersion (phaseInclusion h K hK hne).hom.left :=
  OriginalNativeHSShadowPhaseFactory.baseInclusion_isOpenImmersion Y (shadow h K)
    (shadow_isCompact h K hK) (phaseNonempty h K hne)
private theorem phaseCover : h.projection.hom.left.base ⁻¹' K ⊆
    range (phaseInclusion h K hK hne).hom.left.base :=
  OriginalNativeHSShadowPhaseFactory.compact_retained Y (shadow h K)
    (shadow_isCompact h K hK) (phaseNonempty h K hne)

def neighbourhood := OriginalNativePhysicalHistoryResaturation.neighbourhood h
  (phaseInclusion h K hK hne) (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne)

abbrev base : SourceReducedComplexSpace := (neighbourhood h K hK hne).source

abbrev source : SourceReducedComplexSpace := OriginalNativePhysicalHistoryResaturation.source h
  (phaseInclusion h K hK hne) (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne)
  (phaseHistory h K hK hne)

def history : PhysicalHistory (base h K hK hne) (source h K hK hne) :=
  OriginalNativePhysicalHistoryResaturation.history h (phaseInclusion h K hK hne)
    (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne) (phaseHistory h K hK hne)

def compact : Set (base h K hK hne).obj.left :=
  (neighbourhood h K hK hne).inclusion.hom.left.base ⁻¹' K

theorem compact_isCompact : IsCompact (compact h K hK hne) :=
  (neighbourhood h K hK hne).shadow_compact hK

theorem compact_retained : K ⊆ range (neighbourhood h K hK hne).inclusion.hom.left.base := by
  intro x hx
  exact ⟨⟨x,(neighbourhood h K hK hne).contains hx⟩,rfl⟩

def sourceMap : source h K hK hne ⟶ Y :=
  OriginalNativePhysicalHistoryResaturation.sourceInclusion h (phaseInclusion h K hK hne)
    (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne) (phaseHistory h K hK hne) ≫
      (phaseHistory h K hK hne).projection ≫ phaseInclusion h K hK hne

theorem projection_square : (history h K hK hne).projection ≫
    (neighbourhood h K hK hne).inclusion = sourceMap h K hK hne ≫ h.projection :=
  OriginalNativePhysicalHistoryResaturation.projection_square h (phaseInclusion h K hK hne)
    (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne) (phaseHistory h K hK hne)

abbrev oldSource : SourceReducedComplexSpace :=
  OriginalNativePhysicalHistoryResaturation.oldSource h (phaseInclusion h K hK hne)
    (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne)

abbrev oldInclusion : oldSource h K hK hne ⟶ Y :=
  OriginalNativePhysicalHistoryResaturation.oldInclusion h (phaseInclusion h K hK hne)
    (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne)

private abbrev cutBase := OriginalNativePhysicalHistoryResaturation.phaseTarget h
  (phaseInclusion h K hK hne) (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne)
private abbrev cutOpen := OriginalNativePhysicalHistoryResaturation.phaseOpen h
  (phaseInclusion h K hK hne) (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne)
private theorem cutOpen_compact : IsCompact (closure (cutOpen h K hK hne : Set (phaseBase h K hK hne).obj.left)) :=
  OriginalNativePhysicalHistoryResaturation.phaseOpen_compactClosure h
    (phaseInclusion h K hK hne) (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne)
private abbrev comparison : cutBase h K hK hne ≅ oldSource h K hK hne :=
  OriginalNativePhysicalHistoryResaturation.comparison h (phaseInclusion h K hK hne)
    (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne)
private theorem comparison_step : HironakaG11SingularCentreModification.IsSingularCentreStep
    (comparison h K hK hne).hom :=
  OriginalNativePhysicalHistoryResaturation.comparison_singularStep h (phaseInclusion h K hK hne)
    (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne)

/-- The ACTUAL proper rank suffix, with its original empty and phase steps. -/
def phaseSuffix : PhysicalHistory (oldSource h K hK hne) (source h K hK hne) :=
  ((PhysicalHistory.nil (oldSource h K hK hne)).snoc
    (comparison h K hK hne).hom (comparison_step h K hK hne)).append
      (OriginalNativePhysicalHistoryRestriction.restrict (phaseHistory h K hK hne)
        (cutOpen h K hK hne) (cutOpen_compact h K hK hne))

private abbrev cutProjection : source h K hK hne ⟶ cutBase h K hK hne :=
  restrictionProjection (cutOpen h K hK hne) (phaseHistory h K hK hne).projection
    (cutOpen_compact h K hK hne) (phaseHistory h K hK hne).singularModification.isProperMap

theorem phaseSuffix_projection : (phaseSuffix h K hK hne).projection =
    cutProjection h K hK hne ≫ (comparison h K hK hne).hom := by
  simp only [phaseSuffix,PhysicalHistory.projection_append,PhysicalHistory.projection,
    OriginalNativePhysicalHistoryRestriction.projection_restrict,Category.comp_id]

theorem phaseSuffix_proper : IsProperMap (phaseSuffix h K hK hne).projection.hom.left.base :=
  (phaseSuffix h K hK hne).singularModification.isProperMap

private abbrev cutInclusion : cutBase h K hK hne ⟶ phaseBase h K hK hne :=
  OriginalNativePhysicalHistoryResaturation.phaseInclusion h (phaseInclusion h K hK hne)
    (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne)
private abbrev sourceInclusion : source h K hK hne ⟶ phaseSource h K hK hne :=
  OriginalNativePhysicalHistoryResaturation.sourceInclusion h (phaseInclusion h K hK hne)
    (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne) (phaseHistory h K hK hne)

private theorem cutProjection_square : cutProjection h K hK hne ≫ cutInclusion h K hK hne=
    sourceInclusion h K hK hne ≫ (phaseHistory h K hK hne).projection :=
  restrictionProjection_inclusion (cutOpen h K hK hne) (phaseHistory h K hK hne).projection
    (cutOpen_compact h K hK hne) (phaseHistory h K hK hne).singularModification.isProperMap

theorem phaseSuffix_old_square : (phaseSuffix h K hK hne).projection ≫ oldInclusion h K hK hne=
    sourceMap h K hK hne := by
  have hc : (comparison h K hK hne).hom ≫ oldInclusion h K hK hne=
      cutInclusion h K hK hne ≫ phaseInclusion h K hK hne :=
    OriginalNativePhysicalHistoryResaturation.comparison_square h (phaseInclusion h K hK hne)
      (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne)
  calc
    _ = (cutProjection h K hK hne ≫ (comparison h K hK hne).hom) ≫ oldInclusion h K hK hne :=
      congrArg (fun a=>a ≫ oldInclusion h K hK hne) (phaseSuffix_projection h K hK hne)
    _ = cutProjection h K hK hne ≫ ((comparison h K hK hne).hom ≫ oldInclusion h K hK hne) :=
      Category.assoc _ _ _
    _ = cutProjection h K hK hne ≫ (cutInclusion h K hK hne ≫ phaseInclusion h K hK hne) :=
      congrArg (fun a=>cutProjection h K hK hne ≫ a) hc
    _ = (cutProjection h K hK hne ≫ cutInclusion h K hK hne) ≫ phaseInclusion h K hK hne :=
      (Category.assoc _ _ _).symm
    _ = (sourceInclusion h K hK hne ≫ (phaseHistory h K hK hne).projection) ≫ phaseInclusion h K hK hne :=
      congrArg (fun a=>a ≫ phaseInclusion h K hK hne) (cutProjection_square h K hK hne)
    _ = sourceMap h K hK hne := Category.assoc _ _ _

private def phaseTargetMap : oldSource h K hK hne ⟶ phaseBase h K hK hne :=
  (comparison h K hK hne).inv ≫ cutInclusion h K hK hne

private theorem phaseTargetMap_open :
    LocallyRingedSpace.IsOpenImmersion (phaseTargetMap h K hK hne).hom.left := by
  have hc : LocallyRingedSpace.IsOpenImmersion (comparison h K hK hne).inv.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft (comparison h K hK hne).symm).hom
    infer_instance
  exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (comparison h K hK hne).inv.hom.left hc
    (cutInclusion h K hK hne).hom.left (inclusion_isOpenImmersion _ _ _)

private theorem sourceInclusion_open :
    LocallyRingedSpace.IsOpenImmersion (sourceInclusion h K hK hne).hom.left :=
  inclusion_isOpenImmersion _ _ _

private theorem oldInclusion_open : LocallyRingedSpace.IsOpenImmersion (oldInclusion h K hK hne).hom.left :=
  inclusion_isOpenImmersion _ _ _

private theorem phaseSuffix_phase_square : (phaseSuffix h K hK hne).projection ≫ phaseTargetMap h K hK hne=
    sourceInclusion h K hK hne ≫ (phaseHistory h K hK hne).projection := by
  calc
    _ = cutProjection h K hK hne ≫ cutInclusion h K hK hne := by
      rw [phaseSuffix_projection]
      simp only [phaseTargetMap,Category.assoc,Iso.hom_inv_id_assoc]
    _ = _ := cutProjection_square h K hK hne

private theorem phaseTargetMap_range : range (phaseTargetMap h K hK hne).hom.left.base=
    range (cutInclusion h K hK hne).hom.left.base := by
  ext b
  change (∃a,(cutInclusion h K hK hne).hom.left.base ((comparison h K hK hne).inv.hom.left.base a)=b) ↔
    ∃a,(cutInclusion h K hK hne).hom.left.base a=b
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨_,rfl⟩
  · rintro ⟨a,rfl⟩
    refine ⟨(comparison h K hK hne).hom.hom.left.base a,?_⟩
    exact congrArg (cutInclusion h K hK hne).hom.left.base
      (congrArg (fun f : cutBase h K hK hne ⟶ cutBase h K hK hne=>f.hom.left.base a)
        (comparison h K hK hne).hom_inv_id)

private theorem phaseSuffix_saturated : range (sourceInclusion h K hK hne).hom.left.base=
    (phaseHistory h K hK hne).projection.hom.left.base ⁻¹'
      range (phaseTargetMap h K hK hne).hom.left.base := by
  rw [phaseTargetMap_range]
  change range (Subtype.val : preimageOpen (cutOpen h K hK hne) (phaseHistory h K hK hne).projection →
    (phaseSource h K hK hne).obj.left)=
      (phaseHistory h K hK hne).projection.hom.left.base ⁻¹'
        range (Subtype.val : cutOpen h K hK hne → (phaseBase h K hK hne).obj.left)
  rw [Subtype.range_coe,Subtype.range_coe]
  rfl

private def profile : ℕ → ℕ := originalStalkHS Y
  (OriginalNativeHSShadowPhaseFactory.maximum Y (shadow h K) (shadow_isCompact h K hK)
    (phaseNonempty h K hne)).point

theorem phaseSuffix_off_threshold : IsIsoOver (phaseSuffix h K hK hne).projection
    (originalSingularHSThreshold (oldSource h K hK hne) (profile h K hK hne))ᶜ :=
  isIsoOver_open_square_threshold_compl (profile h K hK hne)
    (phaseHistory h K hK hne).projection (phaseSuffix h K hK hne).projection
    (sourceInclusion h K hK hne) (phaseTargetMap h K hK hne)
    (sourceInclusion_open h K hK hne) (phaseTargetMap_open h K hK hne)
    (phaseSuffix_phase_square h K hK hne) (phaseSuffix_saturated h K hK hne)
    (OriginalNativeHSShadowFactoryGeometry.isIsoOver_threshold_compl Y (shadow h K)
      (shadow_isCompact h K hK) (phaseNonempty h K hne))

theorem phaseSuffix_hs_nonincrease (z : (source h K hK hne).obj.left) :
    originalStalkHS (source h K hK hne) z ≤ originalStalkHS (oldSource h K hK hne)
      ((phaseSuffix h K hK hne).projection.hom.left.base z) := by
  have hi:=OriginalNativeHSShadowFactoryGeometry.hs_nonincrease Y (shadow h K)
    (shadow_isCompact h K hK) (phaseNonempty h K hne) ((sourceInclusion h K hK hne).hom.left.base z)
  have he:=congrArg (fun f : source h K hK hne ⟶ phaseBase h K hK hne=>f.hom.left.base z)
    (phaseSuffix_phase_square h K hK hne)
  change (phaseTargetMap h K hK hne).hom.left.base ((phaseSuffix h K hK hne).projection.hom.left.base z)=
    (phaseHistory h K hK hne).projection.hom.left.base ((sourceInclusion h K hK hne).hom.left.base z) at he
  rw [← he,originalStalkHS_openImmersion (sourceInclusion h K hK hne) (sourceInclusion_open h K hK hne),
    originalStalkHS_openImmersion (phaseTargetMap h K hK hne) (phaseTargetMap_open h K hK hne)] at hi
  exact hi

theorem phaseSuffix_threshold_empty :
    originalSingularHSThreshold (source h K hK hne) (profile h K hK hne)=∅ := by
  have he:=threshold_preimage_openImmersion (profile h K hK hne)
    (sourceInclusion h K hK hne) (sourceInclusion_open h K hK hne)
  have ht : originalSingularHSThreshold (phaseSource h K hK hne) (profile h K hK hne)=∅ :=
    OriginalNativeHSShadowPhaseFactory.threshold_empty Y (shadow h K)
      (shadow_isCompact h K hK) (phaseNonempty h K hne)
  rw [ht,preimage_empty] at he
  exact he.symm

def oldShadow : Set (oldSource h K hK hne).obj.left :=
  (oldInclusion h K hK hne).hom.left.base ⁻¹' shadow h K

theorem oldShadow_retained : shadow h K ⊆ range (oldInclusion h K hK hne).hom.left.base := by
  intro y hy
  exact ⟨⟨y,(neighbourhood h K hK hne).contains hy⟩,rfl⟩

theorem oldShadow_isCompact : IsCompact (oldShadow h K hK hne) :=
  (oldInclusion_open h K hK hne).base_open.isEmbedding.isInducing.isCompact_preimage'
    (shadow_isCompact h K hK) (oldShadow_retained h K hK hne)

theorem original_projection_factorization : (history h K hK hne).projection ≫
    (neighbourhood h K hK hne).inclusion =
      (phaseSuffix h K hK hne).projection ≫ oldInclusion h K hK hne ≫ h.projection := by
  calc
    _ = sourceMap h K hK hne ≫ h.projection := projection_square h K hK hne
    _ = ((phaseSuffix h K hK hne).projection ≫ oldInclusion h K hK hne) ≫ h.projection :=
      congrArg (fun a=>a ≫ h.projection) (phaseSuffix_old_square h K hK hne).symm
    _ = _ := Category.assoc _ _ _

theorem new_shadow_eq : (history h K hK hne).projection.hom.left.base ⁻¹' compact h K hK hne=
    (phaseSuffix h K hK hne).projection.hom.left.base ⁻¹' oldShadow h K hK hne := by
  ext z
  exact iff_of_eq (congrArg (fun f : source h K hK hne ⟶ B=>f.hom.left.base z∈K)
    (original_projection_factorization h K hK hne))

private abbrev maximum := OriginalNativeHSShadowPhaseFactory.maximum Y (shadow h K)
  (shadow_isCompact h K hK) (phaseNonempty h K hne)

private def maximumInOldSource : (oldSource h K hK hne).obj.left :=
  ⟨(maximum h K hK hne).point,(neighbourhood h K hK hne).contains (maximum h K hK hne).in_compact⟩

private theorem maximum_mem_oldShadow : maximumInOldSource h K hK hne∈oldShadow h K hK hne :=
  (maximum h K hK hne).in_compact

private theorem maximum_singular : maximumInOldSource h K hK hne∈
    intrinsicSingularLocus (oldSource h K hK hne).obj :=
  (Set.ext_iff.mp (preimage_intrinsicSingularLocus_of_isOpenImmersion
    (oldInclusion h K hK hne) (oldInclusion_open h K hK hne)) _).mp (maximum h K hK hne).singular

private theorem maximum_profile : profile h K hK hne=
    originalStalkHS (oldSource h K hK hne) (maximumInOldSource h K hK hne) :=
  originalStalkHS_openImmersion (oldInclusion h K hK hne) (oldInclusion_open h K hK hne)
    (maximumInOldSource h K hK hne)

private theorem maximum_maximal (x : (oldSource h K hK hne).obj.left) (hx : x∈oldShadow h K hK hne)
    (hxS : x∈intrinsicSingularLocus (oldSource h K hK hne).obj) :
    toLex (originalStalkHS (oldSource h K hK hne) x) ≤
      toLex (originalStalkHS (oldSource h K hK hne) (maximumInOldSource h K hK hne)) := by
  have hxSY : (oldInclusion h K hK hne).hom.left.base x∈intrinsicSingularLocus Y.obj :=
    (Set.ext_iff.mp (preimage_intrinsicSingularLocus_of_isOpenImmersion
      (oldInclusion h K hK hne) (oldInclusion_open h K hK hne)) x).mpr hxS
  have hm := (maximum h K hK hne).maximal ((oldInclusion h K hK hne).hom.left.base x) hx hxSY
  change toLex (originalStalkHS Y ((oldInclusion h K hK hne).hom.left.base x)) ≤
    toLex (profile h K hK hne) at hm
  rw [originalStalkHS_openImmersion (oldInclusion h K hK hne) (oldInclusion_open h K hK hne),
    maximum_profile] at hm
  exact hm

private theorem rank_eq_of_compact_set_eq {X : SourceReducedComplexSpace} {S T : Set X.obj.left}
    (hS : IsCompact S) (hT : IsCompact T) (heq : S=T) : rank X S hS=rank X T hT := by
  cases heq
  rfl

/-- Actual strict descent for the SAME accumulated physical history.
All phase, maximum, HS and native inverse data are internally derived. -/
theorem rank_drop : Multiset.IsDershowitzMannaLT
    (rank (source h K hK hne)
      ((history h K hK hne).projection.hom.left.base ⁻¹' compact h K hK hne)
      ((history h K hK hne).singularModification.isProperMap.isCompact_preimage (compact_isCompact h K hK hne)))
    (rank Y (shadow h K) (shadow_isCompact h K hK)) := by
  have hOff : IsIsoOver (phaseSuffix h K hK hne).projection
      (originalSingularHSThreshold (oldSource h K hK hne)
        (originalStalkHS (oldSource h K hK hne) (maximumInOldSource h K hK hne)))ᶜ := by
    rw [← maximum_profile]
    exact phaseSuffix_off_threshold h K hK hne
  have hElim : ∀z, (phaseSuffix h K hK hne).projection.hom.left.base z∈oldShadow h K hK hne →
      z∈intrinsicSingularLocus (source h K hK hne).obj →
      originalStalkHS (source h K hK hne) z ≠
        originalStalkHS (oldSource h K hK hne) (maximumInOldSource h K hK hne) := by
    intro z _hzK hzS heq
    have heqH := heq.trans (maximum_profile h K hK hne).symm
    have hzH : z∈originalSingularHSThreshold (source h K hK hne) (profile h K hK hne) :=
      ⟨hzS,fun l=>(congrFun heqH l).ge⟩
    rw [phaseSuffix_threshold_empty] at hzH
    exact hzH
  have hd := OriginalNativeCompactShadowRank.rank_drop (phaseSuffix h K hK hne).projection
    (phaseSuffix_proper h K hK hne) (oldShadow h K hK hne) (oldShadow_isCompact h K hK hne)
    (maximumInOldSource h K hK hne) (maximum_mem_oldShadow h K hK hne)
    (maximum_singular h K hK hne) (maximum_maximal h K hK hne)
    (fun z _ _=>phaseSuffix_hs_nonincrease h K hK hne z) hOff hElim
  have hr : rank (oldSource h K hK hne) (oldShadow h K hK hne) (oldShadow_isCompact h K hK hne)=
      rank Y (shadow h K) (shadow_isCompact h K hK) :=
    rank_openImmersion (oldInclusion h K hK hne) (oldInclusion_open h K hK hne)
      (shadow h K) (shadow_isCompact h K hK) (oldShadow_retained h K hK hne)
  rw [hr] at hd
  have he := rank_eq_of_compact_set_eq
    ((history h K hK hne).singularModification.isProperMap.isCompact_preimage (compact_isCompact h K hK hne))
    ((phaseSuffix h K hK hne).singularModification.isProperMap.isCompact_preimage (oldShadow_isCompact h K hK hne))
    (new_shadow_eq h K hK hne)
  rw [he]
  exact hd

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSOuterSuccessor
