import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterSuccessor

/-! Actual initial lex bounds on the WHOLE old singular fibres of the
computed outer neighbourhood. Incoming native identifications give
leading-profile absence/equality, not final endpoint comparison.
Blueprint FIRST: original-native-hs-outer-initial-bound.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSOuterInitialBound
noncomputable section
open Hironaka SourceReducedComplexSpace
  OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11CompatibleAnalyticCover
  HironakaG11HSPhaseInduction OriginalNativeHSOuterHistory

abbrev factoryProfile (Y : SourceReducedComplexSpace) (L : Set Y.obj.left)
    (hL : IsCompact L) (hne : (L ∩ intrinsicSingularLocus Y.obj).Nonempty) : ℕ → ℕ :=
  originalStalkHS Y (OriginalNativeHSShadowPhaseFactory.maximum Y L hL hne).point

private def factoryToBarrier (Y : SourceReducedComplexSpace) (L : Set Y.obj.left)
    (hL : IsCompact L) (hne : (L ∩ intrinsicSingularLocus Y.obj).Nonempty) :
    OriginalNativeHSShadowPhaseFactory.base Y L hL hne ⟶
      OriginalNativeHSCompactShadowBarrier.nativeSource
        (OriginalNativeHSShadowPhaseFactory.maximum Y L hL hne) hL :=
  OriginalNativeHSShadowPhaseFactory.Branch.targetInclusion
      (OriginalNativeHSShadowPhaseFactory.selectedBranch Y L hL hne) ≫
    (OriginalNativeShadowFirstBlowup.target
      (OriginalNativeHSShadowPhaseFactory.selectedMaximum Y L hL hne)
      (OriginalNativeShadowFirstBlowup.barrierShadow_compact
        (OriginalNativeHSShadowPhaseFactory.maximum Y L hL hne) hL)).inclusion

private theorem factoryToBarrier_open (Y : SourceReducedComplexSpace) (L : Set Y.obj.left)
    (hL : IsCompact L) (hne : (L ∩ intrinsicSingularLocus Y.obj).Nonempty) :
    LocallyRingedSpace.IsOpenImmersion (factoryToBarrier Y L hL hne).hom.left :=
  @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    (OriginalNativeHSShadowPhaseFactory.Branch.targetInclusion
      (OriginalNativeHSShadowPhaseFactory.selectedBranch Y L hL hne)).hom.left
    (OriginalNativeHSShadowPhaseFactory.Branch.targetInclusion_isOpenImmersion _)
    (OriginalNativeShadowFirstBlowup.target
      (OriginalNativeHSShadowPhaseFactory.selectedMaximum Y L hL hne)
      (OriginalNativeShadowFirstBlowup.barrierShadow_compact
        (OriginalNativeHSShadowPhaseFactory.maximum Y L hL hne) hL)).inclusion.hom.left
    (OriginalNativeShadowFirstBlowup.target
      (OriginalNativeHSShadowPhaseFactory.selectedMaximum Y L hL hne)
      (OriginalNativeShadowFirstBlowup.barrierShadow_compact
        (OriginalNativeHSShadowPhaseFactory.maximum Y L hL hne) hL)).inclusion_isOpenImmersion

/-- The actual factory base has the SAME leading bound at EVERY singular point. -/
theorem factory_base_bound (Y : SourceReducedComplexSpace) (L : Set Y.obj.left)
    (hL : IsCompact L) (hne : (L ∩ intrinsicSingularLocus Y.obj).Nonempty)
    (y : (OriginalNativeHSShadowPhaseFactory.base Y L hL hne).obj.left)
    (hy : y ∈ intrinsicSingularLocus (OriginalNativeHSShadowPhaseFactory.base Y L hL hne).obj) :
    toLex (originalStalkHS (OriginalNativeHSShadowPhaseFactory.base Y L hL hne) y) ≤
      toLex (factoryProfile Y L hL hne) := by
  have hs := preimage_intrinsicSingularLocus_of_isOpenImmersion
    (factoryToBarrier Y L hL hne) (factoryToBarrier_open Y L hL hne)
  have hsing := (Set.ext_iff.mp hs y).mpr hy
  have hb := OriginalNativeHSCompactShadowBarrier.native_bound
    (OriginalNativeHSShadowPhaseFactory.maximum Y L hL hne) hL
    ((factoryToBarrier Y L hL hne).hom.left.base y) hsing
  rw [originalStalkHS_openImmersion (factoryToBarrier Y L hL hne)
    (factoryToBarrier_open Y L hL hne) y] at hb
  exact hb

/-- The bound on the image is on singular points, including those outside L. -/
theorem factory_range_bound (Y : SourceReducedComplexSpace) (L : Set Y.obj.left)
    (hL : IsCompact L) (hne : (L ∩ intrinsicSingularLocus Y.obj).Nonempty)
    (y : Y.obj.left) (hy : y ∈ intrinsicSingularLocus Y.obj)
    (hr : y ∈ range (OriginalNativeHSShadowPhaseFactory.baseInclusion Y L hL hne).hom.left.base) :
    toLex (originalStalkHS Y y) ≤ toLex (factoryProfile Y L hL hne) := by
  obtain ⟨z, rfl⟩ := hr
  have hj := OriginalNativeHSShadowPhaseFactory.baseInclusion_isOpenImmersion Y L hL hne
  have hz := (Set.ext_iff.mp (preimage_intrinsicSingularLocus_of_isOpenImmersion
    (OriginalNativeHSShadowPhaseFactory.baseInclusion Y L hL hne) hj) z).mp hy
  rw [originalStalkHS_openImmersion
    (OriginalNativeHSShadowPhaseFactory.baseInclusion Y L hL hne) hj z]
  exact factory_base_bound Y L hL hne z hz

section History
variable {B Y : SourceReducedComplexSpace} (h : PhysicalHistory B Y) (K : Set B.obj.left)
  (hK : IsCompact K)
  (hne : (intrinsicSingularLocus Y.obj ∩ OriginalNativeHSOuterSuccessor.shadow h K).Nonempty)

include hne in
private theorem shadowNonempty :
    (OriginalNativeHSOuterSuccessor.shadow h K ∩ intrinsicSingularLocus Y.obj).Nonempty := by
  simpa only [inter_comm] using hne

abbrev profile : ℕ → ℕ := factoryProfile Y (OriginalNativeHSOuterSuccessor.shadow h K)
  (OriginalNativeHSOuterSuccessor.shadow_isCompact h K hK) (shadowNonempty h K hne)

/-- WHOLE old singular fibres over the CLOSURE of the actual computed neighbourhood. -/
theorem old_fibre_closure_bound (y : Y.obj.left) (hy : y ∈ intrinsicSingularLocus Y.obj)
    (hV : h.projection.hom.left.base y ∈ closure
      ((OriginalNativeHSOuterSuccessor.neighbourhood h K hK hne).openSet : Set B.obj.left)) :
    toLex (originalStalkHS Y y) ≤ toLex (profile h K hK hne) := by
  apply factory_range_bound Y (OriginalNativeHSOuterSuccessor.shadow h K)
    (OriginalNativeHSOuterSuccessor.shadow_isCompact h K hK) (shadowNonempty h K hne) y hy
  exact OriginalNativePhysicalHistoryResaturation.closure_preimage_subset h
    (OriginalNativeHSShadowPhaseFactory.baseInclusion Y (OriginalNativeHSOuterSuccessor.shadow h K)
      (OriginalNativeHSOuterSuccessor.shadow_isCompact h K hK) (shadowNonempty h K hne))
    (OriginalNativeHSShadowPhaseFactory.baseInclusion_isOpenImmersion Y
      (OriginalNativeHSOuterSuccessor.shadow h K)
      (OriginalNativeHSOuterSuccessor.shadow_isCompact h K hK) (shadowNonempty h K hne))
    K hK (OriginalNativeHSShadowPhaseFactory.compact_retained Y
      (OriginalNativeHSOuterSuccessor.shadow h K)
      (OriginalNativeHSOuterSuccessor.shadow_isCompact h K hK) (shadowNonempty h K hne)) hV

theorem old_fibre_bound (y : Y.obj.left) (hy : y ∈ intrinsicSingularLocus Y.obj)
    (hV : h.projection.hom.left.base y ∈
      (OriginalNativeHSOuterSuccessor.neighbourhood h K hK hne).openSet) :
    toLex (originalStalkHS Y y) ≤ toLex (profile h K hK hne) :=
  old_fibre_closure_bound h K hK hne y hy (subset_closure hV)

def boundRegion {Z : SourceReducedComplexSpace} (a : Z ⟶ Y) : Set Z.obj.left :=
  (a ≫ h.projection).hom.left.base ⁻¹'
    ((OriginalNativeHSOuterSuccessor.neighbourhood h K hK hne).openSet : Set B.obj.left)

end History

section Incoming
variable {B₁ B₂ Y₁ Y₂ Z : SourceReducedComplexSpace}
  (h₁ : PhysicalHistory B₁ Y₁) (K₁ : Set B₁.obj.left) (hc₁ : IsCompact K₁)
  (hn₁ : (intrinsicSingularLocus Y₁.obj ∩ OriginalNativeHSOuterSuccessor.shadow h₁ K₁).Nonempty)
  (h₂ : PhysicalHistory B₂ Y₂) (K₂ : Set B₂.obj.left) (hc₂ : IsCompact K₂)
  (hn₂ : (intrinsicSingularLocus Y₂.obj ∩ OriginalNativeHSOuterSuccessor.shadow h₂ K₂).Nonempty)
  (a₁ : Z ⟶ Y₁) (ha₁ : LocallyRingedSpace.IsOpenImmersion a₁.hom.left)
  (a₂ : Z ⟶ Y₂) (ha₂ : LocallyRingedSpace.IsOpenImmersion a₂.hom.left)

include ha₁ ha₂ in
theorem threshold_profile_le (z : Z.obj.left)
    (hz : a₁.hom.left.base z ∈ originalSingularHSThreshold Y₁ (profile h₁ K₁ hc₁ hn₁))
    (hV : z ∈ boundRegion h₂ K₂ hc₂ hn₂ a₂) :
    toLex (profile h₁ K₁ hc₁ hn₁) ≤ toLex (profile h₂ K₂ hc₂ hn₂) := by
  have hsingZ := (Set.ext_iff.mp
    (preimage_intrinsicSingularLocus_of_isOpenImmersion a₁ ha₁) z).mp hz.1
  have hsing₂ := (Set.ext_iff.mp
    (preimage_intrinsicSingularLocus_of_isOpenImmersion a₂ ha₂) z).mpr hsingZ
  calc
    _ ≤ toLex (originalStalkHS Y₁ (a₁.hom.left.base z)) := Pi.toLex_monotone hz.2
    _ = toLex (originalStalkHS Y₂ (a₂.hom.left.base z)) := congrArg toLex
      ((originalStalkHS_openImmersion a₁ ha₁ z).trans
        (originalStalkHS_openImmersion a₂ ha₂ z).symm)
    _ ≤ _ := old_fibre_bound h₂ K₂ hc₂ hn₂ (a₂.hom.left.base z) hsing₂ hV

include ha₁ ha₂ in
theorem higher_threshold_absent
    (hlt : toLex (profile h₂ K₂ hc₂ hn₂) < toLex (profile h₁ K₁ hc₁ hn₁)) :
    (a₁.hom.left.base ⁻¹' originalSingularHSThreshold Y₁ (profile h₁ K₁ hc₁ hn₁)) ∩
      boundRegion h₂ K₂ hc₂ hn₂ a₂ = ∅ := by
  apply Set.eq_empty_of_subset_empty
  intro z hz
  exact (not_le_of_gt hlt)
    (threshold_profile_le h₁ K₁ hc₁ hn₁ h₂ K₂ hc₂ hn₂ a₁ ha₁ a₂ ha₂ z hz.1 hz.2)

end Incoming

section CommonFibre
variable {B Y Z X : SourceReducedComplexSpace}
  (h : PhysicalHistory B Y) (K : Set B.obj.left) (hc : IsCompact K)
  (hn : (intrinsicSingularLocus Y.obj ∩ OriginalNativeHSOuterSuccessor.shadow h K).Nonempty)
  (a : Z ⟶ Y) (b : B ⟶ X) (hb : LocallyRingedSpace.IsOpenImmersion b.hom.left)
  (p : Z ⟶ X) (hsq : a ≫ h.projection ≫ b = p)
  (L : Set X.obj.left) (hL : L ⊆ b.hom.left.base '' K)

include hb hsq hL in
theorem common_fibre_mem_boundRegion (z : Z.obj.left) (hz : p.hom.left.base z ∈ L) :
    z ∈ boundRegion h K hc hn a := by
  obtain ⟨k, hk, heq⟩ := hL hz
  have hp : b.hom.left.base (h.projection.hom.left.base (a.hom.left.base z)) =
      p.hom.left.base z := congrArg (fun f : Z ⟶ X => f.hom.left.base z) hsq
  have he : h.projection.hom.left.base (a.hom.left.base z) = k :=
    hb.base_open.isEmbedding.injective (hp.trans heq.symm)
  change h.projection.hom.left.base (a.hom.left.base z) ∈
    (OriginalNativeHSOuterSuccessor.neighbourhood h K hc hn).openSet
  rw [he]
  exact (OriginalNativeHSOuterSuccessor.neighbourhood h K hc hn).contains hk

end CommonFibre

section TwoFibres
variable {B₁ B₂ Y₁ Y₂ Z X : SourceReducedComplexSpace}
  (h₁ : PhysicalHistory B₁ Y₁) (K₁ : Set B₁.obj.left) (hc₁ : IsCompact K₁)
  (hn₁ : (intrinsicSingularLocus Y₁.obj ∩ OriginalNativeHSOuterSuccessor.shadow h₁ K₁).Nonempty)
  (h₂ : PhysicalHistory B₂ Y₂) (K₂ : Set B₂.obj.left) (hc₂ : IsCompact K₂)
  (hn₂ : (intrinsicSingularLocus Y₂.obj ∩ OriginalNativeHSOuterSuccessor.shadow h₂ K₂).Nonempty)
  (a₁ : Z ⟶ Y₁) (ha₁ : LocallyRingedSpace.IsOpenImmersion a₁.hom.left)
  (a₂ : Z ⟶ Y₂) (ha₂ : LocallyRingedSpace.IsOpenImmersion a₂.hom.left)
  (b₁ : B₁ ⟶ X) (hb₁ : LocallyRingedSpace.IsOpenImmersion b₁.hom.left)
  (b₂ : B₂ ⟶ X) (hb₂ : LocallyRingedSpace.IsOpenImmersion b₂.hom.left)
  (p : Z ⟶ X) (hsq₁ : a₁ ≫ h₁.projection ≫ b₁ = p)
  (hsq₂ : a₂ ≫ h₂.projection ≫ b₂ = p)
  (L : Set X.obj.left) (hL₁ : L ⊆ b₁.hom.left.base '' K₁)
  (hL₂ : L ⊆ b₂.hom.left.base '' K₂)

include ha₁ ha₂ hb₁ hb₂ hsq₁ hsq₂ hL₁ hL₂ in
/-- An incoming common fibre sees only equal realized actual leading profiles. -/
theorem profiles_eq_of_both_thresholds_meet
    (he₁ : (p.hom.left.base ⁻¹' L ∩ a₁.hom.left.base ⁻¹'
      originalSingularHSThreshold Y₁ (profile h₁ K₁ hc₁ hn₁)).Nonempty)
    (he₂ : (p.hom.left.base ⁻¹' L ∩ a₂.hom.left.base ⁻¹'
      originalSingularHSThreshold Y₂ (profile h₂ K₂ hc₂ hn₂)).Nonempty) :
    profile h₁ K₁ hc₁ hn₁ = profile h₂ K₂ hc₂ hn₂ := by
  obtain ⟨z₁, hz₁, ht₁⟩ := he₁
  obtain ⟨z₂, hz₂, ht₂⟩ := he₂
  have hle := threshold_profile_le h₁ K₁ hc₁ hn₁ h₂ K₂ hc₂ hn₂ a₁ ha₁ a₂ ha₂ z₁ ht₁
    (common_fibre_mem_boundRegion h₂ K₂ hc₂ hn₂ a₂ b₂ hb₂ p hsq₂ L hL₂ z₁ hz₁)
  have hge := threshold_profile_le h₂ K₂ hc₂ hn₂ h₁ K₁ hc₁ hn₁ a₂ ha₂ a₁ ha₁ z₂ ht₂
    (common_fibre_mem_boundRegion h₁ K₁ hc₁ hn₁ a₁ b₁ hb₁ p hsq₁ L hL₁ z₂ hz₂)
  exact congrArg ofLex (le_antisymm hle hge)

end TwoFibres
end
end Hironaka.Analytic.Unibranch.OriginalNativeHSOuterInitialBound
