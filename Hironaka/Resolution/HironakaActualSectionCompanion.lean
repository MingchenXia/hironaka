import Hironaka.Resolution.HironakaActualSectionRestrictedIdeals
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSectionCompanion
noncomputable section
open Hironaka.HolomorphicIdealSheaves MarkedIdeals
  HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  HironakaActualSectionRestrictedIdeals HironakaActualSectionInitialValues
  MonomialPartAlong NonmonomialOrderLocal DivisorExponentAlong
  CanonicalCentres BlowupTowers HironakaSmoothSubmersionCoefficientIdeals
  CompanionRebase CompanionReductionAlong
variable {n : ℕ} {U : TopologicalSpace.Opens (ComplexModel n)}

private theorem projection_section (x : U) : projection U (zeroSection U x)=x := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x

theorem nmOrd_section_eq (A : Set U) (E : List (Set U))
    (J : GermIdeal (n+1) (productOpen U))
    (hJ : ∀z g,J.mem z g → HolomorphicAt (n+1) g z) (d : ℕ) (x : U) :
    nmOrd (M := CMfd.of (n := n+1) (productOpen U))
      (⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩ : MarkedIdeal (n+1) (productOpen U)) (zeroSection U x)=
    nmOrd (M := CMfd.of (n := n) U)
      (⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeal n U) x := by
  unfold nmOrd
  apply congrArg sInf
  ext q
  apply not_congr
  change zeroSection U x∈GermIdealOrder.cosupport (n+1) (liftedCarrier A)
      (nonmonomialPartAlong (n+1) (liftedCarrier A) J (E.map (projection U ⁻¹' ·))) (q+1) ↔ _
  rw [source_cosupport_eq_lifted A
    (nonmonomialPartAlong (n+1) (liftedCarrier A) J (E.map (projection U ⁻¹' ·)))
    (fun _ _ hg => hg.1) (q+1),pullback_section_nonmonomialPartAlong A E J hJ]
  change (projection U (zeroSection U x)∈_ ∧ _=0) ↔ _
  simp only [projection_section]
  simp [zeroSection]

open ResolutionInvariantSpec (IsInvDomain)
open IdealWeightPowers HironakaSmoothSubmersionRelativeRestriction GermIdealPullbackCalculus RelativePrincipalizationSpan

theorem markedPullback_section_companionOf (q : ℕ) (A : Set U) (E : List (Set U))
    (J : GermIdeal (n+1) (productOpen U)) (d o : ℕ)
    (hM : IsInvDomain q
      (⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩ : MarkedIdeal (n+1) (productOpen U))) :
    markedPullback (m := n) (zeroSection U)
      (companionOf (n+1) (M := CMfd.of (n := n+1) (productOpen U))
        (⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩ : MarkedIdeal (n+1) (productOpen U)) o)=
    companionOf n (M := CMfd.of (n := n) U)
      (⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeal n U) o := by
  have hm:=hM.isWellFormed
  have hJ:=hm.isCoherent
  have hJhol : ∀z g,J.mem z g → HolomorphicAt (n+1) g z :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ hg
  have hmon:=isCoherent_monomialPartAlong (Nat.succ_pos n) hm.isClosedSubmanifold_N
    hm.isSNCDivisor hm.isTransverse hJ hM.isNonzeroAlongAt
  have hnon:=isCoherent_nonmonomialPartAlong (Nat.succ_pos n) hm.isClosedSubmanifold_N
    hm.isSNCDivisor hm.isTransverse hJ hM.isNonzeroAlongAt
  have hpre : zeroSection U ⁻¹' liftedCarrier A=A := by
    ext y
    change (projection U (zeroSection U y)∈A ∧ _=0) ↔ y∈A
    simp only [projection_section]
    simp [zeroSection]
  have hE : (E.map (projection U ⁻¹' ·)).map (zeroSection U ⁻¹' ·)=E := by
    rw [List.map_map]
    have hf : (fun H : Set U => zeroSection U ⁻¹' (projection U ⁻¹' H))=id := by
      funext H
      ext y
      simp only [Set.mem_preimage,projection_section,id_eq]
    change List.map (fun H => zeroSection U ⁻¹' (projection U ⁻¹' H)) E=E
    rw [hf,List.map_id]
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · simpa only [markedPullback,companionOf,companionAlong_N] using hpre
  · simpa only [markedPullback,companionOf,companionAlong_E] using hE
  · dsimp only [markedPullback,companionOf]
    rw [companionAlong_ideal,companionAlong_ideal]
    split_ifs
    · rw [pullback_sumIdeal_dimensions (zeroSection_contMDiff U)
        (isCoherent_idealPow hnon _) (isCoherent_idealPow hmon _),
        HironakaActualNonregularCoefficientNaturality.pullback_idealPow (zeroSection_contMDiff U)
          (fun hg => GermIdeal.IsCoherent.holomorphicAt_mem hnon hg),
        HironakaActualNonregularCoefficientNaturality.pullback_idealPow (zeroSection_contMDiff U)
          (fun hg => GermIdeal.IsCoherent.holomorphicAt_mem hmon hg),
        pullback_section_nonmonomialPartAlong A E J hJhol,
        pullback_section_monomialPartAlong A E J hJhol]
    · exact pullback_section_nonmonomialPartAlong A E J hJhol
  · dsimp only [markedPullback,companionOf]
    rw [companionAlong_d,companionAlong_d]

end
end Hironaka.HironakaActualSectionCompanion
