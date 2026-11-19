import Hironaka.Resolution.HironakaG8RestartedPrincipalProvider
import Hironaka.Resolution.HironakaG8RestartedEmptyEpoch

/-! The actual lower native provider and the literal empty-prefix clock
combine on the same returned source and target opens. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8ActualPrincipalRestart
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  NormalCrossings HironakaEmbeddedAnalytic ResolutionInvariantSpec CanonicalCentres ResolutionDriver
  HironakaHolomorphicJetChartInvariance HomogenizedIdealAlong
  HironakaG8NativePhaseCertificate HironakaG8RestartedPrincipalProvider HironakaG8RestartedEmptyEpoch
  HironakaOriginalEmptyHeadPrefix HironakaActualOpenEmbeddingVanishingIdeal

open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X D : CMfd.{0} (n+1)}

private abbrev whole (W : Set X) (d : ℕ) : MarkedIdeal (n+1) X :=
  ⟨univ,[],vanishingIdeal (n := n+1) W,d⟩

private theorem source_domain_of_empty_whole
    (W : Set X) (hW : IsClosed W) (H : BlowupTower X D) (he : IsEmptyTower H)
    (q : ℕ) (hQ : IsInvDomain (n+1) (whole (strictTransform (n+1) H.proj W) q)) :
    IsInvDomain (n+1) (whole W 1) := by
  let W' := strictTransform (n+1) H.proj W
  have hA : IsInvDomain (n+1) (whole W' 1) :=
    ⟨⟨hQ.isWellFormed.1,hQ.isWellFormed.2,hQ.isWellFormed.3,hQ.isWellFormed.4⟩,
      hQ.dimLE,le_rfl,hQ.isNonzeroAlongAt⟩
  obtain ⟨β,hβ⟩ := exists_empty_tower_projection H he
  have hFun : (β : D → X) = H.proj := funext hβ
  have hExc : exceptionalLocus (n+1) β = ∅ := by
    ext z
    simp only [mem_empty_iff_false,iff_false]
    exact MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
      β.contMDiff β.symm.contMDiff β.apply_symm_apply β.symm_apply_apply z
  have hStrict : W' = β ⁻¹' W := by
    change strictTransform (n+1) H.proj W = _
    rw [← hFun,strictTransform,hExc,sdiff_empty,(hW.preimage β.continuous).closure_eq]
  have hBack : β.symm ⁻¹' W' = W := by
    rw [hStrict]
    ext x
    change β (β.symm x) ∈ W ↔ x ∈ W
    rw [β.apply_symm_apply]
  have hPull : MarkedIdeal.pullback β.symm (whole W' 1) = whole W 1 := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ rfl ?_ rfl
    · exact preimage_univ
    · change GermIdeal.pullback (m := n+1) β.symm (vanishingIdeal (n := n+1) W') =
        vanishingIdeal (n := n+1) W
      rw [pullback_vanishingIdeal_of_biholomorphism,hBack]
  have h := InvDomainTowerAlong.isInvDomain_pullback β.symm hA
  rwa [hPull] at h

/-- The principal lower provider returns the literal smaller source open
and its physical target preimage. Every actual canonical lower tail on
that record agrees with the original history on the restricted higher
prefix. No separate lower order bound, domain, or comparison ideal is
needed. -/
theorem exists_actual_principal_restart_on_missed_phase
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    {H : ℕ → ℕ} (T : BlowupTower X D) (hPhase : ActualNativePhase W [] H T)
    (O : Opens X)
    (hSmaller : ∀ x ∈ (O : Set X) ∩ singularSet (n := n+1) W,
      toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) W) x) < toLex H)
    (a : openPreimage T O) :
    let U := openPreimage T O
    let B := CMfd.of (n := n+1) U
    let W' := (Subtype.val : U → D) ⁻¹' strictTransform (n+1) T.proj W
    a ∈ singularSet (n := n+1) W' →
    NonzeroPrincipalAt (X := B) (vanishingIdeal (n := n+1) W') a →
    ∃ (L : Opens (CMfd.of (n := n+1) O)) (haL : a ∈ openPreimage (restrict O T) L) (q : ℕ),
      let V := openPreimage (restrict O T) L
      let D' := CMfd.of (n := n+1) V
      let X' := CMfd.of (n := n+1) L
      let P := restrict L (restrict O T)
      let W₀ := (fun z : L => (z.val : X)) ⁻¹' W
      let W'' := (Subtype.val : V → B) ⁻¹' W'
      let Q : MarkedIdeal (n+1) D' := whole W'' q
      let M : MarkedIdeal (n+1) X' := whole W₀ 1
      let R := canonicalInvariant (n+1)
      IsEmptyTower P ∧ IsInvDomain (n+1) Q ∧ IsMaximalOrderAlong Q.N Q.ideal q ∧
      (⟨a,haL⟩ : V) ∈ Q.cosupp ∧
      ∀ {Y : CMfd.{0} (n+1)} (S : BlowupTower D' Y), IsCanonical Q (R.inv Q) S →
        IsCanonical M (R.inv M) (P.append S) ∧
        (∀ y ∈ (geoTransformAlong Q S).cosupp,
          R.inv M (P.append S) y = emptyPrefixShift n T.length (R.inv Q S y)) ∧
        ((geoTransformAlong Q S).cosupp.Nonempty →
          maxLocus (R.inv M (P.append S)) (geoTransformAlong M (P.append S)).cosupp =
            maxLocus (R.inv Q S) (geoTransformAlong Q S).cosupp) := by
  dsimp only
  intro ha hp
  obtain ⟨he,V,haV,q,hDom,hCap,hAnchor,_hHS,_hSing,L,hOpen⟩ :=
    exists_principal_lower_record_after_actual_higher_phase W hW T hPhase O hSmaller a ha hp
  subst V
  let Hₒ := restrict O T
  let B := CMfd.of (n := n+1) (openPreimage T O)
  let V := openPreimage Hₒ L
  let P := restrict L Hₒ
  let W₁ := (Subtype.val : O → X) ⁻¹' W
  let W₀ := (Subtype.val : L → CMfd.of (n := n+1) O) ⁻¹' W₁
  let W' := (Subtype.val : openPreimage T O → D) ⁻¹' strictTransform (n+1) T.proj W
  let W'' := (Subtype.val : V → B) ⁻¹' W'
  have hClosed : IsClosed W₀ := (hW.isClosed.preimage continuous_subtype_val).preimage continuous_subtype_val
  have hTrace₁ : strictTransform (n+1) Hₒ.proj W₁ = W' :=
    HironakaNormalCrossingsOpenRestrictionSeparation.strictTransform_restricted_tower O T W
  have hTrace : strictTransform (n+1) P.proj W₀ = W'' := by
    have hr := HironakaNormalCrossingsOpenRestrictionSeparation.strictTransform_restricted_tower L Hₒ W₁
    rw [hTrace₁] at hr
    exact hr
  have hAvoid := ContactLowerValue.centresAvoid_of_isEmptyTower L Hₒ he
  have hEmpty : IsEmptyTower P := (RestrictEmptyTower.isEmptyTower_restrict_iff L Hₒ).mpr hAvoid
  have hM : IsInvDomain (n+1) (whole (X := CMfd.of (n := n+1) L) W₀ 1) := by
    apply source_domain_of_empty_whole W₀ hClosed P hEmpty q
    rw [hTrace]
    exact hDom
  refine ⟨L,haV,q,hEmpty,hDom,hCap,hAnchor,?_⟩
  intro Y S hCan
  have hResult := restarted_native_epoch_on_missed_window W₁ (hW.isClosed.preimage continuous_subtype_val)
    Hₒ L hAvoid q S
  dsimp only at hResult
  rw [hTrace₁,length_restrict] at hResult
  obtain ⟨hCanOld,_hFresh,hValues,hMax⟩ := hResult hM hDom hCap hCan
  exact ⟨hCanOld,hValues,hMax⟩

end
end Hironaka.HironakaG8ActualPrincipalRestart
