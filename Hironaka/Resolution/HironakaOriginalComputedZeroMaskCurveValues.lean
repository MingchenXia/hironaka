/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalAnyTestCurveValueNaturality
import Hironaka.Resolution.HironakaOriginalActualSmoothZeroMaskHistories
import Hironaka.Invariant.MaxLocusLocal
/-! Genuine nested-open ANYTEST full curve values and their original-input
consumer for the ACTUAL computed large zero-mask lower record. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalComputedZeroMaskCurveValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealTowerTransport RelativePrincipalizationSpan
  CoefficientIdealRestriction MaxLocusLocal HironakaOriginalAnyTestCurveValueNaturality
  HironakaOriginalActualSmoothZeroMaskHistories CanonicalCentres
  HomogenizedIdealAlong HomogenizedIdealAlongTower HomogenizedGlueingTower
  MarkedIdealOperationsAlong.MarkedIdeal ContactStageKept StepOneValue StepOneLowerDomain StepOneValueMasked StepOneRegime
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem actual_curve_full_value_restrict_iso {A B : CMfd.{u} n}
    (hn : 0<n) (k : ℕ) (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    (U : Opens X) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (Φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
    (Q : BlowupTower A B)
    (χ : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T U))
    (hi : IsTowerIso Φ Q (restrict U T) χ) (p : B)
    (hp : (χ p).val ∈ (geoTransformAlong M T).cosupp) :
    (invFamily hn (k+1)).inv (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → X) M)) Q p=
      (invFamily hn (k+1)).inv M T (χ p).val := by
  have hMU := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hTU := isGeoTestTower_restrict U hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hT
  have hpU : χ p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).cosupp := by
    rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
      hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent U T hT]
    exact hp
  exact (original_curve_any_test_full_value_isTowerIso hn k Φ _ hMU hi hTU p hpU).trans
    (original_curve_any_test_full_value_restrict hn k M hM U T hT (χ p) hp)

/-- Genuine nested-open domain/TEST/BOTHcosupport are constructed before
ALL positive-depth full original values on ANY actual TEST. -/
theorem original_curve_any_test_full_value_nested_opens (hn : 0<n)
    (P : MarkedIdeal n X) (hP : P.ideal.IsCoherent) {W V : Opens X} (hVW : V≤W)
    (hW : IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : W → X) P))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → X) P) (restrict W T)) :
    IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : V → X) P) ∧
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → X) P) (restrict V T) ∧
      ∀ p : openPreimage T V,
        (p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) P) (restrict V T)).cosupp ↔
          (⟨p.val,openPreimage_mono T hVW p.property⟩ : openPreimage T W) ∈
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) P) (restrict W T)).cosupp) ∧
        (p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) P) (restrict V T)).cosupp →
          ∀ k : ℕ,(invFamily hn (k+1)).inv (MarkedIdeal.pullback (Subtype.val : V → X) P) (restrict V T) p=
            (invFamily hn (k+1)).inv (MarkedIdeal.pullback (Subtype.val : W → X) P) (restrict W T)
              ⟨p.val,openPreimage_mono T hVW p.property⟩) := by
  have hD := InvDomainTowerAlong.isInvDomain_pullback_val (nestedOpens W V) hW
  have hDouble := isGeoTestTower_restrict (nestedOpens W V) hW.isWellFormed.isClosedSubmanifold_N
    hW.isWellFormed.isCoherent (restrict W T) hT
  have hi := (isTowerIso_restrict_nestedOpens (X := X) hVW T).symm
  have heq := pullback_symm_nestedOpensDiffeo (M := X) hP hVW
  have hV := InvDomainTowerAlong.isInvDomain_pullback (nestedOpensDiffeo (n := n) hVW).symm hD
  rw [heq] at hV
  have hTV := (IsTowerIso.isGeoTestTower_iff (nestedOpensDiffeo (n := n) hVW).symm
    hD.isWellFormed.isClosedSubmanifold_N hD.isWellFormed.isCoherent hi).mpr hDouble
  rw [heq] at hTV
  have hCos := IsTowerIso.cosupp_geoTransformAlong (nestedOpensDiffeo (n := n) hVW).symm
    hD.isWellFormed.isClosedSubmanifold_N hD.isWellFormed.isCoherent hi hDouble
  rw [heq] at hCos
  refine ⟨hV,hTV,fun p => ?_⟩
  have hpIff : (p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) P) (restrict V T)).cosupp ↔
      (⟨p.val,openPreimage_mono T hVW p.property⟩ : openPreimage T W) ∈
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) P) (restrict W T)).cosupp) := by
    rw [hCos,ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
      hW.isWellFormed.isClosedSubmanifold_N hW.isWellFormed.isCoherent (nestedOpens W V) (restrict W T) hT]
    rfl
  refine ⟨hpIff,fun hp k => ?_⟩
  have hVal := actual_curve_full_value_restrict_iso hn k _ hW (nestedOpens W V)
    (restrict W T) hT (nestedOpensDiffeo (n := n) hVW).symm (restrict V T) _ hi p (hpIff.mp hp)
  rw [heq] at hVal
  exact hVal

/-- ONLY original DOMAIN2/maxorder/ANYTEST zero-nonspecial data construct the
ACTUAL computed large mask BEFORE every smaller domain/TEST/full-value comparison. -/
theorem actual_original_computed_zero_mask_curve_full_values (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : HomogenizedIdealAlong.IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (y : Y)
    (hy : y ∈ (geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T y) (hl : level M T y=0) :
    let r := regimeRun (stepRegime M 0) T y
    let H := BlowupTowerSplit.head T r
    let S := BlowupTowerSplit.tail T r
    let W := lowerMask M 0 H (S.proj y)
    let J := lowerMarkedM M 0 H (S.proj y)
    ∃ hp : S.proj y ∈ W,
      IsInvDomain 1 J ∧ IsGeoTestTower J (restrict W S) ∧
      (⟨y,hp⟩ : openPreimage S W) ∈ (geoTransformAlong J (restrict W S)).cosupp ∧
      ∀ (V : Opens (BlowupTowerSplit.split T r).1) (_hVW : V≤W) (hv : S.proj y ∈ V),
        let A := contactMarkedKept M (tangentChoice M (H.proj (S.proj y))).2 H V
        IsInvDomain 1 A ∧ IsGeoTestTower A (restrict V S) ∧
        (⟨y,hv⟩ : openPreimage S V) ∈ (geoTransformAlong A (restrict V S)).cosupp ∧
        ∀ k : ℕ,(invFamily hn (k+1)).inv A (restrict V S) ⟨y,hv⟩=
          (invFamily hn (k+1)).inv J (restrict W S) ⟨y,hp⟩ := by
  obtain ⟨hp,hJ,hJT,_hCos,hyJ,_hNext⟩ :=
    actual_original_test_zero_mask_history (k := 0) hn M hM hmax T hT y hy hns hl
  refine ⟨hp,hJ,hJT,hyJ,?_⟩
  intro V hVW hv
  let r := regimeRun (stepRegime M 0) T y
  let H := BlowupTowerSplit.head T r
  let S := BlowupTowerSplit.tail T r
  let w := (tangentChoice M (H.proj (S.proj y))).2
  let P := withN (coeffMarkedAlong (geoTransformAlong (barMarked M) H))
    (strictAlong H (M.N ∩ {x | w x=0}))
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar := (he.2 T).1.mpr hT
  have hHead := ((BlowupTowerSplit.isGeoTestTower_iff_head_tail (barMarked M) T r).mp hBar).1
  have hP : P.ideal.IsCoherent := isCoherent_restrictedCoeff M hM.isWellFormed.isCoherent
    hM.isWellFormed.isClosedSubmanifold_N w H hHead
  have hNested := original_curve_any_test_full_value_nested_opens hn P hP hVW hJ S hJT
  obtain ⟨hV,hVT,hPoints⟩ := hNested
  have hPoint := hPoints (⟨y,hv⟩ : openPreimage S V)
  have hyV := hPoint.1.mpr hyJ
  exact ⟨hV,hVT,hyV,fun k => hPoint.2 hyV k⟩

end
end Hironaka.HironakaOriginalComputedZeroMaskCurveValues
