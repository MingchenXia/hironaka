/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalBoundTwoStepOneLocality
import Hironaka.Resolution.HironakaOriginalCurveLocalReferenceComparison
/-! Genuine independently local DOMAIN2/max/TEST, rather than false global
reference hypotheses, supply whole unchanged original StepOne comparison. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalBoundTwoStepOneLocalReferenceComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail CanonicalCentres InvDomainTowerAlong
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MaxLocusLocal HomogenizedIdealAlong HironakaOriginalBoundTwoStepOneLocality
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Genuine successor-mark open cosupport emptiness, rather than an assumed
numeric upper bound, transports the actual maximal-order hypothesis. -/
private theorem actual_maximal_order_open (J : MarkedIdeal n X)
    (hC : J.ideal.IsCoherent) (hmax : IsMaximalOrderAlong J.N J.ideal J.d) (U : Opens X) :
    IsMaximalOrderAlong (MarkedIdeal.pullback (Subtype.val : U → X) J).N
      (MarkedIdeal.pullback (Subtype.val : U → X) J).ideal
      (MarkedIdeal.pullback (Subtype.val : U → X) J).d := by
  let Jplus : MarkedIdeal n X := ⟨J.N,J.E,J.ideal,J.d+1⟩
  have heq := cosupp_pullback_val Jplus
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hC hg) U
  intro x hx
  apply hmax x.val
  change x∈(MarkedIdeal.pullback (Subtype.val : U → X) Jplus).cosupp at hx
  rw [heq] at hx
  exact hx

/-- Genuine local DOMAIN and TEST are transported through real nested
histories before every whole cosupport and numerical StepOne comparison. -/
theorem local_step_one_nested_open (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.ideal.IsCoherent) {W V : Opens X} (hVW : V≤W)
    (hDom : IsInvDomain 2 (MarkedIdeal.pullback (Subtype.val : W → X) M))
    (hmax : IsMaximalOrderAlong (MarkedIdeal.pullback (Subtype.val : W → X) M).N
      (MarkedIdeal.pullback (Subtype.val : W → X) M).ideal
      (MarkedIdeal.pullback (Subtype.val : W → X) M).d)
    (T : BlowupTower X Y)
    (hTest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → X) M) (restrict W T)) :
    IsInvDomain 2 (MarkedIdeal.pullback (Subtype.val : V → X) M) ∧
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T) ∧
      (∀ p : openPreimage T V,
        p∈(geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T)).cosupp ↔
          (⟨p.val,openPreimage_mono T hVW p.property⟩ : openPreimage T W)∈
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) M) (restrict W T)).cosupp) ∧
      ∀ p : openPreimage T V,
        p∈(geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T)).cosupp →
        ∀ k : ℕ,Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T) p=
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) (MarkedIdeal.pullback (Subtype.val : W → X) M) (restrict W T)
            ⟨p.val,openPreimage_mono T hVW p.property⟩ := by
  have hDom' := isInvDomain_pullback_val (nestedOpens W V) hDom
  have hMax' := actual_maximal_order_open (X := CMfd.of (n := n) W) _ hDom.isWellFormed.isCoherent hmax (nestedOpens W V)
  have hTest' := isGeoTestTower_restrict (nestedOpens W V) hDom.isWellFormed.isClosedSubmanifold_N
    hDom.isWellFormed.isCoherent (restrict W T) hTest
  have hiso := (isTowerIso_restrict_nestedOpens (X := X) hVW T).symm
  have heq := pullback_symm_nestedOpensDiffeo (M := X) hM hVW
  have hDomV := isInvDomain_pullback (nestedOpensDiffeo (n := n) hVW).symm hDom'
  rw [heq] at hDomV
  have hTestV := (IsTowerIso.isGeoTestTower_iff (nestedOpensDiffeo (n := n) hVW).symm
    hDom'.isWellFormed.isClosedSubmanifold_N hDom'.isWellFormed.isCoherent hiso).mpr hTest'
  rw [heq] at hTestV
  have hCos := IsTowerIso.cosupp_geoTransformAlong (nestedOpensDiffeo (n := n) hVW).symm
    hDom'.isWellFormed.isClosedSubmanifold_N hDom'.isWellFormed.isCoherent hiso hTest'
  rw [heq] at hCos
  have hCos' := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hDom.isWellFormed.isClosedSubmanifold_N hDom.isWellFormed.isCoherent
    (nestedOpens W V) (restrict W T) hTest
  refine ⟨hDomV,hTestV,?_,?_⟩
  · intro p
    rw [hCos,mem_preimage,hCos',mem_preimage]
    rfl
  · intro p hp k
    have hp' := hp
    rw [hCos,mem_preimage] at hp'
    have hv := step_one_value_of_towerIso hn k _ hDom' hMax' _ hTest' hiso p hp'
    rw [heq] at hv
    have hp'' := hp'
    rw [hCos',mem_preimage] at hp''
    exact hv.trans (step_one_value_restrict_open hn k _ hDom hmax (restrict W T) hTest (nestedOpens W V) _ hp'')

/-- The real intersection compares independently local references; there
is no global DOMAIN2/maximal-order, canonicality or numerical certificate premise. -/
theorem local_step_one_two_opens (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.ideal.IsCoherent) (U V : Opens X)
    (hU : IsInvDomain 2 (MarkedIdeal.pullback (Subtype.val : U → X) M))
    (hV : IsInvDomain 2 (MarkedIdeal.pullback (Subtype.val : V → X) M))
    (hMaxU : IsMaximalOrderAlong (MarkedIdeal.pullback (Subtype.val : U → X) M).N
      (MarkedIdeal.pullback (Subtype.val : U → X) M).ideal
      (MarkedIdeal.pullback (Subtype.val : U → X) M).d)
    (hMaxV : IsMaximalOrderAlong (MarkedIdeal.pullback (Subtype.val : V → X) M).N
      (MarkedIdeal.pullback (Subtype.val : V → X) M).ideal
      (MarkedIdeal.pullback (Subtype.val : V → X) M).d)
    (T : BlowupTower X Y)
    (hTU : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T))
    (hTV : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T))
    (z : Y) (hzU : T.proj z∈U) (hzV : T.proj z∈V) :
    ((⟨z,hzU⟩ : openPreimage T U)∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).cosupp ↔
        (⟨z,hzV⟩ : openPreimage T V)∈
          (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T)).cosupp) ∧
      ((⟨z,hzU⟩ : openPreimage T U)∈
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).cosupp →
        ∀ k : ℕ,Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T) ⟨z,hzU⟩=
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T) ⟨z,hzV⟩) := by
  obtain ⟨_,_,hCosU,hValU⟩ := local_step_one_nested_open hn M hM (W := U) (V := U⊓V) inf_le_left hU hMaxU T hTU
  obtain ⟨_,_,hCosV,hValV⟩ := local_step_one_nested_open hn M hM (W := V) (V := U⊓V) inf_le_right hV hMaxV T hTV
  let q : openPreimage T (U⊓V) := ⟨z,⟨hzU,hzV⟩⟩
  refine ⟨(hCosU q).symm.trans (hCosV q),?_⟩
  intro hz k
  have hq := (hCosU q).mpr hz
  exact (hValU q hq k).symm.trans (hValV q hq k)

end
end Hironaka.HironakaOriginalBoundTwoStepOneLocalReferenceComparison
