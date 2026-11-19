/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCurveFullLocality
/-! Genuine local curve domains, rather than a false global reference
domain, supply complete noncanonical two-open original FULL comparison. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCurveLocalReferenceComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail CanonicalCentres InvDomainTowerAlong
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MaxLocusLocal HironakaOriginalCurveFullLocality
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Genuine local DOMAIN and TEST are transported through real nested
histories before every whole cosupport and numerical FULL comparison. -/
theorem local_curve_full_nested_open (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.ideal.IsCoherent) {W V : Opens X} (hVW : V≤W)
    (hDom : IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : W → X) M))
    (T : BlowupTower X Y)
    (hTest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → X) M) (restrict W T)) :
    IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : V → X) M) ∧
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T) ∧
      (∀ p : openPreimage T V,
        p∈(geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T)).cosupp ↔
          (⟨p.val,openPreimage_mono T hVW p.property⟩ : openPreimage T W)∈
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) M) (restrict W T)).cosupp) ∧
      ∀ p : openPreimage T V,
        p∈(geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T)).cosupp →
        ∀ k : ℕ,(invFamily hn (k+1)).inv (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T) p=
          (invFamily hn (k+1)).inv (MarkedIdeal.pullback (Subtype.val : W → X) M) (restrict W T)
            ⟨p.val,openPreimage_mono T hVW p.property⟩ := by
  have hDom' := isInvDomain_pullback_val (nestedOpens W V) hDom
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
    have hv := curve_full_value_of_towerIso hn k _ hDom' _ hTest' hiso p hp'
    rw [heq] at hv
    have hp'' := hp'
    rw [hCos',mem_preimage] at hp''
    exact hv.trans (curve_full_value_restrict_open hn k _ hDom (restrict W T) hTest (nestedOpens W V) _ hp'')

/-- The real intersection compares independently local references; there
is no global curve DOMAIN, canonicality or numerical certificate premise. -/
theorem local_curve_full_two_opens (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.ideal.IsCoherent) (U V : Opens X)
    (hU : IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : U → X) M))
    (hV : IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : V → X) M))
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
        ∀ k : ℕ,(invFamily hn (k+1)).inv (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T) ⟨z,hzU⟩=
          (invFamily hn (k+1)).inv (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T) ⟨z,hzV⟩) := by
  obtain ⟨_,_,hCosU,hValU⟩ := local_curve_full_nested_open hn M hM (W := U) (V := U⊓V) inf_le_left hU T hTU
  obtain ⟨_,_,hCosV,hValV⟩ := local_curve_full_nested_open hn M hM (W := V) (V := U⊓V) inf_le_right hV T hTV
  let q : openPreimage T (U⊓V) := ⟨z,⟨hzU,hzV⟩⟩
  refine ⟨(hCosU q).symm.trans (hCosV q),?_⟩
  intro hz k
  have hq := (hCosU q).mpr hz
  exact (hValU q hq k).symm.trans (hValV q hq k)

end
end Hironaka.HironakaOriginalCurveLocalReferenceComparison
