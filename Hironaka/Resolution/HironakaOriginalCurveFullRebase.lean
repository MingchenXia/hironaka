/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalUntestedMemberCurveFullValues
/-! Entire original curve FULL values rebase across every genuine history
prefix, including references whose own history is not assumed a TEST. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCurveFullRebase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  InvDomainTowerAlong CanonicalCentres HironakaStepOneMemberLowerExtension HironakaStepOneMemberTailExtension
  HironakaOriginalUntestedMemberCurveFullValues
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- Independent curve-reference geometry gives actual full numerical
rebasing; no reference TEST or canonical history is assumed. -/
theorem modeled_curve_full_append_rebase (hn : 0<n) (k : ℕ)
    (m K : MarkedIdeal n X)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),
      IsGeoTestTower m R → IsInvDomain 1 (geoTransformAlong K R))
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hHS : IsGeoTestTower m (H.append S)) (y : Y)
    (hy : y∈(geoTransformAlong K (H.append S)).cosupp) :
    (invFamily hn (k+1)).inv K (H.append S) y=
      (invFamily hn (k+1)).inv (geoTransformAlong K H) S y := by
  obtain ⟨hH,hS⟩ := (isGeoTestTower_append_iff m H S).mp hHS
  have hTailModel : ∀ {V : CMfd.{u} n} (R : BlowupTower A V),
      IsGeoTestTower (geoTransformAlong m H) R →
        IsInvDomain 1 (geoTransformAlong (geoTransformAlong K H) R) := by
    intro V R hR
    have hd := hModel (H.append R) ((isGeoTestTower_append_iff m H R).mpr ⟨hH,hR⟩)
    rwa [geoTransformAlong_append] at hd
  have hyS : y∈(geoTransformAlong (geoTransformAlong K H) S).cosupp := by
    simpa only [geoTransformAlong_append] using hy
  rw [modeled_curve_full_value_formula hn k m K hModel (H.append S) hHS y hy,
    modeled_curve_full_value_formula hn k (geoTransformAlong m H) (geoTransformAlong K H)
      hTailModel S hS y hyS,geoTransformAlong_append]

/-- ONLY original DOMAIN one supplies the whole geometric reference family. -/
theorem original_curve_full_append_rebase (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hHS : IsGeoTestTower M (H.append S)) (y : Y)
    (hy : y∈(geoTransformAlong M (H.append S)).cosupp) :
    (invFamily hn (k+1)).inv M (H.append S) y=
      (invFamily hn (k+1)).inv (geoTransformAlong M H) S y :=
  modeled_curve_full_append_rebase hn k M M
    (fun R hR => isInvDomain_geoTransformAlong hM R hR) H S hHS y hy

/-- ONLY original bound-two data supplies every actual positive-member
reference domain; its own TEST is unnecessary for the numerical rebase. -/
theorem original_positive_member_curve_full_append_rebase (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (F : Finset (Fin M.E.length)) (hF : F.Nonempty)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hHS : IsGeoTestTower M (H.append S)) (y : Y)
    (hy : y∈(geoTransformAlong (memberRemainderMarked M F) (H.append S)).cosupp) :
    (invFamily hn (k+1)).inv (memberRemainderMarked M F) (H.append S) y=
      (invFamily hn (k+1)).inv (geoTransformAlong (memberRemainderMarked M F) H) S y :=
  modeled_curve_full_append_rebase hn k M (memberRemainderMarked M F)
    (fun R hR => isInvDomain_geoTransformAlong_memberRemainder hn M hM.isWellFormed
      hM.one_le_d hM.dimLE F hF R hR) H S hHS y hy

end
end Hironaka.HironakaOriginalCurveFullRebase
