/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCurveLowerReferenceRebase
import Hironaka.Resolution.HironakaOriginalSourceChoiceCartesian
import Hironaka.Resolution.HironakaOriginalAllStepOneEtaleValues
/-! Genuine actual curve FULL locality on all TEST histories: tower
isomorphisms, real append restrictions and arbitrary two original opens. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCurveFullLocality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail CanonicalCentres InvDomainTowerAlong MarkedIdealBiholomorphism
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaOriginalUntestedCurveSmoothValues
  HironakaOriginalSourceChoiceCartesian HironakaOriginalAllStepOneEtaleValues
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X X' A Y Y' : CMfd.{u} n}

private theorem family_value_cast_depth (hn : 0<n) {a b : ℕ} (hab : a=b)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (z : Y) :
    congrArg ValTy hab ▸ (invFamily hn a).inv M T z=(invFamily hn b).inv M T z := by
  cases hab
  rfl

private theorem actual_curve_full_equal_dim (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M) (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T) {f : X' → X} {g : Y' → Y} {Q : BlowupTower X' Y'}
    (h : IsActualTowerPullback f Q T g) (z : Y')
    (hz : g z∈(geoTransformAlong M T).cosupp) :
    (invFamily hn (k+1)).inv (markedPullback (m := n) f M) Q z=
      (invFamily hn (k+1)).inv M T (g z) := by
  have hv := modeled_curve_smooth_full_value hn hn k h M M
    (fun R hR => isInvDomain_geoTransformAlong hM R hR) hT z hz
  rw [Nat.sub_self] at hv
  have hc := congrArg (fun v : ValTy (0+(k+1)) => congrArg ValTy (Nat.zero_add (k+1)) ▸ v) hv
  have hl := family_value_cast_depth hn (Nat.zero_add (k+1)) (markedPullback (m := n) f M) Q z
  exact hl.symm.trans (hc.trans (familyDimensionMap_zero (k+1) ((invFamily hn (k+1)).inv M T (g z))))

/-- Genuine stagewise isomorphisms give exact original curve FULL values
on every TEST, without any old or new canonicality. -/
theorem curve_full_value_of_towerIso (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M) (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T)
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    {Q : BlowupTower X' Y'} (h : IsTowerIso Φ Q T χ) (z : Y')
    (hz : χ z∈(geoTransformAlong M T).cosupp) :
    (invFamily hn (k+1)).inv (MarkedIdeal.pullback Φ M) Q z=
      (invFamily hn (k+1)).inv M T (χ z) :=
  actual_curve_full_equal_dim hn k M hM T hT (IsTowerIso.actual_cartesian h) z hz

/-- Actual append-restriction flattening supplies the true TEST/cosupport
dictionary BEFORE all original curve FULL values on the same real points. -/
theorem curve_full_value_restrict_append (hn : 0<n)
    (W : Opens X) (M : MarkedIdeal n (CMfd.of (n := n) W)) (hM : IsInvDomain 1 M)
    (B : BlowupTower X A) (T : BlowupTower A Y)
    (hTest : IsGeoTestTower M (restrict W (B.append T))) :
    IsGeoTestTower M ((restrict W B).append (restrict (openPreimage B W) T)) ∧
      ∀ (p : Y) (h : p∈openPreimage (B.append T) W)
        (h' : p∈openPreimage T (openPreimage B W)),
        (⟨p,h⟩ : openPreimage (B.append T) W)∈(geoTransformAlong M (restrict W (B.append T))).cosupp →
        (⟨p,h'⟩ : openPreimage T (openPreimage B W))∈
          (geoTransformAlong M ((restrict W B).append (restrict (openPreimage B W) T))).cosupp ∧
        ∀ k : ℕ,(invFamily hn (k+1)).inv M
          ((restrict W B).append (restrict (openPreimage B W) T)) ⟨p,h'⟩=
            (invFamily hn (k+1)).inv M (restrict W (B.append T)) ⟨p,h⟩ := by
  have hiso := (isTowerIso_restrict_append W B T).symm
  have hpb : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) W) ∞).symm M=M :=
    ContactCanonicalAlong.pullback_id M hM.isWellFormed.isCoherent
  have ht := (IsTowerIso.isGeoTestTower_iff _ hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hiso).mpr hTest
  rw [hpb] at ht
  refine ⟨ht,?_⟩
  intro p hp hp' hCos
  have hχ : (opensCongr (n := n) (openPreimage_append B T W).symm).symm ⟨p,hp'⟩=⟨p,hp⟩ := Subtype.ext rfl
  have hc := IsTowerIso.cosupp_geoTransformAlong _ hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hiso hTest
  rw [hpb] at hc
  refine ⟨?_,?_⟩
  · rw [hc,mem_preimage,hχ]
    exact hCos
  · intro k
    have hv := curve_full_value_of_towerIso hn k M hM _ hTest hiso ⟨p,hp'⟩ (by rw [hχ];exact hCos)
    rwa [hpb,hχ] at hv

/-- ONLY original curve DOMAIN and actual TEST supply every real open FULL
comparison, with no canonicality or lower reference TEST assumption. -/
theorem curve_full_value_restrict_open (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M) (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T) (U : Opens X) (z : openPreimage T U)
    (hz : z.val∈(geoTransformAlong M T).cosupp) :
    (invFamily hn (k+1)).inv (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T) z=
      (invFamily hn (k+1)).inv M T z.val :=
  actual_curve_full_equal_dim hn k M hM T hT (open_inclusion_actual_tower U T) z hz

/-- ANY two real opens compare through the SAME unchanged original endpoint. -/
theorem curve_full_value_two_opens (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M) (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T) (U V : Opens X) (z : Y)
    (hU : T.proj z∈U) (hV : T.proj z∈V) (hz : z∈(geoTransformAlong M T).cosupp) :
    (invFamily hn (k+1)).inv (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T) ⟨z,hU⟩=
      (invFamily hn (k+1)).inv (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T) ⟨z,hV⟩ :=
  (curve_full_value_restrict_open hn k M hM T hT U ⟨z,hU⟩ hz).trans
    (curve_full_value_restrict_open hn k M hM T hT V ⟨z,hV⟩ hz).symm

end
end Hironaka.HironakaOriginalCurveFullLocality
