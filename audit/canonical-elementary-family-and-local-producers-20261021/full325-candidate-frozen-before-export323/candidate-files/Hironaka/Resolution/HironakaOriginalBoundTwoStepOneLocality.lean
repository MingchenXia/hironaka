/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalGivenSmoothStepOneValues
import Hironaka.Resolution.HironakaOriginalCurveFullLocality
/-! Actual DOMAIN2 StepOne locality on every TEST: genuine tower isomorphisms,
append restrictions and real opens, with no canonicality or numeric certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalBoundTwoStepOneLocality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail CanonicalCentres InvDomainTowerAlong MarkedIdealBiholomorphism
  HomogenizedIdealAlong StepOneValue StepOneLowerDomain
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaOriginalGivenSmoothStepOneValues
  HironakaOriginalSourceChoiceCartesian HironakaOriginalAllStepOneEtaleValues
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X X' A Y Y' : CMfd.{u} n}

private theorem stepDimensionMap_cast {α β : Type} (e : β=α) (f : α → β)
    (hf : ∀ x,e ▸ f x=x) (v : ℕ ×ₗ WithTop α) :
    congrArg (fun V => ℕ ×ₗ WithTop V) e ▸ stepDimensionMap f v=v := by
  subst β
  have he : f=id := funext hf
  rw [he]
  simp [stepDimensionMap]

private theorem stepOneInvM_cast_depth (hn : 0<n) {a b : ℕ} (hab : a=b)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (z : Y) :
    congrArg (fun j => ℕ ×ₗ WithTop (ValTy j)) hab ▸
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn a) M T z=
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn b) M T z := by
  cases hab
  rfl

/-- The SAME given Cartesian history is used before EVERY original branch;
zero-relative-dimension identity is on all values, with only true depth casts. -/
private theorem actual_step_one_equal_dim (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    {f : X' → X} {g : Y' → Y} {Q : BlowupTower X' Y'}
    (h : IsActualTowerPullback f Q T g) (z : Y')
    (hz : g z∈(geoTransformAlong M T).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) (markedPullback (m := n) f M) Q z=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z) := by
  have hv := (original_given_all_step_one_smooth_values hn hn M hM hmax T hT h).2 z hz k
  rw [Nat.sub_self] at hv
  let e := congrArg (fun V => ℕ ×ₗ WithTop V) (congrArg ValTy (Nat.zero_add (k+1)))
  have hMap := stepDimensionMap_cast (congrArg ValTy (Nat.zero_add (k+1)))
    (familyDimensionMap 0 (k+1)) (familyDimensionMap_zero (k+1))
    (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (g z))
  have hCast := congrArg (fun w => e ▸ w) hv
  have hSource := stepOneInvM_cast_depth hn (Nat.zero_add (k+1)) (markedPullback (m := n) f M) Q z
  exact hSource.symm.trans (hCast.trans hMap)

/-- Real stagewise isomorphisms, not numerical isomorphism certificates. -/
theorem step_one_value_of_towerIso (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    {Q : BlowupTower X' Y'} (h : IsTowerIso Φ Q T χ) (z : Y')
    (hz : χ z∈(geoTransformAlong M T).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) (MarkedIdeal.pullback Φ M) Q z=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T (χ z) :=
  actual_step_one_equal_dim hn k M hM hmax T hT (IsTowerIso.actual_cartesian h) z hz

/-- Genuine append flattening supplies actual TEST/cosupport before values. -/
theorem step_one_value_restrict_append (hn : 0<n)
    (W : Opens X) (M : MarkedIdeal n (CMfd.of (n := n) W)) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (B : BlowupTower X A) (T : BlowupTower A Y)
    (hTest : IsGeoTestTower M (restrict W (B.append T))) :
    IsGeoTestTower M ((restrict W B).append (restrict (openPreimage B W) T)) ∧
      ∀ (p : Y) (hp : p∈openPreimage (B.append T) W)
        (hp' : p∈openPreimage T (openPreimage B W)),
        (⟨p,hp⟩ : openPreimage (B.append T) W)∈(geoTransformAlong M (restrict W (B.append T))).cosupp →
        (⟨p,hp'⟩ : openPreimage T (openPreimage B W))∈
          (geoTransformAlong M ((restrict W B).append (restrict (openPreimage B W) T))).cosupp ∧
        ∀ k : ℕ,Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M
          ((restrict W B).append (restrict (openPreimage B W) T)) ⟨p,hp'⟩=
            Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M
              (restrict W (B.append T)) ⟨p,hp⟩ := by
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
    have hv := step_one_value_of_towerIso hn k M hM hmax _ hTest hiso ⟨p,hp'⟩ (by rw [hχ];exact hCos)
    rwa [hpb,hχ] at hv

/-- Actual open inclusion and its genuine restriction history. -/
theorem step_one_value_restrict_open (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (U : Opens X) (z : openPreimage T U)
    (hz : z.val∈(geoTransformAlong M T).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1))
      (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T) z=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) M T z.val :=
  actual_step_one_equal_dim hn k M hM hmax T hT (HironakaOriginalUntestedCurveSmoothValues.open_inclusion_actual_tower U T) z hz

/-- ANY two real opens compare through the SAME original endpoint. -/
theorem step_one_value_two_opens (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (U V : Opens X) (z : Y)
    (hU : T.proj z∈U) (hV : T.proj z∈V) (hz : z∈(geoTransformAlong M T).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1))
      (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T) ⟨z,hU⟩=
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1))
          (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T) ⟨z,hV⟩ :=
  (step_one_value_restrict_open hn k M hM hmax T hT U ⟨z,hU⟩ hz).trans
    (step_one_value_restrict_open hn k M hM hmax T hT V ⟨z,hV⟩ hz).symm

end
end Hironaka.HironakaOriginalBoundTwoStepOneLocality
