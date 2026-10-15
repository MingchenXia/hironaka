/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.NonmonomialOrderTailExact
import Hironaka.Resolution.HironakaOriginalSameCarrierCurveStepOne
/-! The ACTUAL original curve GENERAL invariant on EVERY original TEST.
Actual run-companion data are internally constructed before its genuine leaf. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalAnyTestCurveFullValue
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen RelativePrincipalizationSpan
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail StepOneRegime
  CompanionRebase CompanionReductionAlong GeneralValue GeneralCompare GeneralCanonicalTail
  HironakaOriginalSameCarrierCurveStepOne HironakaOriginalCurvePositiveEmptyWindow
  MonomialCaseAlong CanonicalCentres GermIdealOrder HomogenizedIdealAlong
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- ORIGINAL ANYTEST supplies the ACTUAL run/head/mask and REFLEXIVE initial
companion membership BEFORE the genuine same-carrier non-test leaf producer. -/
theorem original_curve_actual_run_companion_step_one_value (hn : 0<n) (k : ℕ) (M : MarkedIdeal n X)
    (hM : IsInvDomain 1 M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) (hpos : 0<nmOrd (geoTransformAlong M T) y) :
    let q := nmOrd (geoTransformAlong M T) y
    let r := regimeRun (OrdRegime M q) T y
    let W := ordMask (geoTransformAlong M (head T r)) q
    ∃ hp : (tail T r).proj y ∈ W,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) (compAt M q (head T r))
        (restrict W (tail T r)) (⟨y,hp⟩ : openPreimage (tail T r) W)=toLex (0,⊤) := by
  let q := nmOrd (geoTransformAlong M T) y
  let r := regimeRun (OrdRegime M q) T y
  let H := head T r
  let S := tail T r
  let A := geoTransformAlong M H
  let W := ordMask A q
  let P := MarkedIdeal.pullback (Subtype.val : W → _) A
  let J := compAt M q H
  have hq : 1≤q := hpos
  obtain ⟨hH,hS⟩ := (isGeoTestTower_iff_head_tail M T r).mp hT
  have hA : IsInvDomain 1 A := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM H hH
  have hReg := proj_tail_mem_ordMask hn hM T hT hy (o := q) rfl
  change OrdRegime M q H (S.proj y) ∧ S.proj y ∈ W at hReg
  let p : openPreimage S W := ⟨y,hReg.2⟩
  have hJ : IsInvDomain 1 J := isInvDomain_compAt hn hq H hA
  have hmax : IsMaximalOrderAlong J.N J.ideal J.d := isMaximalOrderAlong_compAt hn q H hA
  have hP : IsInvDomain 1 P := InvDomainTowerAlong.isInvDomain_pullback_val W hA
  have hN : J.N=P.N := by
    simp only [J,P,compAt,companionOf,companionAlong_N]
    rfl
  have hE : J.E=P.E := by
    simp only [J,P,compAt,companionOf,companionAlong_E]
    rfl
  have hPS : IsGeoTestTower P (restrict W S) :=
    isGeoTestTower_restrict W hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent S hS
  have hInitial : (restrict W S).proj p ∈ J.cosupp := by
    have hi := (mem_cosupp_compAt_iff hn hM hq H .refl hH trivial trivial
      (⟨S.proj y,hReg.2⟩ : openPreimage (.refl : BlowupTower _ _) W)).mpr hReg.1
    change (⟨S.proj y,hReg.2⟩ : W) ∈ J.cosupp at hi
    have hPoint : (restrict W S).proj p=(⟨S.proj y,hReg.2⟩ : W) :=
      Subtype.ext (proj_restrict W S p)
    rw [hPoint]
    exact hi
  have hNoE : y ∉ ⋃ E ∈ (geoTransformAlong M T).E,E := by
    intro h
    have hz := (curve_domain_nonmonomial_unit_on_boundary hn (geoTransformAlong M T)
      (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT) y hy.1 h).2
    omega
  have hCurrent : geoTransformAlong P (restrict W S)=
      MarkedIdeal.pullback (Subtype.val : openPreimage S W → _) (geoTransformAlong A S) :=
    geoTransformAlong_restrict W hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent S hS
  have hOrig : geoTransformAlong A S=geoTransformAlong M T := (geoTransformAlong_head_tail M T r).symm
  have hpNoE : p ∉ ⋃ E ∈ (geoTransformAlong P (restrict W S)).E,E := by
    rw [hCurrent,hOrig]
    intro hpF
    obtain ⟨E,hE,hpE⟩ := mem_iUnion₂.mp hpF
    change E ∈ (geoTransformAlong M T).E.map ((Subtype.val : openPreimage S W → _) ⁻¹' ·) at hE
    obtain ⟨F,hF,rfl⟩ := List.mem_map.mp hE
    exact hNoE (mem_iUnion₂.mpr ⟨F,hF,hpE⟩)
  have hLeaf := same_carrier_curve_step_one_off_boundary
    (X := CMfd.of (n := n) W) (Y := CMfd.of (n := n) (openPreimage S W))
    hn P J hP.isWellFormed hJ hmax hN hE (restrict W S) hPS p hInitial hpNoE
  have hValueZero := hLeaf.2.2
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL at hValueZero
  rw [if_pos hLeaf.2.1] at hValueZero
  have hLevel := congrArg (fun v => (ofLex v).1) hValueZero
  change StepOneValue.level J (restrict W S) p=0 at hLevel
  refine ⟨hReg.2,?_⟩
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_pos hLeaf.2.1,hLevel]

/-- ONLY original curve-domain ANYTEST data compute the complete unchanged
original invariant, including its actual ORIGINAL run-companion positive branch. -/
theorem original_curve_any_test_full_value_formula (hn : 0<n) (k : ℕ) (M : MarkedIdeal n X)
    (hM : IsInvDomain 1 M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) :
    (invFamily hn (k+1)).inv M T y=
      if nmOrd (geoTransformAlong M T) y=0 then
        toLex (0,toLex (Sum.inl (gammaAlong n (geoTransformAlong M T).N
          (geoTransformAlong M T).ideal (geoTransformAlong M T).E (geoTransformAlong M T).d y)))
      else toLex (nmOrd (geoTransformAlong M T) y,toLex (Sum.inr
        ((toLex (0,(⊤ : WithTop (ValTy k))) : ℕ ×ₗ WithTop (ValTy k)) : WithTop (ℕ ×ₗ WithTop (ValTy k))))) := by
  by_cases hz : nmOrd (geoTransformAlong M T) y=0
  · rw [if_pos hz]
    exact genInv_of_nmOrd_eq_zero _ M T hz
  · rw [if_neg hz]
    have hp : 0<nmOrd (geoTransformAlong M T) y := Nat.pos_of_ne_zero hz
    obtain ⟨hMask,hValue⟩ := original_curve_actual_run_companion_step_one_value hn k M hM T hT y hy hp
    change genInv (fun {A} J {B} S p => Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J S p) M T y=_
    rw [genInv_of_nmOrd_ne_zero _ M T rfl hz,genLowerValue_eq_of_mem _ M hMask,hValue]

end
end Hironaka.HironakaOriginalAnyTestCurveFullValue
