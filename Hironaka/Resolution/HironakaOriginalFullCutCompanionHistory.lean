/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFixedCompanionStepOneComparison
import Hironaka.Resolution.HironakaOriginalFiniteFullCutSmoothHistory
/-! Whole original FULL cuts supply the actual companion StepOne histories
by genuine constructor induction, without canonicality or lower certificates. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFullCutCompanionHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  GeneralValue GeneralCompare GeneralCanonicalTail NonmonomialOrderLocal NonmonomialOrderRegime
  NonmonomialOrderTail StepOneRegime CanonicalCentres InvDomainTowerAlong
  HironakaOriginalFixedCompanionStepOneComparison HironakaOriginalFiniteOrderCutCompanionTests
  HironakaOriginalFiniteStepOneCutMaskAvoidance HironakaOriginalFiniteFullCutSmoothHistory
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Genuine own recipes and actual fixed companion cosupport precede the
literal original FULL positive branch, not a numerical representation input. -/
theorem full_value_eq_fixed_companion_of_own_cuts (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsOrderCutTower M T) (q : ℕ) (hq : 0<q)
    (p : Y) (hp : p∈(geoTransformAlong M T).cosupp)
    (hpq : nmOrd (geoTransformAlong M T) p=q)
    (hOwn : ∀ y : Y,IsStepOneCutTower hn (d+1)
      (compAt M q (head T (regimeRun (OrdRegime M q) T y)))
      (restrict (ordMask (geoTransformAlong M (head T (regimeRun (OrdRegime M q) T y))) q)
        (tail T (regimeRun (OrdRegime M q) T y))))
    (z : openPreimage (tail T (regimeRun (OrdRegime M q) T p))
      (ordMask (geoTransformAlong M (head T (regimeRun (OrdRegime M q) T p))) q))
    (hz : z∈(geoTransformAlong (compAt M q (head T (regimeRun (OrdRegime M q) T p)))
      (restrict (ordMask (geoTransformAlong M (head T (regimeRun (OrdRegime M q) T p))) q)
        (tail T (regimeRun (OrdRegime M q) T p)))).cosupp) :
    (invFamily hn (d+2)).inv M T z.val=
      toLex (q,toLex (Sum.inr
        ((Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1))
          (compAt M q (head T (regimeRun (OrdRegime M q) T p)))
          (restrict (ordMask (geoTransformAlong M (head T (regimeRun (OrdRegime M q) T p))) q)
            (tail T (regimeRun (OrdRegime M q) T p))) z :
          ℕ ×ₗ WithTop (ValTy (d+1))) : WithTop (ℕ ×ₗ WithTop (ValTy (d+1)))))) := by
  let r := regimeRun (OrdRegime M q) T p
  have hUpper := orderCutTower_geoTest M T hT
  obtain ⟨hH,hS⟩ := (isGeoTestTower_iff_head_tail M T r).mp hUpper
  have hComp := orderCutTower_current_companion_test hn M hM T hT q hq p
  have hDict := mem_cosupp_compAt_iff hn hM hq (head T r) (tail T r) hH hS hComp z
  rw [←geoTransformAlong_head_tail M T r] at hDict
  have hzq := (hDict.mp hz).2
  obtain ⟨hMask,hValues⟩ := fixed_companion_step_one_eq_own hn d M hM T hT q hq
    p hp hpq z hz (hOwn z.val)
  change genInv (fun {A} J {B} S y =>
    Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn (d+1)) J (Y := B) S y) M T z.val=_
  rw [genInv_of_nmOrd_ne_zero _ M T hzq (Nat.ne_of_gt hq),
    genLowerValue_eq_of_mem _ M hMask,←hValues d]

/-- Real whole upper FULL cuts, not CAN or a supplied companion recipe,
construct EVERY actual positive-order companion StepOne history. -/
theorem fullCutTower_current_companion_stepone_cut (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsFullCutTower hn d M T) :
    ∀ q : ℕ,0<q → ∀ z : Y,
      let r := regimeRun (OrdRegime M q) T z
      let W := ordMask (geoTransformAlong M (head T r)) q
      IsStepOneCutTower hn (d+1) (compAt M q (head T r)) (restrict W (tail T r)) := by
  induction T with
  | refl => intro q hq z;trivial
  | step T C π hπ ih =>
    intro q hq z
    have hOrder := fullCutTower_orderCut hn d M (.step T C π hπ) hT
    by_cases hOld : OrdRegime M q T (π z)
    · have hPrevious := ih hT.1
      have hCompCut := hPrevious q hq (π z)
      have hNextTest := orderCutTower_current_companion_test hn M hM
        (.step T C π hπ) hOrder q hq z
      rw [regimeRun_step_of (OrdRegime M q) T C π hπ hOld] at hNextTest ⊢
      let r := regimeRun (OrdRegime M q) T (π z)
      let H := head T r
      let S := tail T r
      let W := ordMask (geoTransformAlong M H) q
      let J := compAt M q H
      change IsStepOneCutTower hn (d+1) J (restrict W (.step S C π hπ))
      change IsGeoTestTower J (restrict W (.step S C π hπ)) at hNextTest
      have hUpper := orderCutTower_geoTest M T hOrder.1
      obtain ⟨hH,hS⟩ := (isGeoTestTower_iff_head_tail M T r).mp hUpper
      refine ⟨hCompCut,hNextTest.2,?_⟩
      intro y hy c hc
      have hYCos := mem_cosupp_compAt_iff hn hM hq H S hH hS hNextTest.1 y
      rw [←geoTransformAlong_head_tail M T r] at hYCos
      have hyUpper := (hYCos.mp hy).1
      have hcCos : c∈(geoTransformAlong J (restrict W S)).cosupp := hNextTest.2.2.1 hc
      have hyValue := full_value_eq_fixed_companion_of_own_cuts hn d M hM T hOrder.1 q hq
        (π z) hOld.1 hOld.2 (hPrevious q hq) y hy
      have hcValue := full_value_eq_fixed_companion_of_own_cuts hn d M hM T hOrder.1 q hq
        (π z) hOld.1 hOld.2 (hPrevious q hq) c hcCos
      have hBound := hT.2.2 y.val hyUpper c.val hc
      rw [hyValue,hcValue] at hBound
      have hSum := (Prod.Lex.le_iff.mp hBound).elim
        (fun hlt => False.elim ((Nat.lt_irrefl q) hlt)) (fun heq => heq.2)
      exact WithTop.coe_le_coe.mp (Sum.Lex.inr_le_inr_iff.mp hSum)
    · rw [regimeRun_step_of_not (OrdRegime M q) T C π hπ hOld]
      trivial

end
end Hironaka.HironakaOriginalFullCutCompanionHistory
