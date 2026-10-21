/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteOrderCutMiddleHistory
/-! Actual fixed-companion cosupport supplies query regime/run alignment.
The genuine companion TEST is internally built before the existing run theorem. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFixedCompanionRunOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail GeneralValue GeneralCompare GeneralCanonicalTail
  StepOneRegime HironakaOriginalFiniteOrderCutCompanionTests
open ResolutionInvariantSpec (IsInvDomain)
variable {n b : ℕ} {X Y : CMfd.{u} n}

/-- Genuine old-mask membership and internally constructed companion TEST
supply the actual query order regime and true run lower bound. -/
theorem order_cut_fixed_mask_run (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain b M) (T : BlowupTower X Y) (hT : IsOrderCutTower M T)
    (q : ℕ) (hq : 0<q) (p z : Y) (hz : z∈(geoTransformAlong M T).cosupp)
    (hzW : (tail T (regimeRun (OrdRegime M q) T p)).proj z∈
      ordMask (geoTransformAlong M (head T (regimeRun (OrdRegime M q) T p))) q)
    (hzq : q≤nmOrd (geoTransformAlong M T) z) :
    OrdRegime M q T z ∧
      regimeRun (OrdRegime M q) T p≤regimeRun (OrdRegime M q) T z := by
  let r := regimeRun (OrdRegime M q) T p
  let H := head T r
  let S := tail T r
  let W := ordMask (geoTransformAlong M H) q
  have hUpper := orderCutTower_geoTest M T hT
  have hWhole : IsGeoTestTower M (H.append S) := by rw [head_append_tail];exact hUpper
  have hComp := orderCutTower_current_companion_test hn M hM T hT q hq p
  have hRun := ordRegime_and_le_regimeRun hn hM hq H W
    (fun _ _ h => notMem_ordGe_of_mem_ordMask h) S hWhole hComp z
  rw [head_append_tail] at hRun
  obtain ⟨hReg,hLe⟩ := hRun hz hzW hzq
  have hLen : S.length=r := by
    rw [length_tail,min_eq_left (regimeRun_le_length (OrdRegime M q) T p)]
  exact ⟨hReg,hLen.symm.trans_le hLe⟩

/-- ALL actual query hypotheses are supplied by genuine fixed-companion
controlled cosupport, without canonicality or desired point/run certificates. -/
theorem order_cut_fixed_companion_point_run (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain b M) (T : BlowupTower X Y) (hT : IsOrderCutTower M T)
    (q : ℕ) (hq : 0<q) (p : Y)
    (z : openPreimage (tail T (regimeRun (OrdRegime M q) T p))
      (ordMask (geoTransformAlong M (head T (regimeRun (OrdRegime M q) T p))) q))
    (hz : z∈(geoTransformAlong (compAt M q (head T (regimeRun (OrdRegime M q) T p)))
      (restrict (ordMask (geoTransformAlong M (head T (regimeRun (OrdRegime M q) T p))) q)
        (tail T (regimeRun (OrdRegime M q) T p)))).cosupp) :
    OrdRegime M q T z.val ∧
      regimeRun (OrdRegime M q) T p≤regimeRun (OrdRegime M q) T z.val := by
  let r := regimeRun (OrdRegime M q) T p
  have hUpper := orderCutTower_geoTest M T hT
  obtain ⟨hHead,hTail⟩ := (isGeoTestTower_iff_head_tail M T r).mp hUpper
  have hComp := orderCutTower_current_companion_test hn M hM T hT q hq p
  have hDict := mem_cosupp_compAt_iff hn hM hq (head T r) (tail T r) hHead hTail hComp z
  rw [←geoTransformAlong_head_tail M T r] at hDict
  obtain ⟨hzUpper,hzq⟩ := hDict.mp hz
  exact order_cut_fixed_mask_run hn M hM T hT q hq p z.val hzUpper z.property hzq.ge

end
end Hironaka.HironakaOriginalFixedCompanionRunOrder
