/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteOrderCutRebase
/-! Genuine middle histories between actual order-run starts, retaining
literal concatenations, all-centre avoidance and whole companion rebase. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFiniteOrderCutMiddleHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen NonmonomialOrderLocal
  NonmonomialOrderCanonical NonmonomialOrderRegime NonmonomialOrderTail CompanionRebase
  StepOneRegime StepOneNearby StepOneCanonicalTail RestrictEmptyTower
  HironakaOriginalFiniteOrderCutCompanionTests HironakaOriginalFiniteOrderCutRebase
open ResolutionInvariantSpec (IsInvDomain)
variable {n b : ℕ} {X Y : CMfd.{u} n}

theorem orderCutTower_head (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (hT : IsOrderCutTower M T) (r : ℕ) : IsOrderCutTower M (head T r) := by
  induction T generalizing r with
  | refl => cases r <;> trivial
  | step T C π hπ ih =>
    cases r with
    | zero => exact hT
    | succ r => exact ih hT.1 r

/-- ONLY original cut geometry and actual computed run lengths construct
the real middle and actual whole companion equivalence. -/
theorem exists_actual_middle_of_order_cut (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain b M) (T : BlowupTower X Y)
    (hT : IsOrderCutTower M T) (z p : Y) (hz : z∈(geoTransformAlong M T).cosupp)
    (o : ℕ) (ho : 0<o) (hzo : nmOrd (geoTransformAlong M T) z=o)
    (rz rp : ℕ) (hrz : regimeRun (OrdRegime M o) T z=rz)
    (hrp : regimeRun (OrdRegime M o) T p=rp) (hle : rz≤rp) :
    let W := ordMask (geoTransformAlong M (head T rp)) o
    ∃ B : BlowupTower (split T rp).1 (split T rz).1,
      (head T rp).append B=head T rz ∧ B.append (tail T rz)=tail T rp ∧
      CentresAvoid W B ∧
      MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv
        (MarkedIdeal.pullback (Subtype.val : openPreimage B W → (split T rz).1)
          (companionOf n (geoTransformAlong M (head T rz)) o))
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → (split T rp).1)
          (companionOf n (geoTransformAlong M (head T rp)) o)) (restrict W B)) := by
  let W := ordMask (geoTransformAlong M (head T rp)) o
  obtain ⟨B,hB₁,hB₂,hAvoid⟩ : ∃ B : BlowupTower (split T rp).1 (split T rz).1,
      (head T rp).append B=head T rz ∧ B.append (tail T rz)=tail T rp ∧ CentresAvoid W B := by
    rcases hle.lt_or_eq with hLt|hEq
    · have hrple : rp≤T.length := hrp ▸ regimeRun_le_length _ T p
      have hrzlt : rz<T.length := lt_of_lt_of_le hLt hrple
      obtain ⟨τ,hτ₁,hτ₂⟩ := exists_split_le T (a := rz) (b := rz+1) (Nat.le_succ rz)
      have hτlen : τ.length=1 := by
        have hh := congrArg BlowupTower.length hτ₁
        rw [BlowupTower.length_append,length_head,length_head] at hh
        omega
      obtain ⟨C,π,hπ,rfl⟩ := exists_eq_step_refl τ hτlen
      obtain ⟨B₂,hMid₁,hMid₂⟩ := exists_split_le T (a := rz+1) (b := rp) (by omega)
      refine ⟨B₂.append (.step .refl C π hπ),?_,?_,?_⟩
      · rw [←BlowupTower.append_assoc,hMid₁,hτ₁]
      · rw [BlowupTower.append_assoc,hτ₂,hMid₂]
      · show CentresAvoid W (.step B₂ C π hπ)
        obtain ⟨hw,hwo⟩ := orderCutTower_succ_le_before_start hn M hM T hT hz hzo
          (j := rz+1) (by rw [hrz]) (by rw [hrz];exact hrzlt)
        rw [←hMid₁] at hw hwo
        have hWhole : (head T rp).append (.step B₂ C π hπ)=head T rz := by
          rw [←hτ₁,←hMid₁]
          rfl
        have hPrefix : IsOrderCutTower M ((head T rp).append (.step B₂ C π hπ)) := by
          rw [hWhole]
          exact orderCutTower_head M T hT rz
        exact (orderCutTower_centresAvoid_and_companion_rebase hn M hM ho (head T rp) W
          (fun _ _ hx => notMem_ordGe_of_mem_ordMask hx) B₂ C π hπ hPrefix hw hwo).1
    · subst hEq
      obtain ⟨B,hB₁,hB₂⟩ := exists_split_le T (le_refl rz)
      refine ⟨B,hB₁,hB₂,centresAvoid_of_length_eq_zero W B ?_⟩
      have hh := congrArg BlowupTower.length hB₁
      rw [BlowupTower.length_append] at hh
      omega
  refine ⟨B,hB₁,hB₂,hAvoid,?_⟩
  have hGeo : IsGeoTestTower M ((head T rp).append B) := by
    rw [hB₁]
    exact orderCutTower_geoTest M (head T rz) (orderCutTower_head M T hT rz)
  obtain ⟨hHead,hMiddle⟩ := (isGeoTestTower_append_iff M (head T rp) B).mp hGeo
  have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM (head T rp) hHead
  have he := CompanionRebase.restrictEquiv_companionOf_rebase hn hDom ho B hMiddle W hAvoid
  have hModel : geoTransformAlong (geoTransformAlong M (head T rp)) B=
      geoTransformAlong M (head T rz) := by
    rw [←geoTransformAlong_append,hB₁]
  rw [hModel] at he
  exact he

end
end Hironaka.HironakaOriginalFiniteOrderCutMiddleHistory
