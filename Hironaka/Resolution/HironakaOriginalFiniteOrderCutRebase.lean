/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteOrderCutCompanionTests
/-! Genuine order monotonicity and whole geometric companion rebase on
finite literal order cuts, with no original canonicality hypotheses. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFiniteOrderCutRebase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen NonmonomialOrderLocal
  NonmonomialOrderCanonical NonmonomialOrderRegime NonmonomialOrderTail CompanionRebase
  StepOneRegime GermIdealOrder RelativePrincipalizationSpan RestrictEmptyTower
  HironakaOriginalFiniteOrderCutCompanionTests
open ResolutionInvariantSpec (IsInvDomain)
variable {n b : ℕ} {X Y Z : CMfd.{u} n}

/-- Positive-reference cuts also force equality at zero-order centre points. -/
theorem orderCutTower_centre_order_eq (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsOrderCutTower M (.step T C π hπ)) {c d : Y} (hc : c∈C) (hd : d∈C) :
    nmOrd (geoTransformAlong M T) c=nmOrd (geoTransformAlong M T) d := by
  have hLe (x y : Y) (hx : x∈C) (hy : y∈C) :
      nmOrd (geoTransformAlong M T) x≤nmOrd (geoTransformAlong M T) y := by
    by_cases hp : 0<nmOrd (geoTransformAlong M T) x
    · exact hT.2.2 x (hT.2.1.2.1 hx) hp y hy
    · omega
  exact le_antisymm (hLe c d hc hd) (hLe d c hd hc)

/-- True original local order theorems apply after actual centre constancy
has been internally proved from the literal cut recipe. -/
theorem orderCutTower_nmOrd_step_le (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain b M) (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (hT : IsOrderCutTower M (.step T C π hπ))
    {z : Z} (hz : z∈(geoTransformAlong M (.step T C π hπ)).cosupp) :
    π z∈(geoTransformAlong M T).cosupp ∧
      nmOrd (geoTransformAlong M (.step T C π hπ)) z≤nmOrd (geoTransformAlong M T) (π z) := by
  have hOld := orderCutTower_geoTest M T hT.1
  have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hOld
  have hz' : z∈((geoTransformAlong M T).geoTransform C π).cosupp := hz
  by_cases hzC : π z∈C
  · exact ⟨hT.2.1.2.1 hzC,nmOrd_geoTransform_le_of_level hn hCurrent hT.2.1 hπ
      (fun c hc => orderCutTower_centre_order_eq M T C π hπ hT hc hzC) hz' hzC⟩
  · have hCos : π z∈(geoTransformAlong M T).cosupp :=
      (TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong M T)
        hCurrent.isWellFormed.isClosedSubmanifold_N.1
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hCurrent.isWellFormed.isCoherent hg)
        hπ hzC).mp hz'
    refine ⟨hCos,?_⟩
    show nmOrd ((geoTransformAlong M T).geoTransform C π) z≤_
    rw [nmOrd_geoTransform_of_notMem hn hCurrent hT.2.1 hπ hzC]

/-- Actual cosupport and nonincrease on EVERY finite tail of the same history. -/
theorem orderCutTower_nmOrd_le_proj (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain b M) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y),IsOrderCutTower M (T₀.append S) →
      ∀ z∈(geoTransformAlong M (T₀.append S)).cosupp,
        S.proj z∈(geoTransformAlong M T₀).cosupp ∧
          nmOrd (geoTransformAlong M (T₀.append S)) z≤nmOrd (geoTransformAlong M T₀) (S.proj z)
  | _,.refl,_,_,hz => ⟨hz,le_rfl⟩
  | _,.step S C π hπ,hT,z,hz => by
    obtain ⟨hOld,hLe⟩ := orderCutTower_nmOrd_step_le hn M hM (T₀.append S) C π hπ hT hz
    obtain ⟨hBase,hLeBase⟩ := orderCutTower_nmOrd_le_proj hn M hM T₀ S hT.1 (π z) hOld
    exact ⟨hBase,hLe.trans hLeBase⟩

/-- The REAL failed-regime stage has strictly larger order, without CAN. -/
theorem orderCutTower_succ_le_before_start (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain b M) (T : BlowupTower X Y) (hT : IsOrderCutTower M T)
    {y : Y} (hy : y∈(geoTransformAlong M T).cosupp) {q j : ℕ}
    (hyq : nmOrd (geoTransformAlong M T) y=q)
    (hj : regimeRun (OrdRegime M q) T y+1=j)
    (hr : regimeRun (OrdRegime M q) T y<T.length) :
    (tail T j).proj y∈(geoTransformAlong M (head T j)).cosupp ∧
      q+1≤nmOrd (geoTransformAlong M (head T j)) ((tail T j).proj y) := by
  have hNot := not_regime_head_regimeRun (OrdRegime M q) T y hr
  rw [hj] at hNot
  have hRecipe : IsOrderCutTower M ((head T j).append (tail T j)) := by
    rw [head_append_tail];exact hT
  have hPoint : y∈(geoTransformAlong M ((head T j).append (tail T j))).cosupp := by
    rw [head_append_tail];exact hy
  obtain ⟨hCos,hLe⟩ := orderCutTower_nmOrd_le_proj hn M hM (head T j) (tail T j) hRecipe y hPoint
  rw [head_append_tail,hyq] at hLe
  refine ⟨hCos,?_⟩
  rcases hLe.lt_or_eq with hLt|hEq
  · exact hLt
  · exact (hNot ⟨hCos,hEq.symm⟩).elim

private theorem actual_centre_threshold (_hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain b M) (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (hT : IsOrderCutTower M (.step T C π hπ))
    {w : Y} (hw : w∈(geoTransformAlong M T).cosupp) {q : ℕ}
    (hwq : q+1≤nmOrd (geoTransformAlong M T) w) : C⊆ordGe (geoTransformAlong M T) (q+1) := by
  have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T (orderCutTower_geoTest M T hT.1)
  intro c hc
  exact (mem_ordGe_iff hDom.isWellFormed hDom.isNonzeroAlongAt
    ((geoTransformAlong M T).cosupp_subset_N (hT.2.1.2.1 hc)) (q+1)).mpr
      (hwq.trans (hT.2.2 w hw (by omega) c hc))

/-- True ALL-centre thresholds across the actual middle and last step. -/
theorem orderCutTower_centresOrdGt (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain b M) {q : ℕ} {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    ∀ {Y Z : CMfd.{u} n} (S : BlowupTower Y₀ Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      IsOrderCutTower M (T₀.append (.step S C π hπ)) →
      ∀ w∈(geoTransformAlong M (T₀.append S)).cosupp,
        q+1≤nmOrd (geoTransformAlong M (T₀.append S)) w →
          CentresOrdGt (geoTransformAlong M T₀) q (.step S C π hπ)
  | _,_,.refl,C,π,hπ,hT,w,hw,hwq => by
    refine (centresOrdGt_step_iff _ q _ C π hπ).mpr ⟨trivial,?_⟩
    exact actual_centre_threshold hn M hM (T₀.append .refl) C π hπ hT hw hwq
  | _,_,.step S C' π' hπ',C,π,hπ,hT,w,hw,hwq => by
    obtain ⟨hw',hLe⟩ := orderCutTower_nmOrd_step_le hn M hM (T₀.append S) C' π' hπ' hT.1 hw
    have ih := orderCutTower_centresOrdGt hn M hM T₀ S C' π' hπ' hT.1 (π' w) hw' (hwq.trans hLe)
    refine (centresOrdGt_step_iff _ q _ C π hπ).mpr ⟨ih,?_⟩
    have hSub := actual_centre_threshold hn M hM (T₀.append (.step S C' π' hπ')) C π hπ hT hw hwq
    rw [geoTransformAlong_append] at hSub
    exact hSub

/-- Genuine thresholds imply actual earlier-open avoidance before the real
whole relative-ideal companion rebase; no numeric/canonical data is used. -/
theorem orderCutTower_centresAvoid_and_companion_rebase (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain b M) {q : ℕ} (hq : 0<q) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (W : Opens Y₀)
    (hBound : ∀ x∈(geoTransformAlong M T₀).cosupp,x∈W → x∉ordGe (geoTransformAlong M T₀) (q+1))
    (S : BlowupTower Y₀ Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsOrderCutTower M (T₀.append (.step S C π hπ)))
    {w : Y} (hw : w∈(geoTransformAlong M (T₀.append S)).cosupp)
    (hwq : q+1≤nmOrd (geoTransformAlong M (T₀.append S)) w) :
    CentresAvoid W (.step S C π hπ) ∧
      MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv
        (MarkedIdeal.pullback (Subtype.val : openPreimage (.step S C π hπ) W → Z)
          (companionOf n (geoTransformAlong (geoTransformAlong M T₀) (.step S C π hπ)) q))
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y₀)
          (companionOf n (geoTransformAlong M T₀) q)) (restrict W (.step S C π hπ))) := by
  have hUpper := orderCutTower_geoTest M (T₀.append (.step S C π hπ)) hT
  obtain ⟨hHead,hTail⟩ := (isGeoTestTower_append_iff M T₀ (.step S C π hπ)).mp hUpper
  have hHeadDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T₀ hHead
  have hThreshold := orderCutTower_centresOrdGt hn M hM T₀ S C π hπ hT w hw hwq
  have hAvoid := (centresAvoid_of_centresOrdGt hn hHeadDom W hBound (.step S C π hπ) hTail hThreshold).1
  exact ⟨hAvoid,CompanionRebase.restrictEquiv_companionOf_rebase hn hHeadDom hq (.step S C π hπ) hTail W hAvoid⟩

end
end Hironaka.HironakaOriginalFiniteOrderCutRebase
