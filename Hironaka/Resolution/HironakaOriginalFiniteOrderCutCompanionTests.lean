/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedCurrentCompanion
/-! Actual companion TESTs follow from finite original admissible order cuts;
no canonical-prefix or companion-data field is stored in the literal recipe. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFiniteOrderCutCompanionTests
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen CanonicalCentres GeneralValue GeneralCanonicalTail HomogenizedIdealAlong
  GeneralCompare NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail NonmonomialOrderCanonical
  CompanionRebase CompanionReductionAlong InvDomainCompanion InvDomainTowerAlong
  StepOneValue StepOneValueMasked StepOneRegime GermIdealOrder RelativePrincipalizationSpan
open ResolutionInvariantSpec (IsInvDomain)
variable {n b k : ℕ} {X Y Z : CMfd.{u} n}

/-- Only actual original centre admissibility and ordinary natural order cuts. -/
def IsOrderCutTower (M : MarkedIdeal n X) : ∀ {Y : CMfd.{u} n},BlowupTower X Y → Prop
  | _,.refl => True
  | _,.step T C _ _ => IsOrderCutTower M T ∧
      (geoTransformAlong M T).IsAdmissibleCentre C ∧
      ∀ y∈(geoTransformAlong M T).cosupp,0<nmOrd (geoTransformAlong M T) y →
        ∀ c∈C,nmOrd (geoTransformAlong M T) y≤nmOrd (geoTransformAlong M T) c

theorem orderCutTower_geoTest (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (hT : IsOrderCutTower M T) : IsGeoTestTower M T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih => exact ⟨ih hT.1,hT.2.1⟩

theorem orderCutTower_step_of_full_cut (hn : 0<n) (M : MarkedIdeal n X)
    (T : BlowupTower X Y) (hT : IsOrderCutTower M T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCut : ∀ y∈(geoTransformAlong M T).cosupp,∀ c∈C,
      (invFamily hn (k+1)).inv M T y≤(invFamily hn (k+1)).inv M T c) :
    IsOrderCutTower M (.step T C π hπ) := by
  have hOrd : OrdMonotone M ((invFamily hn (k+1)).inv M) :=
    ordMonotone_genInv (fun {A} J {B} R z =>
      Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn k) J (Y := B) R z) M
  exact ⟨hT,hC,fun y hy _hp c hc =>
    hOrd T (orderCutTower_geoTest M T hT) y hy c (hC.2.1 hc) (hCut y hy c hc)⟩

private theorem actual_companion_trace_test (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain b M) (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T) (q : ℕ) (hq : 0<q) (y : Y)
    (hComp : let r := regimeRun (OrdRegime M q) T y
      let W := ordMask (geoTransformAlong M (head T r)) q
      IsGeoTestTower (compAt M q (head T r)) (restrict W (tail T r)))
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hOrder : C ⊆ ordGe (geoTransformAlong M T) q) :
    let r := regimeRun (OrdRegime M q) T y
    let W := ordMask (geoTransformAlong M (head T r)) q
    IsGeoTestTower (compAt M q (head T r)) (restrict W (.step (tail T r) C π hπ)) := by
  let r := regimeRun (OrdRegime M q) T y
  let H := head T r
  let S := tail T r
  let A := geoTransformAlong M H
  let W := ordMask A q
  let J := compAt M q H
  obtain ⟨hH,hS⟩ := (isGeoTestTower_iff_head_tail M T r).mp hT
  have hA := isInvDomain_geoTransformAlong hM H hH
  have hAS := isInvDomain_geoTransformAlong hA S hS
  have hCurrent : geoTransformAlong A S=geoTransformAlong M T := (geoTransformAlong_head_tail M T r).symm
  have hOldComp : IsGeoTestTower J (restrict W S) := hComp
  have hTailNext : IsGeoTestTower A (.step S C π hπ) := by
    refine ⟨hS,?_⟩;rw [hCurrent];exact hC
  obtain ⟨_hRestricted,hAdm⟩ := isGeoTestTower_restrict W hA.isWellFormed.isClosedSubmanifold_N
    hA.isWellFormed.isCoherent (.step S C π hπ) hTailNext
  have hAW := isInvDomain_pullback_val W hA
  have hBound : ∀ x∈(MarkedIdeal.pullback (Subtype.val : W → (split T r).1) A).cosupp,
      x∉ordGe (M := CMfd.of (n := n) W)
        (MarkedIdeal.pullback (Subtype.val : W → (split T r).1) A) (q+1) := by
    intro x _hx hx
    exact notMem_ordGe_of_mem_ordMask x.property
      ((mem_ordGe_pullback_val_iff hn hA.isWellFormed hA.isNonzeroAlongAt W (q+1) x).mp hx)
  have hCos := cosupp_companionOf_geoTransformAlong hn hAW hq hBound (restrict W S) hOldComp
  refine ⟨hOldComp,hAdm.1,?_,?_⟩
  · intro x hx
    rw [hCos]
    refine ⟨?_,hAdm.2.1 hx⟩
    rw [geoTransformAlong_restrict W hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent S hS]
    apply (mem_ordGe_pullback_val_iff hn hAS.isWellFormed hAS.isNonzeroAlongAt (openPreimage S W) q x).mpr
    rw [hCurrent]
    exact hOrder hx
  · have hE : J.E=(MarkedIdeal.pullback (Subtype.val : W → (split T r).1) A).E := by
      simp only [J,compAt,companionOf,companionAlong_E,A];rfl
    rw [E_geoTransformAlong_congr hE (restrict W S)]
    exact hAdm.2.2

/-- TRUE finite-history induction constructs every positive-order masked
companion TEST. No old CAN or companion TEST is a caller hypothesis. -/
theorem orderCutTower_current_companion_test (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain b M)
    (T : BlowupTower X Y) (hT : IsOrderCutTower M T) :
    ∀ q : ℕ,0<q → ∀ z : Y,
      let r := regimeRun (OrdRegime M q) T z
      let W := ordMask (geoTransformAlong M (head T r)) q
      IsGeoTestTower (compAt M q (head T r)) (restrict W (tail T r)) := by
  induction T with
  | refl => intro q hq z;trivial
  | step T C π hπ ih =>
    intro q hq z
    by_cases hOld : OrdRegime M q T (π z)
    · have hOldTest := orderCutTower_geoTest M T hT.1
      have hOldDomain := isInvDomain_geoTransformAlong hM T hOldTest
      have hpOld : 0<nmOrd (geoTransformAlong M T) (π z) := by rw [hOld.2];exact hq
      have hOrder : C ⊆ ordGe (geoTransformAlong M T) q := by
        intro c hc
        apply (mem_ordGe_iff hOldDomain.isWellFormed hOldDomain.isNonzeroAlongAt
          (hT.2.1.2.1 hc).1 q).mpr
        rw [←hOld.2]
        exact hT.2.2 (π z) hOld.1 hpOld c hc
      have hComp := ih hT.1 q hq (π z)
      have hNext := actual_companion_trace_test hn M hM T hOldTest q hq (π z) hComp
        C hT.2.1 π hπ hOrder
      rw [regimeRun_step_of (OrdRegime M q) T C π hπ hOld]
      exact hNext
    · rw [regimeRun_step_of_not (OrdRegime M q) T C π hπ hOld]
      trivial

/-- Actual recomputed companion DOMAIN/maximal order/current point and BOTH
WHOLE cosupport directions follow only after its genuine TEST is proved. -/
theorem orderCutTower_current_companion_data (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain b M)
    (T : BlowupTower X Y) (hT : IsOrderCutTower M T)
    (z : Y) (hz : z∈(geoTransformAlong M T).cosupp)
    (hq : 0<nmOrd (geoTransformAlong M T) z) :
    let q := nmOrd (geoTransformAlong M T) z
    let r := regimeRun (OrdRegime M q) T z
    let H := head T r
    let S := tail T r
    let W := ordMask (geoTransformAlong M H) q
    let J := compAt M q H
    let R := restrict W S
    IsInvDomain b J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧ IsGeoTestTower J R ∧
      IsInvDomain b (geoTransformAlong J R) ∧
      ∃ hp : S.proj z∈W,(⟨z,hp⟩ : openPreimage S W)∈(geoTransformAlong J R).cosupp ∧
        ∀ p : openPreimage S W,p∈(geoTransformAlong J R).cosupp ↔
          p.val∈(geoTransformAlong M T).cosupp ∧ nmOrd (geoTransformAlong M T) p.val=q := by
  dsimp only
  let q := nmOrd (geoTransformAlong M T) z
  let r := regimeRun (OrdRegime M q) T z
  let H := head T r
  let S := tail T r
  let W := ordMask (geoTransformAlong M H) q
  let J := compAt M q H
  let R := restrict W S
  have hUpper := orderCutTower_geoTest M T hT
  obtain ⟨hH,hS⟩ := (isGeoTestTower_iff_head_tail M T r).mp hUpper
  have hHeadDomain := isInvDomain_geoTransformAlong hM H hH
  have hJ := isInvDomain_compAt hn hq H hHeadDomain
  have hMax := isMaximalOrderAlong_compAt hn q H hHeadDomain
  have hTest := orderCutTower_current_companion_test hn M hM T hT q hq z
  have hMask : S.proj z∈W := (proj_tail_mem_ordMask hn hM T hUpper hz (o := q) rfl).2
  have hDict : ∀ p : openPreimage S W,p∈(geoTransformAlong J R).cosupp ↔
      p.val∈(geoTransformAlong M T).cosupp ∧ nmOrd (geoTransformAlong M T) p.val=q := by
    intro p
    have hh := mem_cosupp_compAt_iff hn hM hq H S hH hS hTest p
    rw [←geoTransformAlong_head_tail M T r] at hh
    exact hh
  exact ⟨hJ,hMax,hTest,isInvDomain_geoTransformAlong hJ R hTest,
    hMask,(hDict ⟨z,hMask⟩).mpr ⟨hz,rfl⟩,hDict⟩

end
end Hironaka.HironakaOriginalFiniteOrderCutCompanionTests
