/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalAllStepOneSmoothValues
/-! A true original CAN prefix and a whole full-value-cut next centre
construct a genuine extended old companion TEST, without next canonicality. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalFullCutCompanionTestStep
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen CanonicalCentres GeneralValue GeneralCanonicalTail
  GeneralCompare NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail NonmonomialOrderCanonical
  CompanionRebase CompanionReductionAlong InvDomainCompanion InvDomainTowerAlong
  StepOneValue StepOneValueMasked StepOneRegime GermIdealOrder RelativePrincipalizationSpan
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n b k : ℕ} {X Y Z : CMfd.{u} n}

theorem compAt_test_step_of_upper_cut {Λ : Type v} [LinearOrder Λ]
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain b M)
    (F : ∀ {V : CMfd.{u} n},BlowupTower X V → V → Λ) (hf : OrdMonotone M F)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (hcan : IsCanonical M F T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp)
    (hpos : 0<nmOrd (geoTransformAlong M T) y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π) (hCut : ∀ c ∈ C,F T y≤F T c) :
    let q := nmOrd (geoTransformAlong M T) y
    let r := regimeRun (OrdRegime M q) T y
    let W := ordMask (geoTransformAlong M (head T r)) q
    IsGeoTestTower (compAt M q (head T r)) (restrict W (.step (tail T r) C π hπ)) := by
  let q := nmOrd (geoTransformAlong M T) y
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
  have hComp : IsGeoTestTower J (restrict W S) :=
    isGeoTestTower_companion_tail_of_canonical hn hM hf hpos T hT hcan y
  have hTailNext : IsGeoTestTower A (.step S C π hπ) := by
    refine ⟨hS,?_⟩
    rw [hCurrent]
    exact hC
  obtain ⟨_hOldRestricted,hAdm⟩ := isGeoTestTower_restrict W hA.isWellFormed.isClosedSubmanifold_N
    hA.isWellFormed.isCoherent (.step S C π hπ) hTailNext
  have hAW := isInvDomain_pullback_val W hA
  have hBound : ∀ x ∈ (MarkedIdeal.pullback (Subtype.val : W → (split T r).1) A).cosupp,
      x ∉ ordGe (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → (split T r).1) A) (q+1) := by
    intro x _hx hx
    exact notMem_ordGe_of_mem_ordMask x.property
      ((mem_ordGe_pullback_val_iff hn hA.isWellFormed hA.isNonzeroAlongAt W (q+1) x).mp hx)
  have hCos := cosupp_companionOf_geoTransformAlong hn hAW hpos hBound (restrict W S) hComp
  have hOrderCut : C ⊆ ordGe (geoTransformAlong M T) q := by
    intro c hc
    have hd := isInvDomain_geoTransformAlong hM T hT
    exact (mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt (hC.2.1 hc).1 q).mpr
      (hf T hT y hy c (hC.2.1 hc) (hCut c hc))
  refine ⟨hComp,hAdm.1,?_,?_⟩
  · intro x hx
    rw [hCos]
    refine ⟨?_,hAdm.2.1 hx⟩
    rw [geoTransformAlong_restrict W hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent S hS]
    apply (mem_ordGe_pullback_val_iff hn hAS.isWellFormed hAS.isNonzeroAlongAt (openPreimage S W) q x).mpr
    rw [hCurrent]
    exact hOrderCut hx
  · have hE : J.E=(MarkedIdeal.pullback (Subtype.val : W → (split T r).1) A).E := by
      simp only [J,compAt,companionOf,companionAlong_E,A]
      rfl
    rw [E_geoTransformAlong_congr hE (restrict W S)]
    exact hAdm.2.2

/-- The order dominance of the unchanged original full value is internal;
the WHOLE-centre cut remains an honest geometric condition. -/
theorem original_full_value_cut_compAt_test (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain (k+1) M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hcan : IsCanonical M ((invFamily hn (k+1)).inv M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp)
    (hpos : 0<nmOrd (geoTransformAlong M T) y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCut : ∀ c ∈ C,(invFamily hn (k+1)).inv M T y≤(invFamily hn (k+1)).inv M T c) :
    let q := nmOrd (geoTransformAlong M T) y
    let r := regimeRun (OrdRegime M q) T y
    let W := ordMask (geoTransformAlong M (head T r)) q
    let J := compAt M q (head T r)
    let R := restrict W (.step (tail T r) C π hπ)
    IsGeoTestTower J R ∧ IsInvDomain (k+1) (geoTransformAlong J R) := by
  have hOrd : OrdMonotone M ((invFamily hn (k+1)).inv M) :=
    ordMonotone_genInv (fun {A} J {B} R z =>
      Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn k) J (Y := B) R z) M
  have hTest := compAt_test_step_of_upper_cut hn M hM ((invFamily hn (k+1)).inv M)
    hOrd T hT hcan y hy hpos C hC π hπ hCut
  have hH := ((isGeoTestTower_iff_head_tail M T (regimeRun (OrdRegime M (nmOrd (geoTransformAlong M T) y)) T y)).mp hT).1
  have hJ := isInvDomain_compAt hn hpos _ (isInvDomain_geoTransformAlong hM _ hH)
  exact ⟨hTest,isInvDomain_geoTransformAlong hJ _ hTest⟩

/-- Both directions concern the SAME old companion and OLD attained q after
the real next step; no canonicality of the new prefix is inferred. -/
theorem original_full_value_cut_compAt_next_cosupport (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain (k+1) M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hcan : IsCanonical M ((invFamily hn (k+1)).inv M) T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp)
    (hpos : 0<nmOrd (geoTransformAlong M T) y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCut : ∀ c ∈ C,(invFamily hn (k+1)).inv M T y≤(invFamily hn (k+1)).inv M T c) :
    let q := nmOrd (geoTransformAlong M T) y
    let r := regimeRun (OrdRegime M q) T y
    let W := ordMask (geoTransformAlong M (head T r)) q
    ∀ z : openPreimage (.step (tail T r) C π hπ) W,
      z ∈ (geoTransformAlong (compAt M q (head T r)) (restrict W (.step (tail T r) C π hπ))).cosupp ↔
        z.val ∈ (geoTransformAlong M (.step T C π hπ)).cosupp ∧
          nmOrd (geoTransformAlong M (.step T C π hπ)) z.val=q := by
  dsimp only
  let q := nmOrd (geoTransformAlong M T) y
  let r := regimeRun (OrdRegime M q) T y
  obtain ⟨hJTest,_hCurrent⟩ := original_full_value_cut_compAt_test hn M hM T hT hcan y hy hpos C hC π hπ hCut
  obtain ⟨hH,hS⟩ := (isGeoTestTower_iff_head_tail M T r).mp hT
  have hTailNext : IsGeoTestTower (geoTransformAlong M (head T r)) (.step (tail T r) C π hπ) := by
    refine ⟨hS,?_⟩
    rw [←geoTransformAlong_head_tail M T r]
    exact hC
  intro z
  have hh := mem_cosupp_compAt_iff hn hM hpos (head T r) (.step (tail T r) C π hπ) hH hTailNext hJTest z
  simpa only [geoTransformAlong_step,←geoTransformAlong_head_tail M T r] using hh

end
end Hironaka.HironakaOriginalFullCutCompanionTestStep
