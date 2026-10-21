/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalReferenceValueBoundedStep
/-! SAME ORIGINAL full-history invariant and SAME FIXED OLD reference cut over
EVERY finite original canonical tail. Raw auxiliary geometric comparison after
erasure does not imply auxiliary admissibility/canonicality. Scheduler and
arbitrary-admissible original coefficient semicoherence remain OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalReferenceValueCanonicalTailTransform
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  CanonicalCentres GermIdealOrder HironakaOriginalReferenceValueOpenNaturality
  HironakaOriginalReferenceValueAuxiliaryMarked HironakaOriginalReferenceValueLocalBlowup
  HironakaOriginalReferenceValueBoundedStep HironakaOriginalReferenceValueCanonicalNextTransform
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Literal fixed OLD original full-reference cut on the real tail preimage. -/
def tailFixedReferenceCut (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (T : BlowupTower X Y) (x : Y) (W : Opens Y) (S : BlowupTower Y Z) : Set (openPreimage S W) :=
  thresholdCut hn d m (T.append S) ((invFamily hn d).inv m T x) (openPreimage S W)

private theorem actual_tail_induction (hn : 0 < n) (d : ℕ) (m : MarkedIdeal n X)
    (h : IsInvDomain d m) (T : BlowupTower X Y) (b : ValTy d) (W : Opens Y)
    (B : MarkedIdeal n (CMfd.of (n := n) W)) (hBN : B.N=univ) (hBd : B.d=1)
    (hBI : B.ideal=vanishingIdeal (n := n) (thresholdCut hn d m T b W))
    (hC : IsClosedSubmanifold n (thresholdCut hn d m T b W))
    (hb : ∀ y ∈ (geoTransformAlong m T).cosupp,y ∈ W → (invFamily hn d).inv m T y ≤ b) :
    ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z),IsCanonical m ((invFamily hn d).inv m) (T.append S) →
      let J := geoTransformAlong B (restrict W S)
      let C := thresholdCut hn d m (T.append S) b (openPreimage S W)
      J.N=univ ∧ J.d=1 ∧ J.ideal=vanishingIdeal (n := n) C ∧ IsClosedSubmanifold n C ∧ J.ideal.IsCoherent ∧
      ∀ z ∈ (geoTransformAlong m (T.append S)).cosupp,z ∈ openPreimage S W → (invFamily hn d).inv m (T.append S) z ≤ b
  | _, .refl, _ => ⟨hBN,hBd,hBI,hC,hBI.symm ▸ VanishingIdealCoherent.isCoherent_vanishingIdeal hC,hb⟩
  | _, .step S D π hπ, hc => by
    have hcp : IsCanonical m ((invFamily hn d).inv m) (T.append S) := hc.1
    obtain ⟨hN0,hd0,hI0,hC0,hcoh0,hbound0⟩ := actual_tail_induction hn d m h T b W B hBN hBd hBI hC hb S hcp
    let V := openPreimage S W
    let J := geoTransformAlong B (restrict W S)
    have hstep := bounded_fixed_threshold_step hn d m h (T.append S) hcp b V hbound0 hC0 hπ hc
    have hr : IsBlowupAlong n ((Subtype.val : V → _) ⁻¹' D) (nextMap hπ V) :=
      BlowupRestrictOpen.isBlowupAlong_restrict hπ V (V.isOpen.preimage hπ.contMDiff.continuous)
    have hInew : (J.geoTransform ((Subtype.val : V → _) ⁻¹' D) (nextMap hπ V)).ideal =
        vanishingIdeal (n := n) (thresholdCut hn d m (.step (T.append S) D π hπ) b (nextOpen hπ V)) := by
      rw [geoTransform_ideal_eq_controlledTransform hN0 hcoh0 hr,hI0,hd0]
      exact hstep.2.2.1
    exact ⟨geoTransform_N_eq_univ hN0 hr,hd0,hInew,hstep.1,hInew.symm ▸ hstep.2.2.2,hstep.2.1⟩

/-- ONLY original inputs internally construct one real window with ENTIRE actual
raw auxiliary ideal comparison for EVERY finite ORIGINAL canonical tail. -/
theorem exists_original_canonical_tail_reference_transform (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T) (x : Y)
    (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ W : Opens Y,x ∈ W ∧ ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z),
      IsCanonical m ((invFamily hn d).inv m) (T.append S) →
      let J := geoTransformAlong (referenceMarked hn d m T x W) (restrict W S)
      J.N=univ ∧ J.d=1 ∧ J.ideal=vanishingIdeal (n := n) (tailFixedReferenceCut hn d m T x W S) ∧
      IsClosedSubmanifold n (tailFixedReferenceCut hn d m T x W S) ∧ J.ideal.IsCoherent ∧
      J.cosupp=tailFixedReferenceCut hn d m T x W S ∧
      IsComplexAnalyticSubset (n := n) (tailFixedReferenceCut hn d m T x W S) := by
  obtain ⟨W,hxW,hbound,_hCne,hCadm,_hBadm,_hBcos⟩ := exists_original_reference_admissible_open hn d m h T hc x hx
  let b := (invFamily hn d).inv m T x
  let B := referenceMarked hn d m T x W
  have hC : IsClosedSubmanifold n (thresholdCut hn d m T b W) := hCadm.1
  have hBI : B.ideal=vanishingIdeal (n := n) (thresholdCut hn d m T b W) := rfl
  refine ⟨W,hxW,?_⟩
  intro Z S hcan
  obtain ⟨hN,hd,hI,hC',hcoh,_hbound'⟩ := actual_tail_induction (X := X) (Y := Y) hn d m h T b W B rfl rfl hBI hC hbound S hcan
  have hcos : (geoTransformAlong B (restrict W S)).cosupp=tailFixedReferenceCut hn d m T x W S := by
    change cosupport n (geoTransformAlong B (restrict W S)).N (geoTransformAlong B (restrict W S)).ideal
      (geoTransformAlong B (restrict W S)).d = _
    rw [hN,hd,hI,cosupport_one (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (hI ▸ hcoh) hg),univ_inter,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hC'.1]
    rfl
  exact ⟨hN,hd,hI,hC',hcoh,hcos,AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC'⟩

private theorem empty_vanishing_unit {A : CMfd.{u} n} :
    vanishingIdeal (n := n) (∅ : Set A)=IdealWeightPowers.unitIdeal n A := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun hg => hg.1,fun hg => ?_⟩)
  exact ⟨hg,Eventually.of_forall fun _ hx => hx.elim⟩

/-- Any ACTUAL original terminal canonical tail erases the SAME old auxiliary
cut. It does not make the post-erasure auxiliary tail an admissible history. -/
theorem exists_original_terminal_tail_reference_unit (hn : 0 < n) (d : ℕ)
    (m : MarkedIdeal n X) (h : IsInvDomain d m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn d).inv m) T) (x : Y)
    (hx : x ∈ (geoTransformAlong m T).cosupp) :
    ∃ W : Opens Y,x ∈ W ∧ ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z),
      IsCanonical m ((invFamily hn d).inv m) (T.append S) → IsGeoResolution m (T.append S) →
      (geoTransformAlong (referenceMarked hn d m T x W) (restrict W S)).ideal=
        IdealWeightPowers.unitIdeal n (openPreimage S W) ∧
      (geoTransformAlong (referenceMarked hn d m T x W) (restrict W S)).cosupp=∅ := by
  obtain ⟨W,hxW,hdict⟩ := exists_original_canonical_tail_reference_transform hn d m h T hc x hx
  refine ⟨W,hxW,?_⟩
  intro Z S hcan hres
  obtain ⟨_hN,_hd,hI,_hC,_hcoh,hcos,_hA⟩ := hdict S hcan
  have hcut : tailFixedReferenceCut hn d m T x W S=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hh : (p : Z) ∈ (geoTransformAlong m (T.append S)).cosupp := hp.1
    rw [hres.2] at hh
    exact hh
  refine ⟨?_,hcos.trans hcut⟩
  rw [hI,hcut,empty_vanishing_unit (A := CMfd.of (n := n) (openPreimage S W))]

end
end Hironaka.HironakaOriginalReferenceValueCanonicalTailTransform
