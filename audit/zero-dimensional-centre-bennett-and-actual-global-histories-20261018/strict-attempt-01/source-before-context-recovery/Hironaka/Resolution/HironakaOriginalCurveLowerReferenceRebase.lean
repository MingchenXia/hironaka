/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCurveFullRebase
import Hironaka.Invariant.GeneralRepresentative
/-! Actual kept-contact and member lower references retain their whole
original curve FULL values under true relative-ideal rebasing, without CAN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCurveLowerReferenceRebase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  CanonicalCentres InvDomainTowerAlong InvDomainRebase GeneralValue GeneralRepresentative
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal
  HironakaOriginalCurveFullRebase StepOneCompare StepOneValue InvDomainMemberRestriction HomogenizedIdealAlong
  HomogenizedIdealAlongTower ContactIndependenceAlong TangentDirectionAlong
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen RestrictEmptyTower HomogenizedGlueingTower
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- Whole relative equivalence and actual curve rebasing supply genuine
new domain/TEST/cosupport before EVERY positive-depth numerical equality. -/
theorem curve_full_rebase_of_restrictEquiv (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    (P : BlowupTower X A) (T : BlowupTower A Y)
    (hPT : IsGeoTestTower M (P.append T)) (N : MarkedIdeal n A)
    (hEq : RestrictEquiv N (geoTransformAlong M P)) (hN : N.ideal.IsCoherent) :
    IsInvDomain 1 N ∧ IsGeoTestTower N T ∧
      (geoTransformAlong M (P.append T)).cosupp=(geoTransformAlong N T).cosupp ∧
      ∀ y∈(geoTransformAlong M (P.append T)).cosupp,∀ k : ℕ,
        (invFamily hn (k+1)).inv M (P.append T) y=(invFamily hn (k+1)).inv N T y := by
  obtain ⟨hP,hT⟩ := (isGeoTestTower_append_iff M P T).mp hPT
  have hMP := isInvDomain_geoTransformAlong hM P hP
  have hEq' := restrictEquiv_symm hEq
  have hDom := isInvDomain_of_restrictEquiv hMP hEq' hN
  have hW := RestrictEquiv.wEquiv hEq' hMP.isWellFormed.isClosedSubmanifold_N.1
    hMP.isWellFormed.isCoherent hN
  refine ⟨hDom,((hW.2 T).1).mp hT,?_,?_⟩
  · rw [geoTransformAlong_append]
    exact (hW.2 T).2 hT
  · intro y hy k
    rw [original_curve_full_append_rebase hn k M hM P T hPT y hy]
    exact genInv_congr
      (fun {V} J {Z} S p => Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J S p)
      hEq' hMP.isWellFormed.isClosedSubmanifold_N.1 hMP.isWellFormed.isCoherent hN T y

/-- Genuine coefficient/contact relative ideal geometry supplies the new
reference; actual lower TEST is retained and no lower CAN is required. -/
theorem contactKept_curve_full_rebase (hn : 0<n) (J : MarkedIdeal n X)
    (hJ : J.IsWellFormed) (hd : 1≤J.d) (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong J.N J.ideal J.d U u)
    (P : BlowupTower X A) (B : BlowupTower A Y)
    (hPB : IsGeoTestTower (barMarked J) (P.append B)) (W : Opens A)
    (hWU : (W : Set A)⊆openPreimage P U) (hW : CentresAvoid W B)
    (hDom : IsInvDomain 1 (contactKept J u P W))
    {Z : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) (openPreimage B W)) Z)
    (hTest : IsGeoTestTower (contactKept J u P W) ((restrict W B).append T)) :
    let N := contactKept J u (P.append B) (openPreimage B W)
    IsInvDomain 1 N ∧ IsGeoTestTower N T ∧
      (geoTransformAlong (contactKept J u P W) ((restrict W B).append T)).cosupp=
        (geoTransformAlong N T).cosupp ∧
      ∀ z∈(geoTransformAlong (contactKept J u P W) ((restrict W B).append T)).cosupp,
        ∀ k : ℕ,(invFamily hn (k+1)).inv (contactKept J u P W) ((restrict W B).append T) z=
          (invFamily hn (k+1)).inv N T z := by
  have hEq := ContactStageRebase.restrictEquiv_restrictedCoeffHomAlong_rebase
    J hJ.isClosedSubmanifold_N hJ.isCoherent hd U hu P B hPB W hWU hW
  have hJN : IsClosedSubmanifold n (barMarked J).N := hJ.isClosedSubmanifold_N
  have hJC := isCoherent_barMarked J hJ.isClosedSubmanifold_N hJ.isCoherent
  obtain ⟨hNT,hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJC (P.append B) hPB
  have hNewCoherent : (contactKept J u (P.append B) (openPreimage B W)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val (isCoherent_coeffMarkedAlong hcT hNT)
  exact curve_full_rebase_of_restrictEquiv hn (contactKept J u P W) hDom
    (restrict W B) T hTest _ hEq hNewCoherent

/-- Genuine original member geometry supplies the actual new reference
before the noncanonical numerical curve FULL rebase. -/
theorem memberRestrict_curve_full_rebase (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hd : 1≤M.d) {E₀ : List (Set X)}
    (hE₀ : ∀ H∈E₀,H∈M.E) (B : BlowupTower X A) (hB : IsGeoTestTower M B)
    (W : Opens X) (hW : CentresAvoid W B) (p : openPreimage B W)
    (hDom : IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : W → X)
      (memberRestrict M (membersThrough M.E E₀ (B.proj p)))))
    (T : BlowupTower (CMfd.of (n := n) (openPreimage B W)) Y)
    (hTest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → X)
      (memberRestrict M (membersThrough M.E E₀ (B.proj p)))) ((restrict W B).append T)) :
    let N := MarkedIdeal.pullback (Subtype.val : openPreimage B W → A)
      (memberRestrict (geoTransformAlong M B)
        (membersThrough (geoTransformAlong M B).E (E₀.map (strictAlong B)) p))
    IsInvDomain 1 N ∧ IsGeoTestTower N T ∧
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X)
        (memberRestrict M (membersThrough M.E E₀ (B.proj p)))) ((restrict W B).append T)).cosupp=
        (geoTransformAlong N T).cosupp ∧
      ∀ y∈(geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X)
        (memberRestrict M (membersThrough M.E E₀ (B.proj p)))) ((restrict W B).append T)).cosupp,
        ∀ k : ℕ,(invFamily hn (k+1)).inv (MarkedIdeal.pullback (Subtype.val : W → X)
          (memberRestrict M (membersThrough M.E E₀ (B.proj p)))) ((restrict W B).append T) y=
            (invFamily hn (k+1)).inv N T y := by
  have hEq := restrictEquiv_memberRestrict_rebase hn hM hd hE₀ B hB W hW p
  have hMB := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM B hB
  have hCoherent := (MarkedIdealRestrictOpen.IsWellFormed.pullback_val
    (isWellFormed_memberRestrict hn hMB
      (membersThrough (geoTransformAlong M B).E (E₀.map (strictAlong B)) p))
    (openPreimage B W)).isCoherent
  exact curve_full_rebase_of_restrictEquiv hn _ hDom (restrict W B) T hTest _ hEq hCoherent

end
end Hironaka.HironakaOriginalCurveLowerReferenceRebase
