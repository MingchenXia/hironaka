/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFullCutFrozenCompanion
import Hironaka.Resolution.HironakaGeneralTwoAnalyticSuperlevels
/-! Actual whole global positive FULL superlevels on genuine original
full-cut histories, without CAN or analytic/closed locus certificates. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFullCutPositiveGlobalSuperlevels
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  GeneralValue GeneralCompare GeneralCanonicalTail NonmonomialOrderLocal NonmonomialOrderRegime
  NonmonomialOrderTail StepOneValue CanonicalCentres InvDomainTowerAlong
  HironakaOriginalFullCutFrozenCompanion HironakaOriginalFrozenCompanionPresentation
  HironakaOriginalFullCutCompanionHistory HironakaOriginalFiniteOrderCutCompanionTests
  HironakaOriginalFiniteFullCutSmoothHistory CodimOneSupportAlong GlobalComponents BoundaryCount
  HironakaGeneralTwoAnalyticSuperlevels HironakaOriginalCompanionChronologicalBoundaryAnalytic
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Genuine actual open analytic patches and actual order upper semicontinuity
supply global closedness; no canonical usc or closed locus is an input. -/
theorem isClosed_positive_full_superlevel (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsFullCutTower hn d M T) (q : ℕ) (hq : 0<q)
    (β : WithTop (ℕ ×ₗ WithTop (ValTy (d+1)))) :
    IsClosed {y | y∈(geoTransformAlong M T).cosupp ∧
      toLex (q,toLex (Sum.inr β))≤(invFamily hn (d+2)).inv M T y} := by
  let L : Set Y := {y | y∈(geoTransformAlong M T).cosupp ∧
    toLex (q,toLex (Sum.inr β))≤(invFamily hn (d+2)).inv M T y}
  have hTest := orderCutTower_geoTest M T (fullCutTower_orderCut hn d M T hT)
  have hCurrent := isInvDomain_geoTransformAlong hM T hTest
  have hA := isComplexAnalyticSubset_cosupport_along hCurrent.isWellFormed.isCoherent
    hCurrent.isWellFormed.isClosedSubmanifold_N hCurrent.one_le_d
  change IsClosed L
  rw [←isOpen_compl_iff,isOpen_iff_mem_nhds]
  intro x hx
  by_cases hxA : x∈(geoTransformAlong M T).cosupp
  · rcases lt_trichotomy (nmOrd (geoTransformAlong M T) x) q with hlo|heq|hhi
    · have hb := eventually_nmOrd_le hn hCurrent.isWellFormed hCurrent.isNonzeroAlongAt
        ((geoTransformAlong M T).cosupp_subset_N hxA)
      filter_upwards [hb] with y hy
      intro hyL
      have hLex := Prod.Lex.le_iff.mp hyL.2
      change q<nmOrd (geoTransformAlong M T) y ∨
        q=nmOrd (geoTransformAlong M T) y ∧ _ at hLex
      have hge : q≤nmOrd (geoTransformAlong M T) y :=
        hLex.elim (fun h => h.le) (fun h => h.1.le)
      exact (not_le.mpr (lt_of_le_of_lt hy hlo)) hge
    · have hqx : orderAt M T x=q := heq
      have hpos : 0<orderAt M T x := by rw [hqx];exact hq
      have hpx := (full_cut_frozen_companion_data hn d M hM T hT x hxA hpos).1
      have hClosed := (isComplexAnalyticSubset_full_cut_frozen_superlevel hn d M hM T hT x hxA hpos β).isClosed
      rw [hqx] at hClosed
      have hxU : (⟨x,hpx⟩ : patchAt M T x)∉(Subtype.val : patchAt M T x → Y) ⁻¹' L := hx
      have hNhd : ∀ᶠ z : patchAt M T x in 𝓝 (⟨x,hpx⟩ : patchAt M T x),z.val∉L :=
        hClosed.isOpen_compl.mem_nhds hxU
      exact (eventually_nhds_val_iff (patchAt M T x) (x := ⟨x,hpx⟩) (P := fun y => y∉L)).mpr hNhd
    · exfalso
      apply hx
      refine ⟨hxA,?_⟩
      apply Prod.Lex.le_iff.mpr
      exact Or.inl hhi
  · filter_upwards [hA.isClosed.isOpen_compl.mem_nhds hxA] with y hy
    exact fun hyL => hy hyL.1

/-- True geometric finite-history exceptions and internally supplied own
companion TEST give component constancy at EVERY actual lower depth. -/
theorem exists_positive_full_component_dictionary (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsOrderCutTower M T) (q : ℕ) (hq : 0<q)
    (β : WithTop (ℕ ×ₗ WithTop (ValTy (d+1)))) :
    ∃ Z : Set Y,IsComplexAnalyticSubset (n := n) Z ∧ AnalyticDimensionBasics.DimLE (n := n) Z 0 ∧
      ∀ B∈globalComponents (n := n) (geoTransformAlong M T).cosupp,
        ∀ x∈B \ Z,∀ y∈B \ Z,
          (toLex (q,toLex (Sum.inr β))≤(invFamily hn (d+2)).inv M T x ↔
            toLex (q,toLex (Sum.inr β))≤(invFamily hn (d+2)).inv M T y) := by
  have hTest := orderCutTower_geoTest M T hT
  obtain ⟨Z,hZ,hdZ,hOrder,hRun,hBoundary,hSpecial⟩ :=
    exists_analytic_dimzero_positive_history_exception hn M hM T hTest q hq
  refine ⟨Z,hZ,hdZ,?_⟩
  have hCurrent := isInvDomain_geoTransformAlong hM T hTest
  have hA := isComplexAnalyticSubset_cosupport_along hCurrent.isWellFormed.isCoherent
    hCurrent.isWellFormed.isClosedSubmanifold_N hCurrent.one_le_d
  let lower := fun {A : CMfd.{u} n} (J : MarkedIdeal n A) {B : CMfd.{u} n}
    (S : BlowupTower A B) (z : B) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) J S z
  have hValue : ∀ z∈(geoTransformAlong M T).cosupp,z∉Z → nmOrd (geoTransformAlong M T) z=q →
      (invFamily hn (d+2)).inv M T z=
        toLex (q,toLex (Sum.inr ((toLex
          (boundaryCount (chronologicalMembers M T (StepOneRegime.regimeRun (OrdRegime M q) T z)) z,
            (⊤ : WithTop (ValTy (d+1)))) : ℕ ×ₗ WithTop (ValTy (d+1))) :
            WithTop (ℕ ×ₗ WithTop (ValTy (d+1)))))) := by
    intro z hzA hzZ hzq
    let r := StepOneRegime.regimeRun (OrdRegime M q) T z
    let rf : Fin (T.length+1) := ⟨r,Nat.lt_succ_of_le (StepOneRegime.regimeRun_le_length _ T z)⟩
    let H := head T r
    let S := tail T r
    let W := ordMask (geoTransformAlong M H) q
    let J := compAt M q H
    let R := restrict W S
    have hMask : S.proj z∈W := (proj_tail_mem_ordMask hn hM T hTest hzA hzq).2
    let p : openPreimage S W := ⟨z,hMask⟩
    obtain ⟨hH,hS⟩ := (isGeoTestTower_iff_head_tail M T r).mp hTest
    have hHead := isInvDomain_geoTransformAlong hM H hH
    have hJ : IsInvDomain 2 J := isInvDomain_compAt hn hq H hHead
    have hComp := orderCutTower_current_companion_test hn M hM T hT q hq z
    have hDict := mem_cosupp_compAt_iff hn hM hq H S hH hS hComp p
    rw [←geoTransformAlong_head_tail M T r] at hDict
    have hCos : p∈(geoTransformAlong J R).cosupp := hDict.mpr ⟨hzA,hzq⟩
    have he := HomogenizedIdealAlongTower.coeff_homAlong_wEquiv
      (X := CMfd.of (n := n) W) J hJ.isWellFormed.isClosedSubmanifold_N
      hJ.isWellFormed.isCoherent hJ.one_le_d
    have hBar : IsGeoTestTower (barMarked J) R := (he.2 R).1.mpr hComp
    have hpBar : p∈(geoTransformAlong (barMarked J) R).cosupp := by
      rw [(he.2 R).2 hBar]
      exact hCos
    have hsp : IsSpecial J R p := by
      by_contra hnot
      exact hzZ (hSpecial rf p hpBar hnot)
    have hStep : Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) J R p=
        toLex (level J R p,(⊤ : WithTop (ValTy (d+1)))) :=
      Seq.StepOneValueMasked.stepOneInvL_of_isSpecial (invFamily hn (d+1)) J
        (StepOneValueMasked.lowerMarkedM J) R hsp
    have hLevel := actualCompanionLevel_eq_chronologicalBoundaryCount M hM T hTest q r p
    have hStep' := hStep.trans (congrArg (fun a : ℕ => toLex (a,(⊤ : WithTop (ValTy (d+1))))) hLevel)
    change genInv lower M T z=_
    rw [genInv_of_nmOrd_ne_zero lower M T hzq (Nat.ne_of_gt hq),genLowerValue_eq_of_mem lower M hMask]
    exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy (d+1)) =>
      toLex (q,toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy (d+1))))))) hStep'
  intro B hB x hx y hy
  have ho0 : q≤nmOrd (geoTransformAlong M T) x ↔ q≤nmOrd (geoTransformAlong M T) y := by
    simpa using hOrder B hB x hx y hy 0
  have ho1 : q+1≤nmOrd (geoTransformAlong M T) x ↔ q+1≤nmOrd (geoTransformAlong M T) y := by
    simpa using hOrder B hB x hx y hy 1
  by_cases hxlo : nmOrd (geoTransformAlong M T) x<q
  · have hylo : nmOrd (geoTransformAlong M T) y<q :=
      Nat.lt_of_not_ge (fun h => (not_le.mpr hxlo) (ho0.mpr h))
    have hxl : (invFamily hn (d+2)).inv M T x<toLex (q,toLex (Sum.inr β)) := by
      apply Prod.Lex.lt_iff.mpr
      exact Or.inl hxlo
    have hyl : (invFamily hn (d+2)).inv M T y<toLex (q,toLex (Sum.inr β)) := by
      apply Prod.Lex.lt_iff.mpr
      exact Or.inl hylo
    exact iff_of_false (not_le.mpr hxl) (not_le.mpr hyl)
  by_cases hxhi : q<nmOrd (geoTransformAlong M T) x
  · have hyhi : q<nmOrd (geoTransformAlong M T) y := ho1.mp (Nat.succ_le_of_lt hxhi)
    have hxl : toLex (q,toLex (Sum.inr β))≤(invFamily hn (d+2)).inv M T x := by
      apply Prod.Lex.le_iff.mpr
      exact Or.inl hxhi
    have hyl : toLex (q,toLex (Sum.inr β))≤(invFamily hn (d+2)).inv M T y := by
      apply Prod.Lex.le_iff.mpr
      exact Or.inl hyhi
    exact iff_of_true hxl hyl
  have hxq : nmOrd (geoTransformAlong M T) x=q := by omega
  have hyq : nmOrd (geoTransformAlong M T) y=q := by
    have hylt : ¬q+1≤nmOrd (geoTransformAlong M T) y := by
      intro h
      have := ho1.mpr h
      omega
    have := ho0.mp (by omega : q≤nmOrd (geoTransformAlong M T) x)
    omega
  have hr := hRun B hB x hx y hy
  have hc : boundaryCount (chronologicalMembers M T (StepOneRegime.regimeRun (OrdRegime M q) T x)) x=
      boundaryCount (chronologicalMembers M T (StepOneRegime.regimeRun (OrdRegime M q) T x)) y :=
    MemberInterLocusAlong.boundaryCount_eq_of_forall_iff (fun H hH => hBoundary B hB x hx y hy H (List.mem_of_mem_take hH))
  rw [hValue x (subset_of_mem_globalComponents hA hB hx.1) hx.2 hxq,
    hValue y (subset_of_mem_globalComponents hA hB hy.1) hy.2 hyq,←hr,hc]

/-- Actual global closedness and actual geometric component data precede
analytic descent for the ENTIRE original positive FULL superlevel. -/
theorem isComplexAnalyticSubset_positive_full_superlevel (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsFullCutTower hn d M T) (q : ℕ) (hq : 0<q)
    (β : WithTop (ℕ ×ₗ WithTop (ValTy (d+1)))) :
    IsComplexAnalyticSubset (n := n) {y | y∈(geoTransformAlong M T).cosupp ∧
      toLex (q,toLex (Sum.inr β))≤(invFamily hn (d+2)).inv M T y} := by
  have hOrder := fullCutTower_orderCut hn d M T hT
  have hTest := orderCutTower_geoTest M T hOrder
  have hCurrent := isInvDomain_geoTransformAlong hM T hTest
  have hA := isComplexAnalyticSubset_cosupport_along hCurrent.isWellFormed.isCoherent
    hCurrent.isWellFormed.isClosedSubmanifold_N hCurrent.one_le_d
  have hClosed := isClosed_positive_full_superlevel hn d M hM T hT q hq β
  obtain ⟨Z,hZ,hdZ,hDict⟩ := exists_positive_full_component_dictionary hn d M hM T hOrder q hq β
  apply isComplexAnalyticSubset_of_component_dictionary hA hClosed (fun _ h => h.1) hZ hdZ
  intro B hB x hx y hy
  exact and_congr (iff_of_true (subset_of_mem_globalComponents hA hB hx.1)
    (subset_of_mem_globalComponents hA hB hy.1)) (hDict B hB x hx y hy)

end
end Hironaka.HironakaOriginalFullCutPositiveGlobalSuperlevels
