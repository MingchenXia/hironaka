/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFullCutGlobalSuperlevels
import Hironaka.Blowup.BlowupExistence
/-! Literal finite positive FULL levels are actual upper admissible centres
before CAN. Real geometric zero-dimensional exceptions precede all centre
fields and actual analytic blowup construction. Top levels remain separate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalOrderCutFiniteLevelCentres
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  GeneralValue GeneralCompare GeneralCanonicalTail CanonicalCentres ResolutionDriver
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  StepOneValue InvDomainTowerAlong HironakaOriginalFiniteOrderCutCompanionTests
  HironakaOriginalFiniteFullCutSmoothHistory HironakaGeneralTwoAnalyticSuperlevels
  HironakaOneDimensionalCanonicalSuperlevels AnalyticDimensionBasics ResolutionInvariantDriver
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The actual finite FULL level cannot meet the genuine SPECIAL complement
of the internally constructed geometric zero-dimensional exception. -/
theorem exists_dimzero_exception_containing_finite_full_level (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsOrderCutTower M T) (q : ℕ) (hq : 0<q) (s : ℕ) (a : ValTy (d+1)) :
    ∃ Z : Set Y,IsComplexAnalyticSubset (n := n) Z ∧ DimLE (n := n) Z 0 ∧
      {y | y∈(geoTransformAlong M T).cosupp ∧ (invFamily hn (d+2)).inv M T y=
        toLex (q,toLex (Sum.inr
          ((toLex (s,(a : WithTop (ValTy (d+1)))) : ℕ ×ₗ WithTop (ValTy (d+1))) :
            WithTop (ℕ ×ₗ WithTop (ValTy (d+1))))))}⊆Z := by
  have hTest := orderCutTower_geoTest M T hT
  obtain ⟨Z,hZ,hdZ,_hOrder,_hRun,_hBoundary,hSpecial⟩ :=
    exists_analytic_dimzero_positive_history_exception hn M hM T hTest q hq
  refine ⟨Z,hZ,hdZ,?_⟩
  intro y hy
  by_contra hyZ
  have hyq : nmOrd (geoTransformAlong M T) y=q := congrArg (fun v : ValTy (d+2) => (ofLex v).1) hy.2
  let r := StepOneRegime.regimeRun (OrdRegime M q) T y
  let rf : Fin (T.length+1) := ⟨r,Nat.lt_succ_of_le (StepOneRegime.regimeRun_le_length _ T y)⟩
  let H := head T r
  let S := tail T r
  let W := ordMask (geoTransformAlong M H) q
  let J := compAt M q H
  let R := restrict W S
  have hMask : S.proj y∈W := (proj_tail_mem_ordMask hn hM T hTest hy.1 hyq).2
  let p : openPreimage S W := ⟨y,hMask⟩
  obtain ⟨hH,hS⟩ := (isGeoTestTower_iff_head_tail M T r).mp hTest
  have hHead := isInvDomain_geoTransformAlong hM H hH
  have hJ : IsInvDomain 2 J := isInvDomain_compAt hn hq H hHead
  have hComp := orderCutTower_current_companion_test hn M hM T hT q hq y
  have hDict := mem_cosupp_compAt_iff hn hM hq H S hH hS hComp p
  rw [←geoTransformAlong_head_tail M T r] at hDict
  have hCos : p∈(geoTransformAlong J R).cosupp := hDict.mpr ⟨hy.1,hyq⟩
  have he := HomogenizedIdealAlongTower.coeff_homAlong_wEquiv
    (X := CMfd.of (n := n) W) J hJ.isWellFormed.isClosedSubmanifold_N
    hJ.isWellFormed.isCoherent hJ.one_le_d
  have hBar : IsGeoTestTower (barMarked J) R := (he.2 R).1.mpr hComp
  have hpBar : p∈(geoTransformAlong (barMarked J) R).cosupp := by
    rw [(he.2 R).2 hBar]
    exact hCos
  have hsp : IsSpecial J R p := by
    by_contra hnot
    exact hyZ (hSpecial rf p hpBar hnot)
  have hStep : Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) J R p=
      toLex (level J R p,(⊤ : WithTop (ValTy (d+1)))) :=
    Seq.StepOneValueMasked.stepOneInvL_of_isSpecial (invFamily hn (d+1)) J
      (StepOneValueMasked.lowerMarkedM J) R hsp
  let lower := fun {A : CMfd.{u} n} (K : MarkedIdeal n A) {B : CMfd.{u} n}
    (Q : BlowupTower A B) (z : B) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) K Q z
  have hValue : (invFamily hn (d+2)).inv M T y=
      toLex (q,toLex (Sum.inr
          ((toLex (level J R p,(⊤ : WithTop (ValTy (d+1)))) : ℕ ×ₗ WithTop (ValTy (d+1))) :
            WithTop (ℕ ×ₗ WithTop (ValTy (d+1)))))) := by
    change genInv lower M T y=_
    rw [genInv_of_nmOrd_ne_zero lower M T hyq (Nat.ne_of_gt hq),genLowerValue_eq_of_mem lower M hMask]
    exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy (d+1)) =>
      toLex (q,toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy (d+1))))))) hStep
  have h := congrArg (fun v : ValTy (d+2) => (ofLex v).2) (hy.2.symm.trans hValue)
  simp only [ofLex_toLex] at h
  have hh := congrArg ofLex h
  simp only [ofLex_toLex,Sum.inr.injEq] at hh
  have hpairs := WithTop.coe_injective hh
  have ha := congrArg (fun v : ℕ ×ₗ WithTop (ValTy (d+1)) => (ofLex v).2) hpairs
  exact WithTop.coe_ne_top ha

/-- Every literal finite positive FULL level is actual analytic dimension zero
and a genuine upper admissible centre, without assuming centre geometry. -/
theorem finite_full_level_actual_admissible (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsOrderCutTower M T) (q : ℕ) (hq : 0<q) (s : ℕ) (a : ValTy (d+1)) :
    let C : Set Y := {y | y∈(geoTransformAlong M T).cosupp ∧ (invFamily hn (d+2)).inv M T y=
      toLex (q,toLex (Sum.inr
        ((toLex (s,(a : WithTop (ValTy (d+1)))) : ℕ ×ₗ WithTop (ValTy (d+1))) :
          WithTop (ℕ ×ₗ WithTop (ValTy (d+1))))))}
    IsComplexAnalyticSubset (n := n) C ∧ DimLE (n := n) C 0 ∧
      (geoTransformAlong M T).IsAdmissibleCentre C := by
  obtain ⟨Z,hZ,hdZ,hCZ⟩ := exists_dimzero_exception_containing_finite_full_level hn d M hM T hT q hq s a
  have hCurrent := isInvDomain_geoTransformAlong hM T (orderCutTower_geoTest M T hT)
  have hSM := isClosedSubmanifold_subset_of_analytic_dimLE_zero hZ hdZ hCZ
  exact ⟨AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hSM,
    DimensionMonotone.DimLE.anti hZ hCZ hdZ,
    hSM,(fun _ h => h.1),hasNormalCrossings_subset_of_analytic_dimLE_zero hZ hdZ hCZ hCurrent.isWellFormed.isSNCDivisor⟩

/-- Genuine internally proved finite-level centre geometry and thinness
construct an actual next analytic blowup of the original history. -/
theorem exists_actual_finite_full_level_blowup (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsOrderCutTower M T) (q : ℕ) (hq : 0<q) (s : ℕ) (a : ValTy (d+1)) :
    let C : Set Y := {y | y∈(geoTransformAlong M T).cosupp ∧ (invFamily hn (d+2)).inv M T y=
      toLex (q,toLex (Sum.inr
        ((toLex (s,(a : WithTop (ValTy (d+1)))) : ℕ ×ₗ WithTop (ValTy (d+1))) :
          WithTop (ℕ ×ₗ WithTop (ValTy (d+1))))))}
    ∃ (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      IsGeoTestTower M (.step T C π hπ) ∧
      ((geoTransformAlong M T).geoTransform C π).IsWellFormed ∧
      NormalCrossings.IsSNCDivisor n ((geoTransformAlong M T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) := by
  let C : Set Y := {y | y∈(geoTransformAlong M T).cosupp ∧ (invFamily hn (d+2)).inv M T y=
      toLex (q,toLex (Sum.inr
        ((toLex (s,(a : WithTop (ValTy (d+1)))) : ℕ ×ₗ WithTop (ValTy (d+1))) :
          WithTop (ℕ ×ₗ WithTop (ValTy (d+1))))))}
  have hC := (finite_full_level_actual_admissible hn d M hM T hT q hq s a).2.2
  have hTest := orderCutTower_geoTest M T hT
  have hCurrent := isInvDomain_geoTransformAlong hM T hTest
  have hThin : interior C=∅ := eq_empty_of_subset_empty
    ((interior_mono hC.2.1).trans (interior_cosupp_eq_empty hCurrent).subset)
  obtain ⟨Z,π,hπ⟩ := exists_blowup C hC.1 hThin
  have hWF := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
    hCurrent.isWellFormed hC hπ
  exact ⟨Z,π,hπ,⟨hTest,hC⟩,hWF,hWF.isSNCDivisor⟩
end
end Hironaka.HironakaOriginalOrderCutFiniteLevelCentres
