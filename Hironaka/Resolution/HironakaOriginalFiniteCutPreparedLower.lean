/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteCutInheritedLowerValues
/-! Real next frozen lower TEST, current DOMAIN and WHOLE cosupport after
original noncanonical finite cut preparation; numerical maximum is not admissibility. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFiniteCutPreparedLower
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen CanonicalCentres
  HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdealRestriction
  StepOneLowerDomain StepOneValue StepOneValueMasked StepOneRegime StepOneCanonicalTail
  StepOneCompare MemberRestrictAdmissible InvDomainTowerAlong HironakaOriginalFrozenRecursiveLower
  HironakaOriginalFiniteLevelCutLowerTests HironakaOriginalFiniteStepOneCutMaskAvoidance
  HironakaOriginalFiniteCutInheritedLowerValues
open ResolutionInvariantSpec (IsInvDomain)
open ResolutionDriver (maxLocus)
variable {n : ℕ} {X A Y Z : CMfd.{u} n}

/-- True old lower TEST and actual trace cosupport give genuine geometry
of the SAME next lower TEST. No numerical maximum substitutes for admissibility. -/
private theorem actual_next_lower_test (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hd : 1≤M.d) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y) (s : ℕ) (y₀ : A)
    (hHead : y₀∈(geoTransformAlong (barMarked M) H).cosupp)
    (hMask : y₀∈lowerMask M s H y₀)
    (hOld : IsGeoTestTower (lowerMarkedM M s H y₀) (restrict (lowerMask M s H y₀) S))
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hUpper : IsGeoTestTower (barMarked M) (H.append (.step S C π hπ)))
    (hTrace : ∀ q : openPreimage S (lowerMask M s H y₀),q.val∈C →
      q∈(geoTransformAlong (lowerMarkedM M s H y₀) (restrict (lowerMask M s H y₀) S)).cosupp) :
    IsGeoTestTower (lowerMarkedM M s H y₀) (restrict (lowerMask M s H y₀) (.step S C π hπ)) := by
  cases s with
  | zero => exact (isGeoTestTower_cosupp_lowerMarkedB M hM hd hmax H (.step S C π hπ) hUpper hHead).1
  | succ s =>
    have hSplit := (isGeoTestTower_append_iff (barMarked M) H (.step S C π hπ)).mp hUpper
    have hBar := StepOneLowerDomain.isWellFormed_barMarked M hM
    have hHeadWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hBar H hSplit.1
    have hRestricted := isGeoTestTower_restrict (lowerMask M (s+1) H y₀)
      hHeadWF.isClosedSubmanifold_N hHeadWF.isCoherent (.step S C π hπ) hSplit.2
    have hAdm := hRestricted.2
    rw [geoTransformAlong_restrict (lowerMask M (s+1) H y₀) hHeadWF.isClosedSubmanifold_N
      hHeadWF.isCoherent S hSplit.2.1,←geoTransformAlong_append] at hAdm
    have hOldUpper : IsGeoTestTower (barMarked M) (H.append S) :=
      (isGeoTestTower_append_iff _ H S).mpr ⟨hSplit.1,hSplit.2.1⟩
    have hTraceAdm : (geoTransformAlong (lowerMarkedM M (s+1) H y₀)
        (restrict (lowerMask M (s+1) H y₀) S)).IsAdmissibleCentre
        ((Subtype.val : openPreimage S (lowerMask M (s+1) H y₀) → Y) ⁻¹' C) := by
      apply (isAdmissibleCentre_lowerMarked_succ_iff M hM hn H S hOldUpper hMask hOld _).mpr
      refine ⟨hAdm,?_⟩
      intro q hq
      exact ((mem_cosupp_lowerMarked_succ_iff M hM hn H S hOldUpper hMask hOld q).mp (hTrace q hq)).2
    exact ⟨hOld,hTraceAdm⟩

/-- ONLY original finite preparation and a genuine next whole cut construct
actual frozen lower geometry, new whole cosupport and the entire lower maximum. -/
theorem finite_cut_prepared_lower_data (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hT : IsStepOneCutTower hn (d+1) M T)
    (y : Y) (hy : y∈(geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x∈(geoTransformAlong M T).cosupp,∀ c∈C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) M T c) :
    let K := lowerAt M T y
    let R := lowerTailAt M T y
    let RNext := restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ)
    IsInvDomain 1 K ∧ IsGeoTestTower K R ∧ IsGeoTestTower K RNext ∧
      IsInvDomain 1 (geoTransformAlong K RNext) ∧
      (∀ z : openPreimage (.step (tail T (runAt M T y)) C π hπ) (maskAt M T y),
        z∈(geoTransformAlong K RNext).cosupp ↔
          z.val∈(geoTransformAlong M (.step T C π hπ)).cosupp ∧
            level M (.step T C π hπ) z.val=level M T y) ∧
      (Subtype.val : patchAt M T y → Y) ⁻¹' C⊆
        maxLocus ((invFamily hn (d+1)).inv K R) (geoTransformAlong K R).cosupp := by
  have hLevel := stepOneCutTower_levelCut hn M T hT
  have hUpper := levelCutTower_geoTest M T hLevel
  obtain ⟨hD,hOld,_hCur,hMask,_hPoint,_hDict⟩ :=
    levelCutTower_current_lower_data hn M hM hmax T hLevel y hy hns
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d
  have hBar := (he.2 T).1.mpr hUpper
  have hyBar : y∈(geoTransformAlong (barMarked M) T).cosupp := by rw [(he.2 T).2 hBar];exact hy
  obtain ⟨hReg,hHead⟩ := stepRegime_and_mem_cosupp_head M hM.isWellFormed T hBar hyBar hns
  have hBarNext : IsGeoTestTower (barMarked M) (.step T C π hπ) := (he.2 _).1.mpr ⟨hUpper,hC⟩
  let r := runAt M T y
  let H := head T r
  let S := tail T r
  have hWhole : H.append (.step S C π hπ)=.step T C π hπ := by rw [BlowupTower.append_step,head_append_tail]
  have hTrace := finite_cut_inherited_lower_values hn d M hM hmax T hT y hy hns C hC hCuts
  have hNext := actual_next_lower_test hn M hM.isWellFormed hM.one_le_d hmax H S (level M T y)
    (S.proj y) hHead hMask hOld C π hπ (by rw [hWhole];exact hBarNext) (fun q hq => (hTrace q hq).1)
  refine ⟨hD,hOld,hNext,isInvDomain_geoTransformAlong hD _ hNext,?_,
    finite_cut_lower_maximum_inclusion hn d M hM hmax T hT y hy hns C hC hCuts⟩
  intro z
  have hh := mem_cosupp_lowerMarkedM_iff M hM.isWellFormed hM.one_le_d hn hmax H
    (.step S C π hπ) (by rw [hWhole];exact hBarNext) hHead hReg.1 hMask hNext z
  rw [hWhole,(he.2 _).2 hBarNext] at hh
  exact hh

end
end Hironaka.HironakaOriginalFiniteCutPreparedLower
