/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteCutFixedLowerValues
/-! Actual original finite cuts, without CAN, supply the entire computed
lower FULL cut before future geometric preparation. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFiniteCutInheritedLowerValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres HomogenizedIdealAlong CoefficientIdealRestriction StepOneValue StepOneValueMasked StepOneRegime
  StepOneCanonicalTail StepOneMaskTower HironakaOriginalFrozenRecursiveLower
  HironakaOriginalFiniteLevelCutLowerTests HironakaOriginalFiniteStepOneCutMaskAvoidance
  HironakaOriginalFiniteCutFixedLowerValues
open ResolutionInvariantSpec (IsInvDomain)
open ResolutionDriver (maxLocus)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Genuine lower geometry and actual fixed-reference values precede lower
whole-cut reflection; no original or lower canonicality is supplied. -/
theorem finite_cut_inherited_lower_values (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hT : IsStepOneCutTower hn (d+1) M T)
    (y : Y) (hy : y∈(geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (hCuts : ∀ x∈(geoTransformAlong M T).cosupp,∀ c∈C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) M T c) :
    ∀ c : patchAt M T y,c.val∈C →
      c∈(geoTransformAlong (lowerAt M T y) (lowerTailAt M T y)).cosupp ∧
      ∀ p : patchAt M T y,p∈(geoTransformAlong (lowerAt M T y) (lowerTailAt M T y)).cosupp →
        (invFamily hn (d+1)).inv (lowerAt M T y) (lowerTailAt M T y) p≤
          (invFamily hn (d+1)).inv (lowerAt M T y) (lowerTailAt M T y) c := by
  have hLevel := stepOneCutTower_levelCut hn M T hT
  have hUpper := levelCutTower_geoTest M T hLevel
  obtain ⟨_hDom,_hTest,_hCurrent,_hMask,_hPoint,hDict⟩ :=
    levelCutTower_current_lower_data hn M hM hmax T hLevel y hy hns
  have he := HomogenizedIdealAlongTower.coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar := (he.2 T).1.mpr hUpper
  have hyBar : y∈(geoTransformAlong (barMarked M) T).cosupp := by rw [(he.2 T).2 hBar];exact hy
  obtain ⟨hReg,_hHead⟩ := stepRegime_and_mem_cosupp_head M hM.isWellFormed T hBar hyBar hns
  intro c hc
  have hGe : level M T y≤level M T c := by
    have hh := Prod.Lex.le_iff.mp (hCuts y hy c hc)
    rw [Seq.StepOneValueMasked.stepOneInvL_fst,Seq.StepOneValueMasked.stepOneInvL_fst] at hh
    exact hh.elim (fun h => h.le) (fun h => h.1.le)
  have hLe : level M T c≤level M T y := by
    have hh := level_le_of_mem_lowerMask M (fun A hA => hM.isWellFormed.isSNCDivisor.1 A hA)
      (head T (runAt M T y)) (tail T (runAt M T y)) hReg.1 c.property
    rwa [head_append_tail] at hh
  have hcCos := (hDict c).mpr ⟨hC.2.1 hc,le_antisymm hLe hGe⟩
  refine ⟨hcCos,?_⟩
  intro p hp
  have hpOriginal := ((hDict p).mp hp).1
  have hpValue := finite_cut_stepone_eq_fixed_lower hn d M hM hmax T hT y hy hns p hp
  have hcValue := finite_cut_stepone_eq_fixed_lower hn d M hM hmax T hT y hy hns c hcCos
  have hBound := hCuts p hpOriginal c hc
  rw [hpValue,hcValue] at hBound
  rcases Prod.Lex.le_iff.mp hBound with hlt|⟨_,hle⟩
  · exact False.elim ((lt_irrefl _) hlt)
  · exact WithTop.coe_le_coe.mp hle

/-- Inclusion in the ORIGINAL whole lower maximum; no centre equality or next CAN. -/
theorem finite_cut_lower_maximum_inclusion (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y)
    (hT : IsStepOneCutTower hn (d+1) M T)
    (y : Y) (hy : y∈(geoTransformAlong M T).cosupp) (hns : ¬IsSpecial M T y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (hCuts : ∀ x∈(geoTransformAlong M T).cosupp,∀ c∈C,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) M T x≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) M T c) :
    (Subtype.val : patchAt M T y → Y) ⁻¹' C⊆
      maxLocus ((invFamily hn (d+1)).inv (lowerAt M T y) (lowerTailAt M T y))
        (geoTransformAlong (lowerAt M T y) (lowerTailAt M T y)).cosupp :=
  finite_cut_inherited_lower_values hn d M hM hmax T hT y hy hns C hC hCuts

end
end Hironaka.HironakaOriginalFiniteCutInheritedLowerValues
