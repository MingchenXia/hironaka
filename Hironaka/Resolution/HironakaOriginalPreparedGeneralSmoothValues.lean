/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedCompanionSmoothDiagram
import Hironaka.Resolution.HironakaOriginalGivenSmoothStepOneValues
/-! Unchanged FULL GENERAL values after ONE actual possibly noncanonical
preparation step in original carrier-bound 2, on the SAME given source history. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedGeneralSmoothValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres GeneralValue GeneralCompare NonmonomialOrderLocal NonmonomialOrderRegime
  NonmonomialOrderTail StepOneRegime HomogenizedIdealAlong
  HironakaOriginalPreparedCompanionSmoothDiagram HironakaOriginalGivenSmoothStepOneValues
  HironakaOriginalSimultaneousHSAdmissibleCentre HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionActualFamilyMonomialLeaf HironakaSmoothSubmersionCanonicalValueDimensionShift
  HironakaHolomorphicJetChartInvariance ResolutionDriver
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m : ℕ} {X D Z : CMfd.{u} n} {Y Z' : CMfd.{u} m}

private theorem domain_two_at_depth (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (d : ℕ) :
    IsInvDomain (d+2) M := by
  refine ⟨hM.isWellFormed,?_,hM.one_le_d,hM.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨j,hj,hreg⟩ := hM.dimLE x hx
  exact ⟨j,by omega,hreg⟩

/-- Actual CURRENT companion TEST and SAME GIVEN lower Cartesian history
precede the real unchanged positive GENERAL substitution. -/
theorem prepared_original_general_smooth_values
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (T : BlowupTower X D) (hc : IsCanonical M ((invFamily hn 2).inv M) T)
    (C : Set D) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → D) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ y ∈ (geoTransformAlong M T).cosupp,0<nmOrd (geoTransformAlong M T) y →
      ∀ c ∈ C,(invFamily hn 2).inv M T y≤(invFamily hn 2).inv M T c)
    {f : Y → X} {g : Z' → Z} {Q : BlowupTower Y Z'}
    (h : IsActualTowerPullback f Q (.step T C π hπ) g)
    (z : Z') (hz : g z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp) (d : ℕ) :
    (invFamily hm ((m-n)+d+2)).inv (markedPullback (m := m) f M) Q z=
      familyDimensionMap (m-n) (d+2) ((invFamily hn (d+2)).inv M (.step T C π hπ) (g z)) := by
  let P : BlowupTower X Z := .step T C π hπ
  have hT := (invFamily hn 2).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  have hP : IsGeoTestTower M P := ⟨hT,hC⟩
  by_cases hZero : nmOrd (geoTransformAlong M P) (g z)=0
  · exact (IsActualTowerPullback.actual_family_monomial_leaf hn hm h M
      (domain_two_at_depth M hM d) hP z hZero).2
  have hPos : 0<nmOrd (geoTransformAlong M P) (g z) := Nat.pos_of_ne_zero hZero
  obtain ⟨hOrd,hRun,hp,hp',p,q,hRecord,hCart,_hCoord,hPoint,hDom,hMax,hTest,
    _hCurrent,hTargetPoint,_hSourceDom,_hSourceTest,_hSourceCurrent,_hSourcePoint,_hWhole,_hCos,_hHeads⟩ :=
    prepared_current_companion_smooth_diagram (k := 1) hn M hM T hc C hC π hπ hCuts h z hz hPos
  let o := nmOrd (geoTransformAlong M P) (g z)
  have ho : 0<o := hPos
  let r := regimeRun (OrdRegime M o) P (g z)
  let U := ordMask (geoTransformAlong M (head P r)) o
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q r)) o
  let J := compAt M o (head P r)
  let J' := compAt (markedPullback (m := m) f M) o (head Q r)
  let R := restrict U (tail P r)
  let R' := restrict V (tail Q r)
  let z' : openPreimage (tail Q r) V := ⟨z,hp'⟩
  change markedPullback (m := m) p J=J' at hRecord
  change IsActualTowerPullback p R' R q at hCart
  change IsInvDomain 2 J at hDom
  change IsMaximalOrderAlong J.N J.ideal J.d at hMax
  change IsGeoTestTower J R at hTest
  have hTarget : q z' ∈ (geoTransformAlong J R).cosupp := by
    rw [hPoint]
    exact hTargetPoint
  have hv := (original_given_all_step_one_smooth_values hn hm J hDom hMax R hTest hCart).2 z' hTarget d
  rw [hRecord,hPoint] at hv
  change genInv (fun {A} K {B} S w => Seq.StepOneValueMasked.stepOneInvM (X := A)
      (invFamily hm ((m-n)+d+1)) K (Y := B) S w) (markedPullback (m := m) f M) Q z=
    generalDimensionMap (m-n) (stepDimensionMap (familyDimensionMap (m-n) (d+1)))
      (genInv (fun {A} K {B} S w => Seq.StepOneValueMasked.stepOneInvM (X := A)
        (invFamily hn (d+1)) K (Y := B) S w) M P (g z))
  unfold generalDimensionMap genInv genSecond
  rw [hOrd,show nmOrd (geoTransformAlong M P) (g z)=o from rfl,
    if_neg (ne_of_gt ho),hRun,genLowerValue_eq_of_mem _ _ hp',genLowerValue_eq_of_mem _ _ hp]
  simp only [if_neg (ne_of_gt ho),ofLex_toLex,Sum.map_inr,WithTop.map_coe]
  exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy ((m-n)+d+1)) =>
    toLex (o,toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy ((m-n)+d+1))))))) hv

/-- Original compact-current inputs choose the actual step and ONE real smooth
source history before all new cosupport points and EVERY family depth d+2. -/
theorem exists_original_compact_prepared_general_smooth_history
    (hn : 0<n) (hm : 0<m) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (T : BlowupTower X D) (hc : IsCanonical M ((invFamily hn 2).inv M) T)
    (hK : IsCompact (geoTransformAlong M T).cosupp)
    (hne : (geoTransformAlong M T).cosupp.Nonempty)
    {ι : Type*} [Fintype ι] (A : ι → GermIdeal n D) (hA : ∀ i,(A i).IsCoherent)
    {f : Y → X} (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f) :
    ∃ (a : D) (C : Set D) (Z : CMfd.{u} n) (π : Z → D) (hπ : IsBlowupAlong n C π),
      C.Nonempty ∧ (geoTransformAlong M T).IsAdmissibleCentre C ∧
      (∀ c ∈ C,(invFamily hn 2).inv M T c=(invFamily hn 2).inv M T a) ∧
      (∀ i,∀ c ∈ C,∀ ℓ,hilbertSamuelAt (A i) c ℓ=hilbertSamuelAt (A i) a ℓ) ∧
      IsGeoTestTower M (.step T C π hπ) ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      NormalCrossings.IsSNCDivisor n ((geoTransformAlong M T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      ∃ (Z' : CMfd.{u} m) (Q : BlowupTower Y Z') (g : Z' → Z),
        IsActualTowerPullback f Q (.step T C π hπ) g ∧ IsGeoTestTower (markedPullback (m := m) f M) Q ∧
        ∀ z : Z',g z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp → ∀ d : ℕ,
          (invFamily hm ((m-n)+d+2)).inv (markedPullback (m := m) f M) Q z=
            familyDimensionMap (m-n) (d+2) ((invFamily hn (d+2)).inv M (.step T C π hπ) (g z)) := by
  obtain ⟨a,C,Z,π,_ha,hCne,hCL,hC,hR,hHS,hπ,hProper,hHolo,_hw,hSNC⟩ :=
    exists_original_current_compact_simultaneous_first_blowup hn 2 M hM T hc hK hne A hA
  have hT := (invFamily hn 2).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  have hP : IsGeoTestTower M (.step T C π hπ) := ⟨hT,hC⟩
  obtain ⟨Z',Q,g,h,_hg,_hLength,_hUniversal,hQ,_hWhole,_hWF,_hCos,_hHeads⟩ :=
    exists_actual_relative_marked_tower hf M hM.isWellFormed (.step T C π hπ) hP
  have hCuts : ∀ y ∈ (geoTransformAlong M T).cosupp,0<nmOrd (geoTransformAlong M T) y →
      ∀ c ∈ C,(invFamily hn 2).inv M T y≤(invFamily hn 2).inv M T c :=
    fun y hy _hp c hc => (hCL hc).2 y hy
  refine ⟨a,C,Z,π,hπ,hCne,hC,hR,hHS,hP,hProper,hHolo,hSNC,Z',Q,g,h,hQ,?_⟩
  intro z hz d
  exact prepared_original_general_smooth_values hn hm M hM T hc C hC π hπ hCuts h z hz d

end
end Hironaka.HironakaOriginalPreparedGeneralSmoothValues
