/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPreparedAllStepOneEtaleValues
import Hironaka.Resolution.HironakaOriginalFullCutInheritedCompanion
import Hironaka.Resolution.HironakaOriginalPreparedCurrentCompanion
/-! Actual CURRENT order-run companion StepOne numerical locality follows
real increment/reset; no frozen/current history equality is assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPreparedCurrentCompanionEtaleValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  CanonicalCentres GeneralValue StepOneRegime NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  HomogenizedIdealAlong BlowupRestrictOpen HironakaOriginalFrozenCompanionPresentation
  HironakaOriginalFullCutInheritedCompanion HironakaOriginalPreparedCurrentCompanion
  HironakaOriginalPreparedAllStepOneEtaleValues HironakaOriginalAllStepOneEtaleValues
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCanonicalValueDimensionShift
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y Z A B : CMfd.{u} n}

private theorem stepDimensionMap_cast {α β : Type} (e : β=α) (f : α → β)
    (hf : ∀ x,e ▸ f x=x) (v : ℕ ×ₗ WithTop α) :
    congrArg (fun A => ℕ ×ₗ WithTop A) e ▸ stepDimensionMap f v=v := by
  subst β
  have hfid : f=id := funext hf
  rw [hfid]
  simp [stepDimensionMap]

private theorem stepOneInvM_cast_depth (hn : 0<n) {a b : ℕ} (hab : a=b)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (z : Y) :
    congrArg (fun j => ℕ ×ₗ WithTop (ValTy j)) hab ▸
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn a) M T z=
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn b) M T z := by
  cases hab
  rfl

private theorem domain_three_at_depth (M : MarkedIdeal n X) (hM : IsInvDomain 3 M) (d : ℕ) :
    IsInvDomain (d+3) M := by
  refine ⟨hM.isWellFormed,?_,hM.one_le_d,hM.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨j,hj,hreg⟩ := hM.dimLE x hx
  exact ⟨j,by omega,hreg⟩

private theorem reflexive_stepOne_etale_values (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    {f : A → X} {g : B → X} {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q .refl g) (z : B) (hz : g z∈M.cosupp) (d : ℕ) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) (markedPullback (m := n) f M) Q z=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) M .refl (g z) := by
  have hVal := (HironakaOriginalSourceStepOneCanonicalSmoothHistory.IsActualTowerPullback.original_stepOne_family
    (k := d+1) hn hn h M (domain_three_at_depth M hM d) hmax trivial).2 z hz
  rw [Nat.sub_self] at hVal
  let e := congrArg (fun A => ℕ ×ₗ WithTop A) (congrArg ValTy (Nat.zero_add (d+2)))
  have hMap := stepDimensionMap_cast (congrArg ValTy (Nat.zero_add (d+2)))
    (familyDimensionMap 0 (d+2)) (familyDimensionMap_zero (d+2))
    (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) M .refl (g z))
  have hCast := congrArg (fun w => e ▸ w) hVal
  have hFinal := hCast.trans hMap
  have hSourceCast := stepOneInvM_cast_depth hn (Nat.zero_add (d+2))
    (markedPullback (m := n) f M) Q z
  exact hSourceCast.symm.trans hFinal

private theorem frozen_companion_step_one_etale_values (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 3 M) (T : BlowupTower X Y)
    (hc : IsCanonical M ((invFamily hn 3).inv M) T)
    (y : Y) (hy : y∈(geoTransformAlong M T).cosupp) (hq : 1≤orderAt M T y)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      (invFamily hn 3).inv M T x≤(invFamily hn 3).inv M T c)
    {f : A → maskAt M T y}
    {g : B → openPreimage (.step (tail T (runAt M T y)) C π hπ) (maskAt M T y)}
    {Q : BlowupTower A B}
    (h : IsActualTowerPullback f Q
      (restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ)) g)
    (z : B) (hz : g z∈(geoTransformAlong (companionAt M T y)
      (restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ))).cosupp) (d : ℕ) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2))
        (markedPullback (m := n) f (companionAt M T y)) Q z=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) (companionAt M T y)
        (restrict (maskAt M T y) (.step (tail T (runAt M T y)) C π hπ)) (g z) := by
  have hData := original_full_cut_prepared_companion_data (k := 2) hn M hM T hc y hy hq C hC π hπ hCuts
  let J := companionAt M T y
  let R := companionTailAt M T y
  let V := patchAt M T y
  let C' : Set V := (Subtype.val : V → Y) ⁻¹' C
  let W := openPreimage (.step (tail T (runAt M T y)) C π hπ) (maskAt M T y)
  let π' : W → V := fun w => ⟨π w.val,w.property⟩
  have hπ' : IsBlowupAlong n C' π' :=
    isBlowupAlong_restrict hπ V (V.isOpen.preimage hπ.contMDiff.continuous)
  have hC' : (geoTransformAlong J R).IsAdmissibleCentre C' := hData.2.2.2.1.2
  have hCuts' : ∀ p∈(geoTransformAlong J R).cosupp,∀ c∈C',
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) J R p≤
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) J R c := by
    intro p hp c hcC
    exact (hData.2.2.2.2.2 hcC).2 p hp
  exact (prepared_all_step_one_etale_values
    (X := CMfd.of (n := n) (maskAt M T y)) (Y := CMfd.of (n := n) V)
    (Z := CMfd.of (n := n) W) hn J hData.1 hData.2.1 R hData.2.2.1 C' hC' π' hπ' hCuts' h).2 z hz d

/-- The actual current order-run data precede numerical comparisons; old
persistence and genuine reset are proved internally and kept separate. -/
theorem current_companion_step_one_etale_values_after_full_cut
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 3 M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((invFamily hn 3).inv M) T)
    (C : Set Y) (hC : (geoTransformAlong M T).IsAdmissibleCentre C)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hCuts : ∀ x ∈ (geoTransformAlong M T).cosupp,∀ c ∈ C,
      (invFamily hn 3).inv M T x≤(invFamily hn 3).inv M T c)
    (y : Z) (hy : y∈(geoTransformAlong M (.step T C π hπ)).cosupp)
    (hp : 0<nmOrd (geoTransformAlong M (.step T C π hπ)) y) :
    let P := .step T C π hπ
    let q := nmOrd (geoTransformAlong M P) y
    let r := regimeRun (OrdRegime M q) P y
    let U := ordMask (geoTransformAlong M (head P r)) q
    let J := compAt M q (head P r)
    let R := restrict U (tail P r)
    IsInvDomain 3 J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧ IsGeoTestTower J R ∧
      ∀ {A B : CMfd.{u} n} {f : A → U} {g : B → openPreimage (tail P r) U}
        {Q : BlowupTower A B},IsActualTowerPullback f Q R g →
        ∀ z : B,g z∈(geoTransformAlong J R).cosupp → ∀ d : ℕ,
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) (markedPullback (m := n) f J) Q z=
            Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) J R (g z) := by
  let P : BlowupTower X Z := .step T C π hπ
  let q := nmOrd (geoTransformAlong M P) y
  have hData := current_compAt_data_after_full_cut (k := 2) hn M hM T hc C hC π hπ
    (fun x hx _ => hCuts x hx) y hy hp
  refine ⟨hData.1,hData.2.1,hData.2.2.1,?_⟩
  let F : ℕ → ℕ → Prop := fun o r =>
    let U := ordMask (geoTransformAlong M (head P r)) o
    let J := compAt M o (head P r)
    let R := restrict U (tail P r)
    IsInvDomain 3 J → IsMaximalOrderAlong J.N J.ideal J.d →
      ∀ {A B : CMfd.{u} n} {f : A → U} {g : B → openPreimage (tail P r) U}
        {Q : BlowupTower A B},IsActualTowerPullback f Q R g →
        ∀ z : B,g z∈(geoTransformAlong J R).cosupp → ∀ d : ℕ,
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) (markedPullback (m := n) f J) Q z=
            Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+2)) J R (g z)
  have hValues : F q (regimeRun (OrdRegime M q) P y) := by
    by_cases hOld : OrdRegime M q T (π y)
    · rw [regimeRun_step_of (OrdRegime M q) T C π hπ hOld]
      have hpOld : 1≤orderAt M T (π y) := by
        change 1≤nmOrd (geoTransformAlong M T) (π y)
        rw [hOld.2]
        exact hp
      let G : ℕ → Prop := fun o => F o (regimeRun (OrdRegime M o) T (π y)+1)
      have hFrozen : G (orderAt M T (π y)) := by
        intro _hJ _hMax A B f g Q h z hz d
        exact frozen_companion_step_one_etale_values hn M hM T hc (π y) hOld.1 hpOld C hC π hπ hCuts h z hz d
      exact (congrArg G hOld.2).mp hFrozen
    · rw [regimeRun_step_of_not (OrdRegime M q) T C π hπ hOld]
      intro hJ hMax A B f g Q h z hz d
      exact reflexive_stepOne_etale_values hn _ hJ hMax h z hz d
  intro A B f g Q h z hz d
  exact hValues hData.1 hData.2.1 h z hz d

end
end Hironaka.HironakaOriginalPreparedCurrentCompanionEtaleValues
