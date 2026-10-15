/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalOuterShortFamily
import Hironaka.Resolution.HironakaOriginalGeneralSpecialCompanion
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalCurveFamily
/-! Complete original curve-history route, mathematics written first.
Actual all-tail monomial transport, complete curve values/order and
canonical/terminal histories are proved. Higher crossing remains open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCurveHistory
noncomputable section
open Classical
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  MonomialInvariantEmptyMember MarkedIdealBiholomorphism NonmonomialOrderLocal
  NonmonomialOrderMonomialTransport MonomialStepAlong
  HironakaOriginalInteriorEmptyHistory HironakaOriginalGeneralCrossingHistory
  HironakaOriginalInvariantEmptyInsertion HironakaOriginalGeneralSpecialCompanion
  StepOneValue StepOneValueMasked GeneralValue NonmonomialOrderRegime StepOneRegime
  HironakaOriginalOuterShortFamily HironakaSmoothSubmersionOriginalCurveFamily
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- Genuine whole monomial transport includes the IMMEDIATE empty suffix:
restricted-equivalence, not false ambient record equality, supplies it. -/
theorem original_towerInv_interior_empty_all_tails (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H) (S : BlowupTower A Y) (y : Y) :
    towerInvAlong M (interiorEmptyHistory H S) y=
      shiftVal (M.E.length+H.length) (towerInvAlong M (H.append S) y) := by
  have hK := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM H hH
  have hr := restrictEquiv_emptyStepBase_pullback (geoTransformAlong M H)
    BlowupExistenceCodimOne.isBlowupAlong_id_empty hK.isClosedSubmanifold_N.1 hK.isSNCDivisor.1
  rw [ContactCanonicalAlong.pullback_id _ hK.isCoherent] at hr
  have hB := (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hK
    (isAdmissibleCentre_empty _) BlowupExistenceCodimOne.isBlowupAlong_id_empty).isCoherent
  have hBN : IsClosed (emptyStepBase (geoTransformAlong M H) id).N := by
    rw [hr.N_eq]
    exact hK.isClosedSubmanifold_N.1
  have hgamma := towerInvAlong_congr hr hBN hB hK.isCoherent S
  rw [interiorEmptyHistory,towerInvAlong_step_empty_append,hgamma]
  unfold towerInvAlong
  rw [geoTransformAlong_append]

/-- ENTIRE specific-family monomial leaf at ALL depths and EVERY actual
suffix, without S-nonempty/CAN/equality certificates. -/
theorem original_invFamily_interior_monomial_all_tails (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H) (S : BlowupTower A Y) (y : Y)
    (h0 : nmOrd (geoTransformAlong M (H.append S)) y=0) :
    (invFamily hn k).inv M (interiorEmptyHistory H S) y=
      shiftFamily k (M.E.length+H.length) ((invFamily hn k).inv M (H.append S) y) := by
  cases k with
  | zero => rfl
  | succ k =>
    change genInv (fun {D} J {Z} Q z =>
        Seq.StepOneValueMasked.stepOneInvM (X := D) (invFamily hn k) J (Y := Z) Q z)
        M (interiorEmptyHistory H S) y=
      generalShift (M.E.length+H.length) (pairShift (shiftFamily k 0))
        (genInv (fun {D} J {Z} Q z =>
          Seq.StepOneValueMasked.stepOneInvM (X := D) (invFamily hn k) J (Y := Z) Q z) M (H.append S) y)
    unfold generalShift genInv genSecond
    rw [nmOrd_interior_empty_all_tails M hM H hH S y,h0]
    simp only [ofLex_toLex]
    exact congrArg (fun v : WithBot MonomialInvariant.Val =>
      (toLex (0,toLex (Sum.inl v)) : ValTy (k+1)))
      (original_towerInv_interior_empty_all_tails M hM H hH S y)

private theorem positive_curve_family_shift_fixed (hn : 0<n) (M : MarkedIdeal n X)
    (T : BlowupTower X Y) (y : Y) (j : ℕ) (hpos : 0<nmOrd (geoTransformAlong M T) y) :
    shiftFamily 1 j ((invFamily hn 1).inv M T y)=(invFamily hn 1).inv M T y := by
  have hid : pairShift (shiftFamily 0 0) = (id : (ℕ ×ₗ WithTop (ValTy 0)) → ℕ ×ₗ WithTop (ValTy 0)) := by
    funext v
    simp [pairShift,shiftFamily]
  change generalShift j (pairShift (shiftFamily 0 0))
    (genInv (fun {D} J {Z} Q z => Seq.StepOneValueMasked.stepOneInvM (X := D) (invFamily hn 0) J (Y := Z) Q z) M T y)=
    genInv (fun {D} J {Z} Q z => Seq.StepOneValueMasked.stepOneInvM (X := D) (invFamily hn 0) J (Y := Z) Q z) M T y
  rw [hid]
  unfold generalShift genInv genSecond
  simp only [if_neg (ne_of_gt hpos),ofLex_toLex,Sum.map_inr,WithTop.map_id]
  rfl

/-- ALL actual original curve cosupport values on EVERY suffix, internally
covering true short/reaching, positive/monomial and empty-tail branches. -/
theorem original_curve_entire_interior_value (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn 1).inv M) (H.append S))
    (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp) :
    (invFamily hn 1).inv M (interiorEmptyHistory H S) y=
      shiftFamily 1 (M.E.length+H.length) ((invFamily hn 1).inv M (H.append S) y) := by
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn 1).isInvValue hM (H.append S) hcan
  have hH := (isGeoTestTower_append_iff M H S).mp ht |>.1
  by_cases h0 : nmOrd (geoTransformAlong M (H.append S)) y=0
  · exact original_invFamily_interior_monomial_all_tails hn 1 M hM.isWellFormed H hH S y h0
  let o := nmOrd (geoTransformAlong M (H.append S)) y
  have ho : 0<o := Nat.pos_of_ne_zero h0
  by_cases hs : regimeRun (OrdRegime M o) (H.append S) y<S.length
  · exact actual_entire_outer_short_family_value hn 0 M hM.isWellFormed H hH S y hs
  have hreach : S.length≤regimeRun (OrdRegime M o) (H.append S) y := le_of_not_gt hs
  obtain ⟨hp,⟨hdom,hmax,hcanJ,hcos⟩,hv⟩ :=
    original_canonical_general_special_companion_value hn 0 M hM H S hcan o y hy rfl ho hreach
  have hsp := original_curve_step_one_special hn _ hdom hmax hcanJ _ hcos
  rw [hv hsp]
  exact (positive_curve_family_shift_fixed hn M (H.append S) y (M.E.length+H.length) ho).symm

theorem original_curve_entire_interior_comparisons (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn 1).inv M) (H.append S))
    (y z : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp)
    (hz : z∈(geoTransformAlong M (H.append S)).cosupp) :
    let v := (invFamily hn 1).inv M (H.append S) y
    let w := (invFamily hn 1).inv M (H.append S) z
    let v' := (invFamily hn 1).inv M (interiorEmptyHistory H S) y
    let w' := (invFamily hn 1).inv M (interiorEmptyHistory H S) z
    (v'<w' ↔ v<w) ∧ (v'≤w' ↔ v≤w) ∧ (v'=w' ↔ v=w) := by
  dsimp only
  rw [original_curve_entire_interior_value hn M hM H S hcan y hy,
    original_curve_entire_interior_value hn M hM H S hcan z hz]
  have hm := strictMono_shiftFamily 1 (M.E.length+H.length)
  exact ⟨hm.lt_iff_lt,hm.le_iff_le,hm.injective.eq_iff⟩

private theorem original_curve_actual_maximum_dictionary (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn 1).inv M) (H.append S)) :
    ResolutionDriver.maxLocus ((invFamily hn 1).inv M (interiorEmptyHistory H S))
        (geoTransformAlong M (interiorEmptyHistory H S)).cosupp=
      ResolutionDriver.maxLocus ((invFamily hn 1).inv M (H.append S))
        (geoTransformAlong M (H.append S)).cosupp := by
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn 1).isInvValue hM (H.append S) hcan
  have hH := (isGeoTestTower_append_iff M H S).mp ht |>.1
  have hcos := (geometric_dictionary M hM.isWellFormed H hH S).2.2.2.1
  ext y
  change (y∈(geoTransformAlong M (interiorEmptyHistory H S)).cosupp ∧
    ∀ z∈(geoTransformAlong M (interiorEmptyHistory H S)).cosupp, _ ≤ _) ↔
    (y∈(geoTransformAlong M (H.append S)).cosupp ∧
    ∀ z∈(geoTransformAlong M (H.append S)).cosupp, _ ≤ _)
  rw [hcos]
  constructor
  · rintro ⟨hy,hmax⟩
    refine ⟨hy,fun z hz => ?_⟩
    exact (original_curve_entire_interior_comparisons hn M hM H S hcan z y hz hy).2.1.mp (hmax z hz)
  · rintro ⟨hy,hmax⟩
    refine ⟨hy,fun z hz => ?_⟩
    exact (original_curve_entire_interior_comparisons hn M hM H S hcan z y hz hy).2.1.mpr (hmax z hz)

/-- Original FULL curve canonical history INTERNALLY supplies the inserted
full canonical history, with every original centre retained incl emptyS. -/
theorem original_curve_interior_isCanonical (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn 1).inv M) (H.append S)) :
    IsCanonical M ((invFamily hn 1).inv M) (interiorEmptyHistory H S) := by
  revert hcan
  induction S with
  | refl =>
    intro hcan
    exact ⟨hcan,Or.inl rfl⟩
  | step S C π hπ ih =>
    intro hcan
    obtain ⟨hc,hC⟩ := hcan
    refine ⟨ih hc,?_⟩
    rcases hC with he | hm
    · exact Or.inl he
    · exact Or.inr (hm.trans (original_curve_actual_maximum_dictionary hn M hM H S hc).symm)

/-- Actual original terminal resolution transports with the internally
proved entire canonical inserted history; no sourceCAN/value certificate. -/
theorem original_curve_interior_canonical_resolution (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn 1).inv M) (H.append S))
    (hres : IsGeoResolution M (H.append S)) :
    IsCanonical M ((invFamily hn 1).inv M) (interiorEmptyHistory H S) ∧
      IsGeoResolution M (interiorEmptyHistory H S) := by
  have hH := (isGeoTestTower_append_iff M H S).mp hres.1 |>.1
  have ht := (HironakaOriginalCrossingValueTransport.isGeoTestTower_interior_empty_iff
    M hM.isWellFormed H hH S).mpr hres.1
  refine ⟨original_curve_interior_isCanonical hn M hM H S hcan,ht,?_⟩
  rw [(geometric_dictionary M hM.isWellFormed H hH S).2.2.2.1,hres.2]

end
end Hironaka.HironakaOriginalCurveHistory
