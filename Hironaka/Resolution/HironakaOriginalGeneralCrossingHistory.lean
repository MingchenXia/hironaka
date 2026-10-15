/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCanonicalNormalizedLowerTail
import Hironaka.Invariant.GeneralTowerIso
/-! Actual original General order histories across an interior empty step.
Complete mathematical route written first in `hironaka-original-general-crossing-history-extension.tex`.
Positive recursive companion values and full outer transport remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalGeneralCrossingHistory
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  MonomialInvariantEmptyMember MarkedIdealBiholomorphism NonmonomialOrderLocal
  NonmonomialOrderTransport NonmonomialOrderRegime StepOneRegime
  HironakaOriginalInteriorEmptyHistory HironakaOriginalCrossingLowerHistory
  HironakaOriginalCrossingValueTransport GeneralValue GeneralCanonicalTail
  HomogenizedIdealAlong CompanionRebase NonmonomialOrderTail
  BlowupTowerIsomorphism BlowupTowerIsoTail
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- The actual original order dictionary at EVERY tail, including the
immediate empty step. Genuine head geometry supplies all equivalence data. -/
theorem nmOrd_interior_empty_all_tails (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H) (S : BlowupTower A Y) (y : Y) :
    nmOrd (geoTransformAlong M (interiorEmptyHistory H S)) y =
      nmOrd (geoTransformAlong M (H.append S)) y := by
  have hK := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM H hH
  have hr := restrictEquiv_emptyStepBase_pullback (geoTransformAlong M H)
    BlowupExistenceCodimOne.isBlowupAlong_id_empty hK.isClosedSubmanifold_N.1 hK.isSNCDivisor.1
  rw [ContactCanonicalAlong.pullback_id _ hK.isCoherent] at hr
  have hB := (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hK
    (isAdmissibleCentre_empty _) BlowupExistenceCodimOne.isBlowupAlong_id_empty).isCoherent
  have hBN : IsClosed (emptyStepBase (geoTransformAlong M H) id).N := by
    rw [hr.N_eq]
    exact hK.isClosedSubmanifold_N.1
  have hj : M.E.length+H.length ≤
      (geoTransformAlong (emptyStepBase (geoTransformAlong M H) id) S).E.length := by
    rw [length_E_geoTransformAlong,length_E_emptyStepBase,length_E_geoTransformAlong]
    omega
  rw [interiorEmptyHistory,geoTransformAlong_step_empty_append,geoTransformAlong_append,
    nmOrd_insertEmpty _ hj y]
  exact nmOrd_geoTransformAlong_congr hr hBN hB hK.isCoherent S y

theorem ordRegime_dictionary (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H) (S : BlowupTower A Y) (o : ℕ) (y : Y) :
    OrdRegime M o (interiorEmptyHistory H S) y ↔ OrdRegime M o (H.append S) y := by
  change (y ∈ (geoTransformAlong M (interiorEmptyHistory H S)).cosupp ∧
    nmOrd (geoTransformAlong M (interiorEmptyHistory H S)) y = o) ↔
    (y ∈ (geoTransformAlong M (H.append S)).cosupp ∧ nmOrd (geoTransformAlong M (H.append S)) y = o)
  rw [(geometric_dictionary M hM H hH S).2.2.2.1,nmOrd_interior_empty_all_tails M hM H hH S y]

open Classical in
/-- The actual order-regime run recursion, with no supplied regime/value
comparison certificate. Its prefix dictionary is proved internally above. -/
theorem ordRegime_run_dictionary (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H) (o : ℕ) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower A Y) (y : Y),
      let r := regimeRun (OrdRegime M o) (H.append S) y
      regimeRun (OrdRegime M o) (interiorEmptyHistory H S) y =
        if r<S.length then r else if OrdRegime M o H (S.proj y) then r+1 else S.length
  | _, .refl, y => by
    change (if OrdRegime M o H y then regimeRun (OrdRegime M o) H y+1 else 0) =
      (if regimeRun (OrdRegime M o) H y<0 then _ else
        if OrdRegime M o H y then _ else 0)
    simp only [Nat.not_lt_zero,if_false,BlowupTower.append_refl]
  | _, .step S C π hπ, y => by
    dsimp only
    change (if OrdRegime M o (interiorEmptyHistory H S) (π y) then
        regimeRun (OrdRegime M o) (interiorEmptyHistory H S) (π y)+1 else 0) =
      (if (if OrdRegime M o (H.append S) (π y) then
          regimeRun (OrdRegime M o) (H.append S) (π y)+1 else 0)<S.length+1 then
        (if OrdRegime M o (H.append S) (π y) then
          regimeRun (OrdRegime M o) (H.append S) (π y)+1 else 0) else
        if OrdRegime M o H (S.proj (π y)) then
          (if OrdRegime M o (H.append S) (π y) then
            regimeRun (OrdRegime M o) (H.append S) (π y)+1 else 0)+1 else S.length+1)
    simp only [ordRegime_dictionary M hM H hH S]
    by_cases hp : OrdRegime M o (H.append S) (π y)
    · simp only [hp,if_true]
      rw [ordRegime_run_dictionary M hM H hH o S (π y)]
      split_ifs <;> omega
    · simp only [hp,if_false,Nat.zero_lt_succ,if_true]

/-- Both ENTIRE actual General crossing splits have the true SAME original
stage/head, from original current order and its actual reaching run. -/
theorem actual_general_crossing_splits (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H) (S : BlowupTower A Y)
    (o : ℕ) (y : Y) (hy : y ∈ (geoTransformAlong M (H.append S)).cosupp)
    (hν : nmOrd (geoTransformAlong M (H.append S)) y=o)
    (hreach : S.length≤regimeRun (OrdRegime M o) (H.append S) y) :
    let r := regimeRun (OrdRegime M o) (H.append S) y
    let r' := regimeRun (OrdRegime M o) (interiorEmptyHistory H S) y
    let a := r-S.length
    r'=r+1 ∧ split (H.append S) r=⟨(split H a).1,head H a,(tail H a).append S⟩ ∧
      split (interiorEmptyHistory H S) r'=⟨(split H a).1,head H a,interiorEmptyHistory (tail H a) S⟩ := by
  classical
  dsimp only
  let r := regimeRun (OrdRegime M o) (H.append S) y
  have hbase : OrdRegime M o H (S.proj y) :=
    regime_at_base_of_reaching_run (OrdRegime M o) H S y ⟨hy,hν⟩ hreach
  have hr : regimeRun (OrdRegime M o) (interiorEmptyHistory H S) y=r+1 := by
    rw [ordRegime_run_dictionary M hM H hH o S y,
      if_neg (not_lt_of_ge hreach),if_pos hbase]
  have hnew := split_append_above_tail
    (H.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) S (r+1) (by omega)
  have hs : r+1-S.length=(r-S.length)+1 := by omega
  rw [hs] at hnew
  change split (interiorEmptyHistory H S) (r+1)=
    ⟨(split H (r-S.length)).1,head H (r-S.length),interiorEmptyHistory (tail H (r-S.length)) S⟩ at hnew
  exact ⟨hr,split_append_above_tail H S r hreach,by rw [hr];exact hnew⟩

private def genInner (hn : 0 < n) (k : ℕ) :
    ∀ {D : CMfd.{u} n}, MarkedIdeal n D → ∀ {B : CMfd.{u} n}, BlowupTower D B → B →
      ℕ ×ₗ WithTop (ValTy k) :=
  fun {D} J {B} R z => Seq.StepOneValueMasked.stepOneInvM (X := D) (invFamily hn k) J (Y := B) R z

private def splitGenData (hn : 0 < n) (k : ℕ) (M : MarkedIdeal n X) (o : ℕ)
    (v : Σ D : CMfd.{u} n, BlowupTower X D × BlowupTower D Y) (y : Y) : Prop :=
  GenLowerData (genInner hn k) (k+1) M o v.2.1 v.2.2 y

/-- ALL-k actual original FULL canonical histories supply real companion
domain/maximal order/whole StepOne canonical tail/cosupport internally. -/
theorem original_canonical_general_crossing_data (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn (k+1)).inv M) (H.append S))
    (o : ℕ) (y : Y) (hy : y ∈ (geoTransformAlong M (H.append S)).cosupp)
    (hν : nmOrd (geoTransformAlong M (H.append S)) y=o) (ho : 1≤o)
    (hreach : S.length≤regimeRun (OrdRegime M o) (H.append S) y) :
    let r := regimeRun (OrdRegime M o) (H.append S) y
    GenLowerData (fun {D} J {B} R z =>
      Seq.StepOneValueMasked.stepOneInvM (X := D) (invFamily hn k) J (Y := B) R z)
      (k+1) M o (head H (r-S.length)) ((tail H (r-S.length)).append S) y := by
  dsimp only
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn (k+1)).isInvValue hM (H.append S) hcan
  have hv := StepOneSeq.isMaxOrderValue_stepOneInvM (k := k+1) (invFamily hn k) hn
  have hc : IsCanonical M (genInv (genInner hn k) M) (H.append S) := hcan
  have hd := hasGenLowerData_of_isCanonical (genInner hn k) hv hn hM (H.append S) ht hc y hy o hν ho
  change splitGenData hn k M o (split (H.append S) (regimeRun (OrdRegime M o) (H.append S) y)) y at hd
  rw [split_append_above_tail H S _ hreach] at hd
  exact hd

/-- A genuine geometric test producer. Its old test input is supplied by
original canonical companion data in the original-input consumer below. -/
private theorem new_restricted_companion_test {D : CMfd.{u} n}
    (U : Opens D) (J : MarkedIdeal n U) (hJ : J.IsWellFormed)
    (B : BlowupTower D A) (S : BlowupTower A Y)
    (ht : IsGeoTestTower J (restrict U (B.append S))) :
    IsGeoTestTower J (restrict U (interiorEmptyHistory B S)) := by
  let Φ := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞
  have hpull : MarkedIdeal.pullback Φ J=J := ContactCanonicalAlong.pullback_id J hJ.isCoherent
  have hnorm := IsTowerIso.isGeoTestTower_iff Φ hJ.isClosedSubmanifold_N hJ.isCoherent
    (isTowerIso_restrict_append U B S)
  rw [hpull] at hnorm
  have htNorm := hnorm.mp ht
  have htB := (isGeoTestTower_append_iff J (restrict U B) (restrict (openPreimage B U) S)).mp htNorm |>.1
  have htNew := (isGeoTestTower_interior_empty_iff (X := CMfd.of (n := n) U)
    J hJ (restrict U B) htB (restrict (openPreimage B U) S)).mpr htNorm
  have hnew := IsTowerIso.isGeoTestTower_iff Φ hJ.isClosedSubmanifold_N hJ.isCoherent
    (actual_restricted_empty_history U B S)
  rw [hpull] at hnew
  exact hnew.mpr htNew

/-- Genuine original FULL canonical input gives companion data, WHOLE
new restricted tail and actual NEW testness, with no tail/can/value cert. -/
theorem original_canonical_general_companion_history (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M ((invFamily hn (k+1)).inv M) (H.append S))
    (o : ℕ) (y : Y) (hy : y ∈ (geoTransformAlong M (H.append S)).cosupp)
    (hν : nmOrd (geoTransformAlong M (H.append S)) y=o) (ho : 1≤o)
    (hreach : S.length≤regimeRun (OrdRegime M o) (H.append S) y) :
    let r := regimeRun (OrdRegime M o) (H.append S) y
    let K := head H (r-S.length)
    let B := tail H (r-S.length)
    let U := ordMask (geoTransformAlong M K) o
    let J := compAt M o K
    GenLowerData (fun {D} J {B} R z =>
      Seq.StepOneValueMasked.stepOneInvM (X := D) (invFamily hn k) J (Y := B) R z)
      (k+1) M o K (B.append S) y ∧
    IsGeoTestTower J (restrict U (interiorEmptyHistory B S)) ∧
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (restrict U (interiorEmptyHistory B S))
      (interiorEmptyHistory (restrict U B) (restrict (openPreimage B U) S))
      (opensCongr (n := n) (openPreimage_append
        (B.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) S U).symm) := by
  dsimp only
  have hd := original_canonical_general_crossing_data hn k M hM H S hcan o y hy hν ho hreach
  obtain ⟨hp,hdom,hmax,hcanJ,hcos⟩ := hd
  let r := regimeRun (OrdRegime M o) (H.append S) y
  let K := head H (r-S.length)
  let B := tail H (r-S.length)
  let U := ordMask (geoTransformAlong M K) o
  let J := compAt M o K
  have htJ := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1)
    (invFamily hn k) J hdom hmax hn (restrict U (B.append S)) hcanJ).2.1
  refine ⟨⟨hp,hdom,hmax,hcanJ,hcos⟩,?_,actual_restricted_empty_history U B S⟩
  exact new_restricted_companion_test U J hdom.isWellFormed B S htJ

end
end Hironaka.HironakaOriginalGeneralCrossingHistory
