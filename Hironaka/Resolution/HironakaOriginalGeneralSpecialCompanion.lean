/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalGeneralCrossingHistory
/-! Whole actual original General values at their true special companions.
Complete mathematics written first in `hironaka-original-general-special-companion-extension.tex`. No newly inserted
canonical-history certificate is assumed; nonspecial recursion remains open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalGeneralSpecialCompanion
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  StepOneRegime StepOneValue StepOneValueMasked HomogenizedIdealAlong
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail GeneralValue StepOneLowerDomain
  MarkedIdealBiholomorphism BlowupTowerIsomorphism BlowupTowerIsoTail
  HironakaOriginalInteriorEmptyHistory HironakaOriginalCrossingLowerHistory
  HironakaOriginalCrossingValueTransport HironakaOriginalGeneralCrossingHistory
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- Actual whole restrictions retain their original level/special branch,
without either new canonical history or desired predicate certificate. -/
theorem whole_restricted_empty_special_dictionary {D : CMfd.{u} n}
    (U : Opens D) (J : MarkedIdeal n U) (hJ : J.IsWellFormed) (hd : 1≤J.d)
    (B : BlowupTower D A) (S : BlowupTower A Y)
    (ht : IsGeoTestTower (barMarked J) (restrict U (B.append S)))
    (p : openPreimage (B.append S) U) :
    ∃ hp' : (interiorEmptyHistory B S).proj (p : Y) ∈ U,
      let p' : openPreimage (interiorEmptyHistory B S) U := ⟨(p : Y),hp'⟩
      level J (restrict U (interiorEmptyHistory B S)) p'=level J (restrict U (B.append S)) p ∧
      (IsSpecial J (restrict U (interiorEmptyHistory B S)) p' ↔ IsSpecial J (restrict U (B.append S)) p) := by
  dsimp only
  let Φ := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞
  let B' := restrict U B
  let S' := restrict (openPreimage B U) S
  let χ := opensCongr (n := n) (openPreimage_append B S U).symm
  let q := χ p
  have hpull : MarkedIdeal.pullback Φ J=J := ContactCanonicalAlong.pullback_id J hJ.isCoherent
  have hpull' : MarkedIdeal.pullback Φ.symm J=J := ContactCanonicalAlong.pullback_id J hJ.isCoherent
  have hfOld := StepOneTowerIso.isTowerIso_facts Φ.symm J hJ hd
    (isTowerIso_restrict_append U B S).symm ht
  rw [hpull'] at hfOld
  have hq : χ.symm q=p := χ.symm_apply_apply p
  have hfPoint := hfOld.2.2 q
  change level J (B'.append S') q=level J (restrict U (B.append S)) (χ.symm q) ∧
    (IsSpecial J (B'.append S') q ↔ IsSpecial J (restrict U (B.append S)) (χ.symm q)) ∧ _ at hfPoint
  rw [hq] at hfPoint
  have htB := (isGeoTestTower_append_iff (barMarked J) B' S').mp hfOld.1 |>.1
  have htNew := (isGeoTestTower_interior_empty_iff (X := CMfd.of (n := n) U)
    (barMarked J) (StepOneLowerDomain.isWellFormed_barMarked (X := CMfd.of (n := n) U) J hJ) B' htB S').mpr hfOld.1
  have hp' : (interiorEmptyHistory B S).proj (p : Y) ∈ U := by
    rw [proj_interiorEmptyHistory]
    exact p.2
  let p' : openPreimage (interiorEmptyHistory B S) U := ⟨(p : Y),hp'⟩
  let χ' := opensCongr (n := n) (openPreimage_append
    (B.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) S U).symm
  have hpoint : χ' p'=q := by apply Subtype.ext;rfl
  have hfNew := StepOneTowerIso.isTowerIso_facts Φ J hJ hd (actual_restricted_empty_history U B S) htNew
  rw [hpull] at hfNew
  have hfNewPoint := hfNew.2.2 p'
  change level J (restrict U (interiorEmptyHistory B S)) p'=level J (interiorEmptyHistory B' S') (χ' p') ∧
    (IsSpecial J (restrict U (interiorEmptyHistory B S)) p' ↔ IsSpecial J (interiorEmptyHistory B' S') (χ' p')) ∧ _ at hfNewPoint
  rw [hpoint] at hfNewPoint
  refine ⟨hp',?_,?_⟩
  · exact (hfNewPoint.1.trans (level_dictionary (X := CMfd.of (n := n) U) J hJ B' htB S' q)).trans hfPoint.1
  · exact hfNewPoint.2.1.trans ((isSpecial_dictionary (X := CMfd.of (n := n) U) J hJ B' htB S' q).trans hfPoint.2.1)

private def actualInner (hn : 0<n) (k : ℕ) :
    ∀ {D : CMfd.{u} n}, MarkedIdeal n D → ∀ {Z : CMfd.{u} n}, BlowupTower D Z → Z →
      ℕ ×ₗ WithTop (ValTy k) :=
  fun {D} J {Z} T z => Seq.StepOneValueMasked.stepOneInvM (X := D) (invFamily hn k) J (Y := Z) T z

private def splitGeneralLowerValue (hn : 0<n) (k : ℕ) (M : MarkedIdeal n X) (o : ℕ)
    (v : Σ D : CMfd.{u} n, BlowupTower X D × BlowupTower D Y) (y : Y) :
      WithTop (ℕ ×ₗ WithTop (ValTy k)) := genLowerValue (actualInner hn k) M o v.2.1 v.2.2 y

/-- ONLY original full canonical input supplies the true companion, and
its actual special branch gives ENTIRE original family equality after the
interior empty step, including level zero and the immediate empty tail. -/
theorem original_canonical_general_special_companion_value (hn : 0<n) (k : ℕ)
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
    let L := restrict U (B.append S)
    ∃ hp : (B.append S).proj y∈U,
      (IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
        IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) L ∧
        (⟨y,hp⟩ : openPreimage (B.append S) U)∈(geoTransformAlong J L).cosupp) ∧
      (IsSpecial J L (⟨y,hp⟩ : openPreimage (B.append S) U) →
        (invFamily hn (k+1)).inv M (interiorEmptyHistory H S) y =
          (invFamily hn (k+1)).inv M (H.append S) y) := by
  dsimp only
  obtain ⟨hp,hdom,hmax,hcanJ,hcos⟩ :=
    original_canonical_general_crossing_data hn k M hM H S hcan o y hy hν ho hreach
  refine ⟨hp,⟨hdom,hmax,hcanJ,hcos⟩,?_⟩
  intro hsp
  let r := regimeRun (OrdRegime M o) (H.append S) y
  let K := head H (r-S.length)
  let B := tail H (r-S.length)
  let U := ordMask (geoTransformAlong M K) o
  let J := compAt M o K
  have htJ := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+1)
    (invFamily hn k) J hdom hmax hn (restrict U (B.append S)) hcanJ).1
  obtain ⟨hpnew,hlevel,hspecial⟩ := whole_restricted_empty_special_dictionary
    U J hdom.isWellFormed hdom.one_le_d B S htJ (⟨y,hp⟩ : openPreimage (B.append S) U)
  have hspnew := hspecial.mpr hsp
  have hv : actualInner hn k J (restrict U (interiorEmptyHistory B S))
      (⟨y,hpnew⟩ : openPreimage (interiorEmptyHistory B S) U) =
    actualInner hn k J (restrict U (B.append S)) (⟨y,hp⟩ : openPreimage (B.append S) U) := by
    unfold actualInner Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_pos hspnew,if_pos hsp,hlevel]
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn (k+1)).isInvValue hM (H.append S) hcan
  have hH := (isGeoTestTower_append_iff M H S).mp ht |>.1
  have hc := actual_general_crossing_splits M hM.isWellFormed H hH S o y hy hν hreach
  have hνnew : nmOrd (geoTransformAlong M (interiorEmptyHistory H S)) y=o :=
    (nmOrd_interior_empty_all_tails M hM.isWellFormed H hH S y).trans hν
  change genInv (actualInner hn k) M (interiorEmptyHistory H S) y =
    genInv (actualInner hn k) M (H.append S) y
  rw [genInv_of_nmOrd_ne_zero (actualInner hn k) M _ hνnew (by omega),
    genInv_of_nmOrd_ne_zero (actualInner hn k) M _ hν (by omega)]
  change toLex (o,toLex (Sum.inr (splitGeneralLowerValue hn k M o
      (split (interiorEmptyHistory H S) (regimeRun (OrdRegime M o) (interiorEmptyHistory H S) y)) y))) =
    toLex (o,toLex (Sum.inr (splitGeneralLowerValue hn k M o (split (H.append S) r) y)))
  rw [hc.2.2,hc.2.1]
  change toLex (o,toLex (Sum.inr (genLowerValue (actualInner hn k) M o K (interiorEmptyHistory B S) y))) =
    toLex (o,toLex (Sum.inr (genLowerValue (actualInner hn k) M o K (B.append S) y)))
  rw [genLowerValue_eq_of_mem _ _ hpnew,genLowerValue_eq_of_mem _ _ hp]
  exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy k) =>
    toLex (o,toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy k)))))) hv

end
end Hironaka.HironakaOriginalGeneralSpecialCompanion
