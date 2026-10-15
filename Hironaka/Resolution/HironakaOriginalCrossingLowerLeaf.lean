/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Blowup.BlowupTowerRestrictLengthExact
import Hironaka.Resolution.HironakaOriginalCrossingValueTransport
import Hironaka.Invariant.GeneralValueOrderZero
/-! Actual original canonical crossing lower histories at their monomial leaves.
Complete mathematics written first in `hironaka-original-crossing-lower-leaf-extension.tex`. Positive-order
inner recursion and the full outer general value remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCrossingLowerLeaf
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  StepOneRegime StepOneValue StepOneValueMasked HomogenizedIdealAlong
  HironakaOriginalInteriorEmptyHistory HironakaOriginalCrossingLowerHistory
  HironakaOriginalCrossingValueTransport HironakaOriginalInvariantEmptyInsertion
  BlowupTowerIsomorphism BlowupTowerIsoTail MarkedIdealBiholomorphism
  NonmonomialOrderLocal
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X A Y : CMfd.{u} n}

private def splitLowerData (hn : 0 < n) (k : ℕ) (M : MarkedIdeal n X) (s : ℕ)
    (v : Σ D : CMfd.{u} n, BlowupTower X D × BlowupTower D Y) (y : Y) : Prop :=
  Seq.StepOneValueMasked.LowerDataL (invFamily hn k) M (lowerMarkedM M) s v.2.1 v.2.2 y

/-- Genuine selected lower domain/canonical history/cosupport from ONLY
the original specific-family Step One canonical datum and actual branch. -/
theorem original_canonical_crossing_lower_data (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S))
    (y : Y) (hy : y ∈ (geoTransformAlong M (H.append S)).cosupp)
    (hns : ¬ IsSpecial M (H.append S) y)
    (hreach : S.length ≤ regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y) :
    let ℓ := level M (H.append S) y
    let r := regimeRun (stepRegime M ℓ) (H.append S) y
    let a := r-S.length
    Seq.StepOneValueMasked.LowerDataL (invFamily hn k) M (lowerMarkedM M) ℓ
      (head H a) ((tail H a).append S) y := by
  dsimp only
  obtain ⟨ht,_,hcos⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn k) M hM hmax hn (H.append S) hcan
  have hc := (Seq.StepOneBridge.isCanonical_iff (invFamily hn k) M hM hmax hn (H.append S)).mp hcan
  have hybar : y ∈ (geoTransformAlong (barMarked M) (H.append S)).cosupp := hcos.symm ▸ hy
  have hd := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical M (k := k+1) (invFamily hn k)
    hM.isWellFormed hM.one_le_d hn hmax hM.dimLE (H.append S) ht hc y hybar hns
  change splitLowerData hn k M (level M (H.append S) y)
    (split (H.append S) (regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y)) y at hd
  rw [split_append_above_tail H S _ hreach] at hd
  exact hd

/-- Actual family transport at a true order-zero branch needs domain and
real testness, with no desired new canonical/value equality certificate. -/
private theorem actual_family_iso_zero (hn : 0 < n) (k : ℕ)
    {D D' Z Z' : CMfd.{u} n} (J : MarkedIdeal n D) (hJ : IsInvDomain k J)
    (Φ : D' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ D)
    {T' : BlowupTower D' Z'} {T : BlowupTower D Z}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Z}
    (hiso : IsTowerIso Φ T' T χ) (ht : IsGeoTestTower J T) (p : Z')
    (h0 : nmOrd (geoTransformAlong J T) (χ p) = 0) :
    (invFamily hn k).inv (MarkedIdeal.pullback Φ J) T' p =
      (invFamily hn k).inv J T (χ p) := by
  cases k with
  | zero => rfl
  | succ k =>
    exact GeneralValueOrderZero.genInv_isTowerIso_of_nmOrd_eq_zero
      (fun {D} L {Z} Q q => Seq.StepOneValueMasked.stepOneInvM (X := D) (invFamily hn k) L (Y := Z) Q q)
      hn hJ Φ hiso ht p h0

/-- A genuine whole restricted-history leaf, including its actual new
open membership. It is consumed below with original-derived lower data. -/
theorem restricted_interior_monomial_leaf (hn : 0 < n) (k : ℕ)
    {D : CMfd.{u} n} (W : Opens D) (J : MarkedIdeal n W) (hJ : IsInvDomain k J)
    (B : BlowupTower D A) (S : BlowupTower A Y) (hS : 0 < S.length)
    (ht : IsGeoTestTower J (restrict W (B.append S)))
    (p : openPreimage (B.append S) W)
    (h0 : nmOrd (geoTransformAlong J (restrict W (B.append S))) p = 0) :
    ∃ hp' : (interiorEmptyHistory B S).proj (p : Y) ∈ W,
      (invFamily hn k).inv J (restrict W (interiorEmptyHistory B S))
          (⟨(p : Y),hp'⟩ : openPreimage (interiorEmptyHistory B S) W) =
        shiftFamily k (J.E.length + B.length)
          ((invFamily hn k).inv J (restrict W (B.append S)) p) := by
  let Φ := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) W) ∞
  let B' := restrict W B
  let S' := restrict (openPreimage B W) S
  let χ := opensCongr (n := n) (openPreimage_append B S W).symm
  let q : openPreimage S (openPreimage B W) := χ p
  have hi : IsTowerIso Φ (restrict W (B.append S)) (B'.append S') χ :=
    isTowerIso_restrict_append W B S
  have hpull : MarkedIdeal.pullback Φ J = J :=
    ContactCanonicalAlong.pullback_id J hJ.isWellFormed.isCoherent
  have hpull' : MarkedIdeal.pullback Φ.symm J = J :=
    ContactCanonicalAlong.pullback_id J hJ.isWellFormed.isCoherent
  have ht' : IsGeoTestTower J (B'.append S') := by
    have h := (IsTowerIso.isGeoTestTower_iff Φ.symm hJ.isWellFormed.isClosedSubmanifold_N
      hJ.isWellFormed.isCoherent hi.symm).mpr ht
    rwa [hpull'] at h
  have hq : χ.symm q = p := χ.symm_apply_apply p
  have hn0 : nmOrd (geoTransformAlong J (B'.append S')) q = 0 := by
    have h := nmOrd_geoTransformAlong_isTowerIso hn Φ.symm hJ hi.symm ht q
    rw [hpull',hq] at h
    exact h.trans h0
  have hvold : (invFamily hn k).inv J (B'.append S') q =
      (invFamily hn k).inv J (restrict W (B.append S)) p := by
    have h := actual_family_iso_zero hn k J hJ Φ.symm hi.symm ht q (by rwa [hq])
    rwa [hpull',hq] at h
  have htB : IsGeoTestTower J B' := (isGeoTestTower_append_iff J B' S').mp ht' |>.1
  have hs' : 0 < S'.length := by rw [length_restrict];exact hS
  have htn : IsGeoTestTower J (interiorEmptyHistory B' S') :=
    (isGeoTestTower_interior_empty_iff (X := CMfd.of (n := n) W)
      J hJ.isWellFormed B' htB S').mpr ht'
  have hn0n : nmOrd (geoTransformAlong J (interiorEmptyHistory B' S')) q = 0 :=
    (nmOrd_interior_empty_nonempty (X := CMfd.of (n := n) W)
      J hJ.isWellFormed B' htB S' hs' q).trans hn0
  have hleaf := invFamily_interior_monomial_leaf (X := CMfd.of (n := n) W)
    hn k J hJ.isWellFormed B' htB S' hs' q hn0
  have hp' : (interiorEmptyHistory B S).proj (p : Y) ∈ W := by
    rw [proj_interiorEmptyHistory]
    exact p.2
  refine ⟨hp',?_⟩
  let p' : openPreimage (interiorEmptyHistory B S) W := ⟨(p : Y),hp'⟩
  let χ' := opensCongr (n := n) (openPreimage_append
    (B.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) S W).symm
  have hpoint : χ' p' = q := by apply Subtype.ext;rfl
  have hvnew := actual_family_iso_zero hn k J hJ Φ
    (actual_restricted_empty_history W B S) htn p' (by
      change nmOrd (geoTransformAlong J (interiorEmptyHistory B' S')) (χ' p') = 0
      rw [hpoint]
      exact hn0n)
  rw [hpull] at hvnew
  change (invFamily hn k).inv J (restrict W (interiorEmptyHistory B S)) p' =
    (invFamily hn k).inv J (interiorEmptyHistory B' S') (χ' p') at hvnew
  rw [hpoint,hleaf,hvold] at hvnew
  simpa only [B',length_restrict] using hvnew

private def splitLowerValue (hn : 0 < n) (k : ℕ) (M : MarkedIdeal n X) (s : ℕ)
    (v : Σ D : CMfd.{u} n, BlowupTower X D × BlowupTower D Y) (y : Y) : WithTop (ValTy k) :=
  Seq.StepOneValueMasked.lowerValueL (invFamily hn k) M (lowerMarkedM M) s v.2.1 v.2.2 y

open Classical in
private def fixedLowerValue (hn : 0 < n) (k : ℕ) (M : MarkedIdeal n X) (s : ℕ)
    {D : CMfd.{u} n} (K : BlowupTower X D) (z : D) (Q : BlowupTower D Y) (y : Y) : WithTop (ValTy k) :=
  if h : Q.proj y ∈ lowerMask M s K z then
    ((invFamily hn k).inv (lowerMarkedM M s K z) (restrict (lowerMask M s K z) Q)
      (⟨y,h⟩ : openPreimage Q (lowerMask M s K z)) : WithTop (ValTy k))
  else ⊤

/-- The ORIGINAL canonical input supplies the genuine lower witness and
whole Step One crossing formula on its ACTUAL monomial-leaf branch.
No lower-domain/test/record/canonical/value certificate is a caller premise. -/
theorem original_canonical_crossing_stepOne_leaf (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y) (hS : 0 < S.length)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S))
    (y : Y) (hy : y ∈ (geoTransformAlong M (H.append S)).cosupp)
    (hns : ¬ IsSpecial M (H.append S) y)
    (hreach : S.length ≤ regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y) :
    let ℓ := level M (H.append S) y
    let r := regimeRun (stepRegime M ℓ) (H.append S) y
    let a := r-S.length
    let K := head H a
    let B := tail H a
    let p := (B.append S).proj y
    let W := lowerMask M ℓ K p
    let J := lowerMarkedM M ℓ K p
    ∃ hp : p ∈ W,
      IsInvDomain k J ∧ IsCanonical J ((invFamily hn k).inv J) (restrict W (B.append S)) ∧
      (⟨y,hp⟩ : openPreimage (B.append S) W) ∈
        (geoTransformAlong J (restrict W (B.append S))).cosupp ∧
      (nmOrd (geoTransformAlong J (restrict W (B.append S)))
          (⟨y,hp⟩ : openPreimage (B.append S) W) = 0 →
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) y =
          pairShift (shiftFamily k (J.E.length+B.length))
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y)) := by
  classical
  dsimp only
  obtain ⟨hp,hdom,hcanL,hcos⟩ := original_canonical_crossing_lower_data hn k M hM hmax H S hcan y hy hns hreach
  refine ⟨hp,hdom,hcanL,hcos,?_⟩
  intro h0
  let ℓ := level M (H.append S) y
  let r := regimeRun (stepRegime M ℓ) (H.append S) y
  let K := head H (r-S.length)
  let B := tail H (r-S.length)
  let W := lowerMask M ℓ K ((B.append S).proj y)
  let J := lowerMarkedM M ℓ K ((B.append S).proj y)
  have htestL := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn k).isInvValue hdom _ hcanL
  obtain ⟨hpnew,hval⟩ := restricted_interior_monomial_leaf hn k W J hdom B S hS htestL ⟨y,hp⟩ h0
  have hbar := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn k) M hM hmax hn (H.append S) hcan).1
  have hH := (isGeoTestTower_append_iff (barMarked M) H S).mp hbar |>.1
  have hlevel : level M (interiorEmptyHistory H S) y = ℓ :=
    level_dictionary M hM.isWellFormed H hH S y
  have hnewns : ¬ IsSpecial M (interiorEmptyHistory H S) y :=
    fun h => hns ((isSpecial_dictionary M hM.isWellFormed H hH S y).mp h)
  have hc := actual_crossing_selected_splits M hM.isWellFormed H hH S y hns hreach
  rw [hlevel] at hc
  have hnewcut := hc.2.2
  rw [hc.1] at hnewcut
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_neg hns,if_neg hnewns,hlevel,hc.1]
  change toLex (ℓ,splitLowerValue hn k M ℓ (split (interiorEmptyHistory H S) (r+1)) y) =
    pairShift (shiftFamily k (J.E.length+B.length))
      (toLex (ℓ,splitLowerValue hn k M ℓ (split (H.append S) r) y))
  simp only [pairShift,ofLex_toLex]
  apply congrArg (fun v : WithTop (ValTy k) => toLex (ℓ,v))
  rw [hnewcut,hc.2.1]
  change fixedLowerValue hn k M ℓ K ((interiorEmptyHistory B S).proj y)
      (interiorEmptyHistory B S) y =
    WithTop.map (shiftFamily k (J.E.length+B.length))
      (fixedLowerValue hn k M ℓ K ((B.append S).proj y) (B.append S) y)
  rw [proj_interiorEmptyHistory]
  unfold fixedLowerValue
  rw [dif_pos hpnew,dif_pos hp]
  exact congrArg (fun v : ValTy k => (v : WithTop (ValTy k))) hval

end
end Hironaka.HironakaOriginalCrossingLowerLeaf
