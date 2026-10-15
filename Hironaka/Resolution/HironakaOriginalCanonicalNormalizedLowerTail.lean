/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCrossingLowerLeaf
/-! Whole original canonical lower-history normalization at EVERY order.
Complete mathematics written first in `hironaka-original-canonical-normalized-lower-tail-extension.tex`. This uses the
actual Seq invariant; no uniform noncompact finiteness is assumed.
Additional interior empty-step positive recursion remains open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCanonicalNormalizedLowerTail
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  BlowupTowerIsomorphism BlowupTowerIsoTail CanonicalCentres StepOneRegime
  StepOneValue StepOneValueMasked HomogenizedIdealAlong
  HironakaOriginalCrossingLowerLeaf
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- Original canonical inputs INTERNALLY give the actual normalized lower
canonical history/cosupport/full value at EVERY lower nonmonomial order.
No supplied normalized history/value certificate and no uniform finiteness. -/
theorem original_canonical_crossing_normalized_lower_data (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S))
    (y : Y) (hy : y ∈ (geoTransformAlong M (H.append S)).cosupp)
    (hns : ¬ IsSpecial M (H.append S) y)
    (hreach : S.length ≤ regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y) :
    let ℓ := level M (H.append S) y
    let r := regimeRun (stepRegime M ℓ) (H.append S) y
    let K := head H (r-S.length)
    let B := tail H (r-S.length)
    let p := (B.append S).proj y
    let W := lowerMask M ℓ K p
    let J := lowerMarkedM M ℓ K p
    let N := (restrict W B).append (restrict (openPreimage B W) S)
    ∃ hp : p∈W,
      let q := opensCongr (n := n) (openPreimage_append B S W).symm
        (⟨y,hp⟩ : openPreimage (B.append S) W)
      IsInvDomain k J ∧ IsCanonical J ((invFamily hn k).inv J) (restrict W (B.append S)) ∧
      IsCanonical J ((invFamily hn k).inv J) N ∧
      (⟨y,hp⟩ : openPreimage (B.append S) W) ∈
        (geoTransformAlong J (restrict W (B.append S))).cosupp ∧
      q∈(geoTransformAlong J N).cosupp ∧
      (invFamily hn k).inv J N q =
        (invFamily hn k).inv J (restrict W (B.append S)) (⟨y,hp⟩ : openPreimage (B.append S) W) := by
  dsimp only
  obtain ⟨hp,hdom,hcanL,hcos⟩ := original_canonical_crossing_lower_data hn k M hM hmax H S hcan y hy hns hreach
  let ℓ := level M (H.append S) y
  let r := regimeRun (stepRegime M ℓ) (H.append S) y
  let K := head H (r-S.length)
  let B := tail H (r-S.length)
  let W := lowerMask M ℓ K ((B.append S).proj y)
  let J := lowerMarkedM M ℓ K ((B.append S).proj y)
  let N := (restrict W B).append (restrict (openPreimage B W) S)
  let Φ := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) W) ∞
  let χ := opensCongr (n := n) (openPreimage_append B S W).symm
  let p : openPreimage (B.append S) W := ⟨y,hp⟩
  let q := χ p
  have hi : IsTowerIso Φ (restrict W (B.append S)) N χ := isTowerIso_restrict_append W B S
  have hpull : MarkedIdeal.pullback Φ.symm J = J :=
    ContactCanonicalAlong.pullback_id J hdom.isWellFormed.isCoherent
  have hcanN := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso (X := CMfd.of (n := n) W)
    (invFamily hn k) hdom Φ.symm hi.symm hcanL
  rw [hpull] at hcanN
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn k).isInvValue hdom _ hcanL
  have hcN := IsTowerIso.cosupp_geoTransformAlong Φ.symm hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent hi.symm ht
  rw [hpull] at hcN
  have hq : χ.symm q = p := χ.symm_apply_apply p
  have hqcos : q ∈ (geoTransformAlong J N).cosupp := by
    rw [hcN]
    change χ.symm q ∈ (geoTransformAlong J (restrict W (B.append S))).cosupp
    rw [hq]
    exact hcos
  have hv := (invFamily hn k).isInvValue.towerIso Φ.symm J hdom N
    (restrict W (B.append S)) χ.symm hi.symm hcanL q (by rw [hq];exact hcos)
  rw [hpull,hq] at hv
  exact ⟨hp,hdom,hcanL,hcanN,hcos,hqcos,hv⟩

end
end Hironaka.HironakaOriginalCanonicalNormalizedLowerTail
