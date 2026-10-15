/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalShortUniformIndex
import Hironaka.Resolution.HironakaOriginalCanonicalNormalizedLowerTail
/-! Actual original whole lower length and exact crossing index.
Complete Mathematics.tex preceded proof. Positive recursive crossing remains open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCrossingExactIndex
noncomputable section
open Classical
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit CanonicalCentres
  StepOneRegime StepOneValue StepOneValueMasked HomogenizedIdealAlong
  InvDomainMemberRestriction InvDomainRebase BoundaryCount NonmonomialOrderLocal
  HironakaOriginalInteriorEmptyHistory HironakaOriginalCrossingLowerHistory
  HironakaOriginalCrossingLowerLeaf HironakaOriginalInvariantEmptyInsertion
  HironakaOriginalShortUniformIndex
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- Actual chosen-contact/member record length, from ORIGINAL bar-test SNC geometry. -/
theorem original_lower_boundary_length_actual_level (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (K : BlowupTower X A) (ht : IsGeoTestTower (barMarked M) K) (p : A) :
    (lowerMarkedM M (level M K p) K p).E.length=M.E.length+K.length-level M K p := by
  let J := geoTransformAlong (barMarked M) K
  have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (StepOneLowerDomain.isWellFormed_barMarked M hM) K ht
  cases hℓ : level M K p with
  | zero =>
    change (J.E.map ((Subtype.val : maskB M K p → A) ⁻¹' ·)).length=M.E.length+K.length-0
    rw [List.length_map]
    exact length_E_geoTransformAlong (barMarked M) K
  | succ s =>
    have hlen : M.E.length≤J.E.length := by
      rw [length_E_geoTransformAlong]
      change M.E.length≤M.E.length+K.length
      omega
    have hc := original_filtered_prefix_exact_count J.E hw.isSNCDivisor p
      M.E.length J.E.length hlen le_rfl
    rw [List.take_length] at hc
    have hlevel : boundaryCount (J.E.take M.E.length) p=s+1 := hℓ
    change ((memberRestrict J (membersThrough J.E (J.E.take M.E.length) p)).E.map
      ((Subtype.val : maskA M K p → A) ⁻¹' ·)).length=M.E.length+K.length-(s+1)
    rw [List.length_map,memberRestrict_membersThrough_E,hc,hlevel]
    rw [length_E_geoTransformAlong]
    rfl

private theorem actual_level_le_initial_boundary (M : MarkedIdeal n X)
    (K : BlowupTower X A) (p : A) : level M K p≤M.E.length := by
  have h := Finset.card_le_univ (Finset.univ.filter fun i : Fin (origMembers M K).length => p∈(origMembers M K).get i)
  change boundaryCount (origMembers M K) p≤M.E.length
  simp only [Fintype.card_fin,origMembers_eq,List.length_map] at h
  exact h

/-- Only original Step One canonical input internally fixes the exact true
crossing lower history position at ALL actual lower orders. -/
theorem original_canonical_crossing_lower_index_exact (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S))
    (y : Y) (hns : ¬ IsSpecial M (H.append S) y)
    (hreach : S.length≤regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y) :
    let ℓ := level M (H.append S) y
    let r := regimeRun (stepRegime M ℓ) (H.append S) y
    let K := head H (r-S.length)
    let B := tail H (r-S.length)
    let J := lowerMarkedM M ℓ K ((B.append S).proj y)
    J.E.length+B.length=M.E.length+H.length-ℓ := by
  dsimp only
  let ℓ := level M (H.append S) y
  let r := regimeRun (stepRegime M ℓ) (H.append S) y
  let K := head H (r-S.length)
  let B := tail H (r-S.length)
  have hbar := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn k) M hM hmax hn (H.append S) hcan).1
  have hH := (isGeoTestTower_append_iff (barMarked M) H S).mp hbar |>.1
  have htK := ((isGeoTestTower_iff_head_tail (barMarked M) H (r-S.length)).mp hH).1
  have hwhole : K.append (B.append S)=H.append S := by
    rw [← BlowupTower.append_assoc,head_append_tail]
  change S.length≤r at hreach
  have hbr : (B.append S).length≤regimeRun (stepRegime M ℓ) (K.append (B.append S)) y := by
    rw [hwhole,BlowupTower.length_append,length_tail]
    change min (r-S.length) H.length+S.length≤r
    omega
  have hreg : stepRegime M ℓ (K.append (B.append S)) y := by
    rw [hwhole]
    exact ⟨rfl,hns⟩
  have hbase := regime_at_base_of_reaching_run (stepRegime M ℓ) K (B.append S) y hreg hbr
  have hlen := original_lower_boundary_length_actual_level M hM.isWellFormed K htK ((B.append S).proj y)
  rw [hbase.1] at hlen
  have hle := actual_level_le_initial_boundary M K ((B.append S).proj y)
  rw [hbase.1] at hle
  have hsum : K.length+B.length=H.length := by
    rw [length_head,length_tail]
    omega
  change (lowerMarkedM M ℓ K ((B.append S).proj y)).E.length+B.length=M.E.length+H.length-ℓ
  rw [hlen]
  omega

/-- The genuine canonical crossing leaf now uses the SAME whole history
map as ALL short points. Lower nmOrd=0 remains an explicit honest branch
on internally supplied original lower data; positive recursion is open. -/
theorem original_canonical_crossing_leaf_history_map (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (H : BlowupTower X A) (S : BlowupTower A Y) (hS : 0<S.length)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M) (H.append S))
    (y : Y) (hy : y∈(geoTransformAlong M (H.append S)).cosupp)
    (hns : ¬ IsSpecial M (H.append S) y)
    (hreach : S.length≤regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y) :
    let ℓ := level M (H.append S) y
    let r := regimeRun (stepRegime M ℓ) (H.append S) y
    let K := head H (r-S.length)
    let B := tail H (r-S.length)
    let p := (B.append S).proj y
    let W := lowerMask M ℓ K p
    let J := lowerMarkedM M ℓ K p
    ∃ hp : p∈W,
      IsInvDomain k J ∧ IsCanonical J ((invFamily hn k).inv J) (restrict W (B.append S)) ∧
      (⟨y,hp⟩ : openPreimage (B.append S) W)∈(geoTransformAlong J (restrict W (B.append S))).cosupp ∧
      (nmOrd (geoTransformAlong J (restrict W (B.append S))) (⟨y,hp⟩ : openPreimage (B.append S) W)=0 →
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (interiorEmptyHistory H S) y=
          historyStepShift k (M.E.length+H.length)
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y)) := by
  dsimp only
  obtain ⟨hp,hdom,hcanL,hcos,hval⟩ :=
    original_canonical_crossing_stepOne_leaf hn k M hM hmax H S hS hcan y hy hns hreach
  refine ⟨hp,hdom,hcanL,hcos,?_⟩
  intro h0
  have hv := hval h0
  have hi := original_canonical_crossing_lower_index_exact hn k M hM hmax H S hcan y hns hreach
  dsimp only at hi
  rw [hi] at hv
  have hfst := Seq.StepOneValueMasked.stepOneInvL_fst (invFamily hn k) M (lowerMarkedM M) (H.append S) y
  change (ofLex (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) M (H.append S) y)).1=
    level M (H.append S) y at hfst
  simpa only [pairShift,historyStepShift,hfst] using hv

end
end Hironaka.HironakaOriginalCrossingExactIndex
