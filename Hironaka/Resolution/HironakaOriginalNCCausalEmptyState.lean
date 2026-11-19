import Hironaka.Resolution.HironakaOriginalNCCausalHistoryValue
import Hironaka.Resolution.HironakaOriginalOldBranchAppend
import Hironaka.Resolution.HironakaOriginalOldBranchCountDrop

set_option autoImplicit false

/-!
# The actual step/phase update for the SAME original causal birth state

The invariant object is precisely CausalHistoryValue.causalHistoryValue.
This module proves the geometric low-count state update, including true
new birth years at actual drops and SAME-year extension by an actual empty
restricted blowup when count does not drop. Every actual empty year remains.

The phase theorem has an explicit generic actual-centre lower-bound domain.
It is not a final natural driver taking a caller centre/count certificate.
The natural highest phase must produce this geometry internally, before the
finite phase induction yields the original causal canonical driver.

Blueprint: hironaka-original-nc-causal-empty-state-extension.tex.
Source-only draft; no kernel-check claim.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCCausalEmptyState

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen NormalCrossings
  HomogenizedGlueingTower MemberInterTowerAlong
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaOriginalOldBranchOpenHistory HironakaOriginalOldBranchCountDrop
  HironakaOriginalNCCountHistory HironakaOriginalNCCausalHistoryValue
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Actual-centre geometry, not a conclusion about canonicality or birth
emptiness. The current count is read on the whole original appended history. -/
def CentresHaveOldCountAtLeast (H : Set X) (T : BlowupTower X Y) (r : ℕ) :
    {Z : CMfd.{u} n} → BlowupTower Y Z → Prop
  | _, .refl => True
  | _, .step P C _ _ => CentresHaveOldCountAtLeast H T r P ∧
      ∀ c ∈ C, r ≤ oldCount H (T.append P) c

private theorem count_congr {B : Type u} [TopologicalSpace B]
    [ChartedSpace (ComplexModel n) B] {F G : Set B}
    (hF : IsNormalCrossingsCarrier (n := n) F) (hG : IsNormalCrossingsCarrier (n := n) G)
    (he : F = G) (b : B) : branchMultiplicity hF b = branchMultiplicity hG b := by
  subst G
  rfl

private theorem birthYear_step_eq_of_count_eq {C : Set Y} {π : Z → Y}
    (T : BlowupTower X Y) (hπ : IsBlowupAlong n C π) (H : Set X) (y : Z)
    (he : oldCount H (.step T C π hπ) y = oldCount H T (π y)) :
    birthYear H (.step T C π hπ) y = birthYear H T (π y) := by
  have hb := birthYear_le_length H T (π y)
  have hLe : birthYear H (.step T C π hπ) y ≤ birthYear H T (π y) := by
    apply Nat.find_min'
    simpa only [countAt, if_pos hb, he] using birthYear_spec H T (π y)
  have hNewLe : birthYear H (.step T C π hπ) y ≤ T.length := hLe.trans hb
  apply le_antisymm hLe
  apply Nat.find_min'
  simpa only [countAt, if_pos hNewLe, he] using birthYear_spec H (.step T C π hπ) y

private theorem birthYear_step_eq_length_of_count_drop {C : Set Y} {π : Z → Y}
    (T : BlowupTower X Y) (hπ : IsBlowupAlong n C π) (H : Set X) (y : Z)
    (hAnti : Antitone (countAt H T (π y)))
    (hDrop : oldCount H (.step T C π hπ) y < oldCount H T (π y)) :
    birthYear H (.step T C π hπ) y = (BlowupTower.step T C π hπ).length := by
  have hMax := birthYear_le_length H (.step T C π hπ) y
  have hNot : ¬ birthYear H (.step T C π hπ) y ≤ T.length := by
    intro hb
    have hs := birthYear_spec H (.step T C π hπ) y
    simp only [countAt, if_pos hb] at hs
    have hLower : oldCount H T (π y) ≤ countAt H T (π y) (birthYear H (.step T C π hπ) y) :=
      (countAt_length H T (π y)).symm.trans_le (hAnti hb)
    omega
  rw [BlowupTower.length_step] at hMax ⊢
  omega

private theorem endpoint_count_le_of_empty_causalBirthTail
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (x : Y)
    (he : IsEmptyTower (causalBirthTail H T x)) :
    ∀ p : openPreimage (tail T (T.length - birthYear H T x)) (causalBirthOpen H T x),
      oldCount H T p.val ≤ oldCount H T x := by
  let k := T.length - birthYear H T x
  let K := head T k
  let Q := tail T k
  let W := causalBirthOpen H T x
  let S := causalBirthTail H T x
  let J := openPreimage Q W
  let hc := currentPair_head M hN hI h T hT hHistory k
  let hW := boundaryAdapted_open W hc
  let hcT := exists_current_pair_of_original_branch_history M hN hI h T hT hHistory
  let hNCJ := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open J hcT)
  have hOld : strictAlong S ((Subtype.val : W → (split T k).1) ⁻¹' strictAlong K H) =
      (Subtype.val : J → Y) ⁻¹' strictAlong T H := by
    change strictAlong (restrict W Q) ((Subtype.val : W → (split T k).1) ⁻¹' strictAlong K H) = _
    rw [strictAlong_restrict W Q (strictAlong K H)]
    have hCompose : strictAlong Q (strictAlong K H) = strictAlong T H := by
      rw [← MemberInterLocusAlong.strictAlong_append, head_append_tail T k]
    rw [hCompose]
  have hNCS : IsNormalCrossingsCarrier (n := n)
      (strictAlong S ((Subtype.val : W → (split T k).1) ⁻¹' strictAlong K H)) := hOld.symm ▸ hNCJ
  have hEmptyCount := branchMultiplicity_empty_tower
    (isNormalCrossingsCarrier_of_boundaryAdapted hW) S he hNCS
  have hBound : ∀ z : W,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z ≤ oldCount H T x := by
    intro z
    have hCount := (branchMultiplicity_open W (isNormalCrossingsCarrier_of_boundaryAdapted hc)
      (isNormalCrossingsCarrier_of_boundaryAdapted hW) z).trans
        (oldCount_eq K (isNormalCrossingsCarrier_of_boundaryAdapted hc) z.val).symm
    exact hCount.trans_le z.property
  intro p
  calc
    _ = branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcT) p.val :=
      oldCount_eq T (isNormalCrossingsCarrier_of_boundaryAdapted hcT) p.val
    _ = branchMultiplicity hNCJ p :=
      (branchMultiplicity_open J (isNormalCrossingsCarrier_of_boundaryAdapted hcT) hNCJ p).symm
    _ = branchMultiplicity hNCS p := (count_congr hNCS hNCJ hOld p).symm
    _ = branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) (S.proj p) := hEmptyCount p
    _ ≤ oldCount H T x := hBound (S.proj p)

/-- This is the actual state producer: a strict drop creates a real new birth;
otherwise the SAME birth retains its actual old empty suffix and appends a
true empty restricted blowup because the entire endpoint window misses C. -/
theorem empty_causalBirthTail_step_of_high_count_centre
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hStep : IsGeoTestTower M (.step T C π hπ))
    (hHistoryStep : IsOriginalBranchTestTower M H (.step T C π hπ))
    (r : ℕ) (hC : ∀ c ∈ C, r ≤ oldCount H T c)
    (hState : ∀ x ∈ (geoTransformAlong M T).cosupp,
      oldCount H T x < r → IsEmptyTower (causalBirthTail H T x)) :
    ∀ y ∈ (geoTransformAlong M (.step T C π hπ)).cosupp,
      oldCount H (.step T C π hπ) y < r → IsEmptyTower (causalBirthTail H (.step T C π hπ) y) := by
  have hHistoryT : IsOriginalBranchTestTower M H T :=
    fun U B hSNC hUnion => (hHistoryStep U B hSNC hUnion).1
  intro y hy hLow
  have hLe := oldCount_step_le M hN hI h T C π hπ hStep hHistoryStep y
  by_cases he : oldCount H (.step T C π hπ) y = oldCount H T (π y)
  · have hOldLow : oldCount H T (π y) < r := by rw [he] at hLow; exact hLow
    have hTI := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      (𝔪 := M) (hN ▸ isClosedSubmanifold_univ) hI T hStep.1
    let U : BlowupTower Y Z := .step .refl C π hπ
    have hU : IsGeoTestTower (geoTransformAlong M T) U := ⟨trivial, hStep.2⟩
    have hx : π y ∈ (geoTransformAlong M T).cosupp :=
      TransformOffCentre.cosupp_geoTransformAlong_subset (geoTransformAlong M T)
        hTI.1 hTI.2 U hU hy
    have hOldEmpty := hState (π y) hx hOldLow
    have hβ := birthYear_step_eq_of_count_eq T hπ H y he
    have hIndex : (BlowupTower.step T C π hπ).length - birthYear H (.step T C π hπ) y =
        (T.length - birthYear H T (π y)) + 1 := by
      rw [BlowupTower.length_step, hβ]
      have hb := birthYear_le_length H T (π y)
      omega
    have hCentreEmpty : (Subtype.val :
        openPreimage (tail T (T.length - birthYear H T (π y))) (causalBirthOpen H T (π y)) → Y) ⁻¹' C = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hb := endpoint_count_le_of_empty_causalBirthTail M hN hI h T hStep.1 hHistoryT (π y) hOldEmpty p
      have hc := hC p.val hp
      omega
    change IsEmptyTower (restrict
      (oldCountLowOpen H (head (.step T C π hπ)
        ((BlowupTower.step T C π hπ).length - birthYear H (.step T C π hπ) y))
        (oldCount H (.step T C π hπ) y))
      (tail (.step T C π hπ)
        ((BlowupTower.step T C π hπ).length - birthYear H (.step T C π hπ) y)))
    rw [hIndex, he]
    change IsEmptyTower (causalBirthTail H T (π y)) ∧
      (Subtype.val : openPreimage (tail T (T.length - birthYear H T (π y)))
        (causalBirthOpen H T (π y)) → Y) ⁻¹' C = ∅
    exact ⟨hOldEmpty, hCentreEmpty⟩
  · have hDrop : oldCount H (.step T C π hπ) y < oldCount H T (π y) := by omega
    have hβ := birthYear_step_eq_length_of_count_drop T hπ H y
      (countAt_antitone M hN hI h T hStep.1 hHistoryT (π y)) hDrop
    change IsEmptyTower (restrict
      (oldCountLowOpen H (head (.step T C π hπ)
        ((BlowupTower.step T C π hπ).length - birthYear H (.step T C π hπ) y))
        (oldCount H (.step T C π hπ) y))
      (tail (.step T C π hπ)
        ((BlowupTower.step T C π hπ).length - birthYear H (.step T C π hπ) y)))
    rw [hβ, Nat.sub_self]
    trivial

/-- Actual high-centre geometry propagates the SAME original causal state
through the entire prescribed phase, including all internal strict drops.
The natural algorithm must produce its geometry internally; this generic
theorem adds no certificate to the original-data final driver inputs. -/
theorem empty_causalBirthTail_after_high_phase
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistoryT : IsOriginalBranchTestTower M H T)
    (hState : HasEmptyCausalBirthTails M H T) (r : ℕ) :
    ∀ {Z : CMfd.{u} n} (P : BlowupTower Y Z),
      IsGeoTestTower (geoTransformAlong M T) P →
      IsOriginalBranchTestTower (geoTransformAlong M T) (strictAlong T H) P →
      CentresHaveOldCountAtLeast H T r P →
      ∀ z ∈ (geoTransformAlong M (T.append P)).cosupp,
        oldCount H (T.append P) z < r → IsEmptyTower (causalBirthTail H (T.append P) z)
  | _, .refl, _hP, _hHistoryP, _hHigh => fun z hz _hLow => hState z hz
  | _, .step P C π hπ, hP, hHistoryP, hHigh => by
      have hHistoryPrefix : IsOriginalBranchTestTower (geoTransformAlong M T) (strictAlong T H) P :=
        fun U B hSNC hUnion => (hHistoryP U B hSNC hUnion).1
      have ih := empty_causalBirthTail_after_high_phase M hN hI h T hT hHistoryT hState r
        P hP.1 hHistoryPrefix hHigh.1
      have hAppend : IsGeoTestTower M (T.append (.step P C π hπ)) :=
        (isGeoTestTower_append_iff M T (.step P C π hπ)).mpr ⟨hT, hP⟩
      have hHistoryAppend : IsOriginalBranchTestTower M H (T.append (.step P C π hπ)) :=
        isOriginalBranchTestTower_append M hN hI T (.step P C π hπ) hT hHistoryT hHistoryP
      exact empty_causalBirthTail_step_of_high_count_centre M hN hI h
        (T.append P) C π hπ hAppend hHistoryAppend r hHigh.2 ih

end
end Hironaka.HironakaOriginalNCCausalEmptyState
