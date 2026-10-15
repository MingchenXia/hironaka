/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalShortLowerValues
/-! Actual test-history geometry and the full-family crossing monomial leaf.
Complete mathematics written first in `hironaka-original-crossing-value-transport-extension.tex`. Positive-order
recursive crossing transport and complete outer history remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCrossingValueTransport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  BlowupTowerSplit NormalCrossings MonomialInvariantEmptyMember CanonicalCentres
  HironakaOriginalInvariantEmptyInsertion HironakaOriginalInteriorEmptyHistory
  MarkedIdealBiholomorphism NonmonomialOrderLocal GeneralValue MonomialStepAlong
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- A private actual-chart transfer; matching is needed ONLY for members
through the real centre point. No global index/preimage injectivity is assumed. -/
private theorem hasNormalCrossings_of_through_members (C : Set X) (E F : List (Set X))
    (hE : HasNormalCrossings n C E)
    (hFE : ∀ x ∈ C, ∀ i : Fin F.length, x ∈ F.get i →
      ∃ j : Fin E.length, E.get j = F.get i) : HasNormalCrossings n C F := by
  classical
  intro x hx
  obtain ⟨S₀,S,hcoord,hcard⟩ := hE x hx
  let idx (i : Fin F.length) (hi : x ∈ F.get i) : Fin E.length := (hFE x hx i hi).choose
  have hidx (i : Fin F.length) (hi : x ∈ F.get i) : E.get (idx i hi) = F.get i :=
    (hFE x hx i hi).choose_spec
  let V (i : Fin F.length) : Finset (Fin n) := if hi : x ∈ F.get i then S (idx i hi) else ∅
  refine ⟨S₀,V,?_,?_⟩
  · obtain ⟨Φ,hsrc,h0,hΦ⟩ := hcoord
    refine ⟨Φ,hsrc,h0,?_⟩
    intro o
    cases o with
    | none => exact hΦ none
    | some i =>
      intro hi y hy hyΦ
      change x ∈ F.get i at hi
      change (y ∈ F.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (V i))
      simp only [V,dif_pos hi]
      have hxj : x ∈ E.get (idx i hi) := (hidx i hi).symm ▸ hi
      have he := hΦ (some (idx i hi)) hxj hy hyΦ
      change (y ∈ E.get (idx i hi) ↔
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S (idx i hi))) at he
      rw [hidx i hi] at he
      exact he
  · intro i hi
    simp only [V,dif_pos hi]
    exact hcard (idx i hi) ((hidx i hi).symm ▸ hi)

/-- All actual centre normal-crossings conditions ignore the empty entry,
while the full ordered boundary list itself is retained. -/
theorem hasNormalCrossings_insertIdx_empty_iff (C : Set X) (E : List (Set X))
    {j : ℕ} (hj : j ≤ E.length) :
    HasNormalCrossings n C (E.insertIdx j ∅) ↔ HasNormalCrossings n C E := by
  constructor
  · intro h
    apply hasNormalCrossings_of_through_members C (E.insertIdx j ∅) E h
    intro _ _ i _
    exact List.mem_iff_get.mp ((List.mem_insertIdx hj).mpr (Or.inr (List.get_mem E i)))
  · intro h
    apply hasNormalCrossings_of_through_members C E (E.insertIdx j ∅) h
    intro x _ i hi
    rcases (List.mem_insertIdx hj).mp (List.get_mem (E.insertIdx j ∅) i) with he | he
    · rw [he] at hi
      exact False.elim hi
    · exact List.mem_iff_get.mp he

theorem isAdmissibleCentre_insertEmpty_iff (M : MarkedIdeal n X)
    {j : ℕ} (hj : j ≤ M.E.length) (C : Set X) :
    (insertEmpty j M).IsAdmissibleCentre C ↔ M.IsAdmissibleCentre C := by
  change (IsClosedSubmanifold n C ∧ C ⊆ M.cosupp ∧
    HasNormalCrossings n C (M.E.insertIdx j ∅)) ↔
      (IsClosedSubmanifold n C ∧ C ⊆ M.cosupp ∧ HasNormalCrossings n C M.E)
  rw [hasNormalCrossings_insertIdx_empty_iff C M.E hj]

/-- TRUE whole testness under an initial boundary insertion, proved from
actual admissibility and full transformed records, not a value certificate. -/
theorem isGeoTestTower_insertEmpty_iff (M : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ M.E.length) : ∀ {Y : CMfd.{u} n} (R : BlowupTower X Y),
      IsGeoTestTower (insertEmpty j M) R ↔ IsGeoTestTower M R
  | _, .refl => Iff.rfl
  | _, .step R C π hπ => by
    rw [isGeoTestTower_step_iff,isGeoTestTower_step_iff,
      isGeoTestTower_insertEmpty_iff M hj R,geoTransformAlong_insertEmpty M hj R,
      isAdmissibleCentre_insertEmpty_iff _ (le_length_E_geoTransformAlong M hj R)]

private theorem identity_empty_base (K : MarkedIdeal n A) (hK : K.IsWellFormed) :
    MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv (emptyStepBase K id) K ∧
      (emptyStepBase K id).ideal.IsCoherent := by
  have hr := restrictEquiv_emptyStepBase_pullback K BlowupExistenceCodimOne.isBlowupAlong_id_empty
    hK.isClosedSubmanifold_N.1 hK.isSNCDivisor.1
  rw [ContactCanonicalAlong.pullback_id K hK.isCoherent] at hr
  exact ⟨hr,(GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hK
    (isAdmissibleCentre_empty K) BlowupExistenceCodimOne.isBlowupAlong_id_empty).isCoherent⟩

/-- The actual SAME original test history across the genuine interior
identity empty step, including empty tails. Inserted-tail testness is a
proved conclusion from original WF and actual head testness. -/
theorem isGeoTestTower_interior_empty_iff (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H) (S : BlowupTower A Y) :
    IsGeoTestTower M (interiorEmptyHistory H S) ↔ IsGeoTestTower M (H.append S) := by
  have hK := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM H hH
  obtain ⟨hr,hB⟩ := identity_empty_base (geoTransformAlong M H) hK
  have hBN : IsClosed (emptyStepBase (geoTransformAlong M H) id).N := by
    rw [hr.N_eq]
    exact hK.isClosedSubmanifold_N.1
  have hw := ((MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv
    hr hBN hB hK.isCoherent).2 S).1
  have hnewH : IsGeoTestTower M (H.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) :=
    (isGeoTestTower_step_iff M H ∅ id _).mpr ⟨hH,isAdmissibleCentre_empty _⟩
  have ht : IsGeoTestTower
      (geoTransformAlong M (H.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty)) S ↔
      IsGeoTestTower (geoTransformAlong M H) S := by
    rw [geoTransformAlong_step,geoTransform_empty_eq_insertEmpty]
    exact (isGeoTestTower_insertEmpty_iff _ (by rw [length_E_emptyStepBase]) S).trans hw
  rw [interiorEmptyHistory,isGeoTestTower_append_iff,isGeoTestTower_append_iff]
  exact and_congr (iff_of_true hnewH hH) ht

/-- The actual original nonmonomial order on the same unre-based histories,
internally computed from the genuine nonempty-tail whole-record dictionary. -/
theorem nmOrd_interior_empty_nonempty (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H)
    (S : BlowupTower A Y) (hS : 0 < S.length) (y : Y) :
    nmOrd (geoTransformAlong M (interiorEmptyHistory H S)) y =
      nmOrd (geoTransformAlong M (H.append S)) y := by
  rw [whole_record_of_nonempty_tail M hM H hH S hS]
  apply nmOrd_insertEmpty
  rw [length_E_geoTransformAlong,BlowupTower.length_append]
  omega

/-- At EVERY recursive dimension the actual monomial leaf has the true
index map in the SAME initial datum and original unre-based histories. -/
theorem invFamily_interior_monomial_leaf (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H)
    (S : BlowupTower A Y) (hS : 0 < S.length) (y : Y)
    (h0 : nmOrd (geoTransformAlong M (H.append S)) y = 0) :
    (invFamily hn k).inv M (interiorEmptyHistory H S) y =
      shiftFamily k (M.E.length + H.length) ((invFamily hn k).inv M (H.append S) y) := by
  cases k with
  | zero => rfl
  | succ k =>
    change genInv (fun {D} J {B} R z =>
        Seq.StepOneValueMasked.stepOneInvM (X := D) (invFamily hn k) J (Y := B) R z)
        M (interiorEmptyHistory H S) y =
      generalShift (M.E.length + H.length) (pairShift (shiftFamily k 0))
        (genInv (fun {D} J {B} R z =>
          Seq.StepOneValueMasked.stepOneInvM (X := D) (invFamily hn k) J (Y := B) R z)
          M (H.append S) y)
    unfold generalShift genInv genSecond
    rw [nmOrd_interior_empty_nonempty M hM H hH S hS y,h0]
    simp only [ofLex_toLex]
    have hj : M.E.length + H.length ≤ (geoTransformAlong M (H.append S)).E.length := by
      rw [length_E_geoTransformAlong,BlowupTower.length_append]
      omega
    have hgamma := gammaAlong_insertEmpty (geoTransformAlong M (H.append S)) hj y
    rw [← whole_record_of_nonempty_tail M hM H hH S hS] at hgamma
    exact congrArg (fun v : WithBot MonomialInvariant.Val =>
      (toLex (0,toLex (Sum.inl v)) : ValTy (k+1))) hgamma

/-- The actual entire unre-based zero-order spectrum reflects all three
comparisons under one genuine original future index at every k. -/
theorem invFamily_interior_monomial_comparisons (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower M H)
    (S : BlowupTower A Y) (hS : 0 < S.length) (y z : Y)
    (hy : nmOrd (geoTransformAlong M (H.append S)) y = 0)
    (hz : nmOrd (geoTransformAlong M (H.append S)) z = 0) :
    let v := (invFamily hn k).inv M (H.append S) y
    let w := (invFamily hn k).inv M (H.append S) z
    let v' := (invFamily hn k).inv M (interiorEmptyHistory H S) y
    let w' := (invFamily hn k).inv M (interiorEmptyHistory H S) z
    (v' < w' ↔ v < w) ∧ (v' ≤ w' ↔ v ≤ w) ∧ (v' = w' ↔ v = w) := by
  dsimp only
  rw [invFamily_interior_monomial_leaf hn k M hM H hH S hS y hy,
    invFamily_interior_monomial_leaf hn k M hM H hH S hS z hz]
  exact ⟨(strictMono_shiftFamily k (M.E.length + H.length)).lt_iff_lt,
    (strictMono_shiftFamily k (M.E.length + H.length)).le_iff_le,
    (strictMono_shiftFamily k (M.E.length + H.length)).injective.eq_iff⟩

end
end Hironaka.HironakaOriginalCrossingValueTransport
