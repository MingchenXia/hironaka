import Hironaka.Resolution.HironakaActualRetainedBoundaryJointStep
import Hironaka.Resolution.HironakaOriginalInvariantEmptyInsertion
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyFilterComparison

/-! Retained joint inputs across a genuine empty born-boundary slot. -/

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4JointProfileEmptyBorn
noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsTransform
  MonomialInvariantEmptyMember HironakaOriginalInvariantEmptyInsertion HironakaOriginalCrossingValueTransport
  HironakaOriginalBoundaryEmptyFilterComparison
  HironakaActualRetainedBoundaryJointStep HironakaActualFiniteMarkedSumHistories
  HironakaG4PreparedCentreCoordinates NonmonomialOrderLocal
open ResolutionInvariantSpec (IsCanonical)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- An empty born position changes only the boundary record of the whole
native joint mask, including its literal normalized product and factors. -/
theorem jointProfileMarked_insertEmpty_born (N : Set X) (old born : List (Set X))
    (q : ℕ) (P : Finset (Fin old.length)) {j : ℕ} (hj : j ≤ born.length) :
    jointProfileMarked N old (born.insertIdx j ∅) q P =
      insertEmpty j (jointProfileMarked N old born q P) := by
  have hProd : canonicalProductMarked N old (born.insertIdx j ∅) q =
      insertEmpty j (canonicalProductMarked N old born q) := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
    unfold canonicalProductMarked
    change HironakaSharpActualFiniteMemberProduct.relativeIdealListProduct N
      (canonicalResidualFamily N old (born.insertIdx j ∅)) =
      HironakaSharpActualFiniteMemberProduct.relativeIdealListProduct N (canonicalResidualFamily N old born)
    congr 1
    unfold canonicalResidualFamily
    apply List.map_congr_left
    intro H _hH
    unfold MonomialPartAlong.nonmonomialPartAlong
    rw [monomialPartAlong_insertIdx_empty N _ born hj]
  have hFactor (i : Fin old.length) :
      canonicalFactorMarked N old (born.insertIdx j ∅) i =
        insertEmpty j (canonicalFactorMarked N old born i) := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
    exact monomialPartAlong_insertIdx_empty N _ born hj
  have hSum (A : MarkedIdeal n X) (L : List (MarkedIdeal n X)) :
      finiteSum (insertEmpty j A) (L.map (insertEmpty j)) = insertEmpty j (finiteSum A L) := by
    induction L generalizing A with
    | nil => rfl
    | cons B L ih =>
      change MarkedIdealOperationsTransform.MarkedIdeal.add (insertEmpty j A)
        (finiteSum (insertEmpty j B) (L.map (insertEmpty j))) =
        insertEmpty j (MarkedIdealOperationsTransform.MarkedIdeal.add A (finiteSum B L))
      rw [ih]
      rfl
  unfold jointProfileMarked
  rw [hProd, ← hSum, List.map_map]
  congr 1
  exact List.map_congr_left (fun i _ => hFactor i)

/-- At any native bound, inserting an empty born position preserves literal
canonical and terminal status of the same actual tower. -/
theorem jointProfileMarked_insertEmpty_born_history (hn : 0 < n) (k : ℕ)
    (N : Set X) (old born : List (Set X)) (q : ℕ) (P : Finset (Fin old.length))
    {j : ℕ} (hj : j ≤ born.length) (T : BlowupTower X Y) :
    let M := jointProfileMarked N old born q P
    let M' := jointProfileMarked N old (born.insertIdx j ∅) q P
    (IsCanonical M' ((CanonicalCentres.invFamily hn k).inv M') T ↔
      IsCanonical M ((CanonicalCentres.invFamily hn k).inv M) T) ∧
    (IsGeoResolution M' T ↔ IsGeoResolution M T) := by
  intro M M'
  have hEq : M' = insertEmpty j M := jointProfileMarked_insertEmpty_born N old born q P hj
  have hME : M.E = born := by
    change (finiteSum (canonicalProductMarked N old born q)
      (P.toList.map (canonicalFactorMarked N old born))).E = born
    cases (P.toList.map (canonicalFactorMarked N old born)) <;> rfl
  have hJ : j ≤ M.E.length := hME.symm ▸ hj
  rw [hEq]
  refine ⟨isCanonical_invFamily_insertEmpty_iff hn k M hJ T,?_⟩
  change (IsGeoTestTower (insertEmpty j M) T ∧ _ ) ↔ (IsGeoTestTower M T ∧ _)
  rw [isGeoTestTower_insertEmpty_iff M hJ T,cosupp_geoTransformAlong_insertEmpty M hJ T]

private theorem joint_fields (N : Set X) (old born : List (Set X)) (q : ℕ)
    (P : Finset (Fin old.length)) :
    let M := jointProfileMarked N old born q P
    M.N = N ∧ M.E = born ∧ M.d = q := by
  unfold jointProfileMarked
  cases P.toList with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons i L =>
    refine ⟨rfl,rfl,?_⟩
    change q * (finiteSum (canonicalFactorMarked N old born i)
      (L.map (canonicalFactorMarked N old born))).d = q
    rw [finiteSum_mark_one _ _ rfl ?_,Nat.mul_one]
    intro B hB
    obtain ⟨j,_hJ,rfl⟩ := List.mem_map.mp hB
    rfl

/-- Removing the genuinely empty born slots from the native tuple gives
exactly the empty-boundary normalization of the whole actual joint mark. -/
theorem jointProfileMarked_filter_empty_born (N : Set X) (old born : List (Set X))
    (q : ℕ) (P : Finset (Fin old.length)) :
    jointProfileMarked N old (born.filter fun H => decide H.Nonempty) q P =
      nonemptyBoundary (jointProfileMarked N old born q P) := by
  let B := born.filter (fun H => decide H.Nonempty)
  have hRaw := joint_fields N old born q P
  have hFiltered := joint_fields N old B q P
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    (hFiltered.1.trans hRaw.1.symm) (hFiltered.2.1.trans ?_) ?_
    (hFiltered.2.2.trans hRaw.2.2.symm)
  · change B = (jointProfileMarked N old born q P).E.filter (fun H => decide H.Nonempty)
    rw [hRaw.2.1]
  · change (jointProfileMarked N old B q P).ideal = (jointProfileMarked N old born q P).ideal
    exact filter_value_of_empty_insertion (fun E => (jointProfileMarked N old E q P).ideal)
      (fun E j hj => by rw [jointProfileMarked_insertEmpty_born N old E q P hj]; rfl) born

end
end Hironaka.HironakaG4JointProfileEmptyBorn
