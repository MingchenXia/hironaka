import Hironaka.Resolution.HironakaG8PowerLowerGeometry
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PowerLowerMarks
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowers BlowupTowerTransforms
  StepOneValue StepOneValueMasked NonmonomialOrderTail HomogenizedIdealAlong CoefficientIdeal
  InvDomainMemberRestriction CompanionRebase CompanionReductionAlong HironakaActualPowerBoundaryExponents

/-- The native mark of a coefficient ideal of a mark d. -/
def coefficientMark (d : ℕ) : ℕ := ∏ j ∈ Finset.range d, (d-j)

theorem coeffMarkedAlong_mark {n : ℕ} {X : CMfd.{0} n} (J : MarkedIdeal n X) :
    (coeffMarkedAlong J).d = coefficientMark J.d := rfl

/-- Every native positive-level lower record has this exact mark, independent
of its point, tower, level, and selected members. -/
theorem lowerMarkedM_succ_mark {n : ℕ} {X Y : CMfd.{0} n}
    (J : MarkedIdeal n X) (s : ℕ) (T : BlowupTower X Y) (y : Y) :
    (lowerMarkedM J (s+1) T y).d = coefficientMark (coefficientMark J.d) := by
  change (memberRestrict (geoTransformAlong (barMarked J) T) (membersThrough (geoTransformAlong (barMarked J) T).E (origMembers J T) y)).d = _
  rw [memberRestrict_d, coeffMarkedAlong_mark, d_geoTransformAlong]
  rfl

/-- The two recursively selected positive-level marks are constant even
when the source clocks, points, or positive levels differ. -/
theorem lowerMarkedM_succ_mark_independent {n : ℕ} {X Y Z : CMfd.{0} n}
    (J : MarkedIdeal n X) (s t : ℕ) (T : BlowupTower X Y) (U : BlowupTower X Z) (y : Y) (z : Z) :
    (lowerMarkedM J (s+1) T y).d = (lowerMarkedM J (t+1) U z).d := by
  rw [lowerMarkedM_succ_mark, lowerMarkedM_succ_mark]

/-- The exact native mark of the companion on either branch. -/
def companionMark (d o : ℕ) : ℕ := if o < d then o * (d-o) else o

theorem companionOf_mark {n : ℕ} {X : CMfd.{0} n} (J : MarkedIdeal n X) (o : ℕ) :
    (companionOf n J o).d = companionMark J.d o := by
  exact companionAlong_d _ _ _ _ _ _

/-- The positive-level recursive marks of the original companion and its
whole-power recoding are explicit, even for different literal source towers. -/
theorem positive_lower_marks_power_companions {n : ℕ} {X Y Z : CMfd.{0} n}
    (J : MarkedIdeal n X) (e o s t : ℕ) (T : BlowupTower X Y) (U : BlowupTower X Z) (y : Y) (z : Z) :
    (lowerMarkedM (companionOf n J o) (s+1) T y).d =
      coefficientMark (coefficientMark (companionMark J.d o)) ∧
    (lowerMarkedM (companionOf n (powerMarked J e) (e*o)) (t+1) U z).d =
      coefficientMark (coefficientMark (companionMark (J.d*e) (e*o))) := by
  rw [lowerMarkedM_succ_mark, lowerMarkedM_succ_mark, companionOf_mark, companionOf_mark]
  exact ⟨rfl,rfl⟩

/-- The native companion mark scales quadratically in the two-factor
branch and linearly in the single-factor branch. -/
theorem companionMark_scale (d o e : ℕ) (he : 0 < e) :
    companionMark (d*e) (e*o) =
      if o < d then e*e*companionMark d o else e*companionMark d o := by
  by_cases h : o < d
  · have hp : e*o < d*e := by simpa [Nat.mul_comm] using (Nat.mul_lt_mul_left he).mpr h
    simp only [companionMark, h, hp, if_true]
    rw [Nat.mul_comm d e, ← Nat.mul_sub_left_distrib]
    ring
  · have hp : ¬ e*o < d*e := by
      intro hlt
      apply h
      exact Nat.lt_of_mul_lt_mul_left (by simpa [Nat.mul_comm] using hlt)
    simp [companionMark,h,hp]

/-- Exact positive-level marks for the literal actual masked companions,
allowing different suffix heads, points, and positive levels. -/
theorem positive_lower_marks_actual_masked_companions {n : ℕ} {X Y Z V : CMfd.{0} n}
    (J : MarkedIdeal n X) (e o : ℕ) (T : BlowupTower X Y) :
    let W := ordMask (geoTransformAlong J T) o
    let A := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) (geoTransformAlong J T)
    let B := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y)
      (geoTransformAlong (powerMarked J e) T)
    ∀ (S : BlowupTower (CMfd.of (n := n) W) Z) (U : BlowupTower (CMfd.of (n := n) W) V)
      (s t : ℕ) (z : Z) (v : V),
      (lowerMarkedM (companionOf n A o) (s+1) S z).d =
        coefficientMark (coefficientMark (companionMark J.d o)) ∧
      (lowerMarkedM (companionOf n B (e*o)) (t+1) U v).d =
        coefficientMark (coefficientMark (companionMark (J.d*e) (e*o))) := by
  let W := ordMask (geoTransformAlong J T) o
  let A := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) (geoTransformAlong J T)
  let B := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y)
    (geoTransformAlong (powerMarked J e) T)
  change ∀ (S : BlowupTower (CMfd.of (n := n) W) Z) (U : BlowupTower (CMfd.of (n := n) W) V)
      (s t : ℕ) (z : Z) (v : V),
      (lowerMarkedM (companionOf n A o) (s+1) S z).d =
        coefficientMark (coefficientMark (companionMark J.d o)) ∧
      (lowerMarkedM (companionOf n B (e*o)) (t+1) U v).d =
        coefficientMark (coefficientMark (companionMark (J.d*e) (e*o)))
  intro S U s t z v
  rw [lowerMarkedM_succ_mark, lowerMarkedM_succ_mark, companionOf_mark, companionOf_mark]
  change coefficientMark (coefficientMark (companionMark (geoTransformAlong J T).d o)) = _ ∧
    coefficientMark (coefficientMark (companionMark (geoTransformAlong (powerMarked J e) T).d (e*o))) = _
  rw [d_geoTransformAlong,d_geoTransformAlong]
  exact ⟨rfl,rfl⟩

end
end Hironaka.HironakaG8PowerLowerMarks
