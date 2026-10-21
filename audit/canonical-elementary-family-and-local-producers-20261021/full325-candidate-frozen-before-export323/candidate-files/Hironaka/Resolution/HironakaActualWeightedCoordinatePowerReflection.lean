/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualWeightedCoefficientCompression
import Hironaka.Resolution.HironakaActualFormalStrictGenerators
import Mathlib.RingTheory.MvPowerSeries.Order

/-!
# Exact actual weighted coordinate-centre conditions

Nonzero actual weighted homogeneous components prove multiplicativity of the
true selected-coordinate centre order. Positive powers reflect whole formal
and analytic normal powers. Thus actual common-mark coefficient compression
has exactly the original individual weighted centre-power conditions.
No current-HS-locus identification, tracking premise or termination is asserted.
Blueprint: `hironaka-actual-weighted-coordinate-power-reflection-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualWeightedCoordinatePowerReflection
noncomputable section
open HolGerm HironakaActualFormalStrictGenerators
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalVertexDivision
  HironakaActualWeightedCoefficientCompression HironakaActualCoefficientPresentationCentrePower
  HironakaActualAnalyticFormalNormalPowers HironakaRelativeNormalIdeal
variable {n : ℕ}

private theorem centerOrder_le_weightedOrder (A : Set (Fin n))
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ≠ 0) :
    (actualFormalCenterOrder A F hF : ℕ∞) ≤ F.weightedOrder (actualCoordinateWeight A) := by
  apply MvPowerSeries.nat_le_weightedOrder
  exact (mem_actualFormalCoordinateIdeal_pow_iff A _ F).mp (mem_actualFormalCenterOrder_power A F hF)

private theorem centerOrder_component_ne_zero (A : Set (Fin n))
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ≠ 0) :
    MvPowerSeries.weightedHomogeneousComponent (actualCoordinateWeight A)
      (actualFormalCenterOrder A F hF) F ≠ 0 := by
  obtain ⟨a,ha,hw⟩ := actualFormalCenterOrder_witness A F hF
  intro hz
  have hc := congrArg (MvPowerSeries.coeff a) hz
  rw [MvPowerSeries.coeff_weightedHomogeneousComponent,if_pos hw,map_zero] at hc
  exact ha hc

/-- The genuine entire selected-coordinate order is additive on nonzero products. -/
theorem actualFormalCenterOrder_mul (A : Set (Fin n)) (F G : MvPowerSeries (Fin n) ℂ)
    (hF : F ≠ 0) (hG : G ≠ 0) :
    actualFormalCenterOrder A (F*G) (mul_ne_zero hF hG)=
      actualFormalCenterOrder A F hF+actualFormalCenterOrder A G hG := by
  let p := actualFormalCenterOrder A F hF
  let q := actualFormalCenterOrder A G hG
  have hpq : F*G ∈ actualFormalCoordinateIdeal n A^(p+q) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul (mem_actualFormalCenterOrder_power A F hF)
      (mem_actualFormalCenterOrder_power A G hG)
  have hge := (mem_coordinate_power_iff_le_actualFormalCenterOrder A (F*G)
    (mul_ne_zero hF hG) (p+q)).mp hpq
  have hmul := MvPowerSeries.weightedHomogeneousComponent_mul_of_le_weightedOrder
    (centerOrder_le_weightedOrder A F hF) (centerOrder_le_weightedOrder A G hG)
  have hne : MvPowerSeries.weightedHomogeneousComponent (actualCoordinateWeight A) (p+q) (F*G) ≠ 0 := by
    rw [hmul]
    exact mul_ne_zero (centerOrder_component_ne_zero A F hF) (centerOrder_component_ne_zero A G hG)
  apply le_antisymm ?_ hge
  by_contra hle
  have hlt : p+q < actualFormalCenterOrder A (F*G) (mul_ne_zero hF hG) := Nat.lt_of_not_ge hle
  apply hne
  apply MvPowerSeries.ext
  intro a
  rw [MvPowerSeries.coeff_weightedHomogeneousComponent,map_zero]
  split_ifs with ha
  · exact (mem_actualFormalCoordinateIdeal_pow_iff A _ (F*G)).mp
      (mem_actualFormalCenterOrder_power A (F*G) (mul_ne_zero hF hG)) a (by rwa [ha])
  · rfl

private theorem centerOrder_one (A : Set (Fin n)) :
    actualFormalCenterOrder A (1 : MvPowerSeries (Fin n) ℂ) one_ne_zero=0 := by
  have h := actualFormalCenterOrder_le_weight A (1 : MvPowerSeries (Fin n) ℂ) one_ne_zero 0 (by simp)
  simpa using h

/-- Actual positive or zero powers retain their literal multiplicity in the true centre order. -/
theorem actualFormalCenterOrder_pow (A : Set (Fin n)) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ≠ 0) (r : ℕ) :
    actualFormalCenterOrder A (F^r) (pow_ne_zero r hF)=r*actualFormalCenterOrder A F hF := by
  induction r with
  | zero => simpa only [pow_zero,zero_mul] using centerOrder_one A
  | succ r ih =>
    have hm := actualFormalCenterOrder_mul A (F^r) F (pow_ne_zero r hF) hF
    simpa only [← pow_succ,ih,Nat.succ_mul] using hm

/-- Whole formal coordinate powers reflect every genuine positive exponent. -/
theorem mem_formal_coordinate_power_mul_iff (A : Set (Fin n)) (F : MvPowerSeries (Fin n) ℂ)
    (w r : ℕ) (hr : 0 < r) :
    F^r ∈ actualFormalCoordinateIdeal n A^(w*r) ↔ F ∈ actualFormalCoordinateIdeal n A^w := by
  by_cases hF : F=0
  · subst F
    simp [zero_pow (Nat.ne_of_gt hr)]
  · rw [mem_coordinate_power_iff_le_actualFormalCenterOrder A (F^r) (pow_ne_zero r hF),
      actualFormalCenterOrder_pow A F hF r,mem_coordinate_power_iff_le_actualFormalCenterOrder A F hF]
    simpa only [Nat.mul_comm (actualFormalCenterOrder A F hF) r] using
      (mul_le_mul_iff_left₀ hr : w*r ≤ actualFormalCenterOrder A F hF*r ↔ w ≤ actualFormalCenterOrder A F hF)

/-- Actual Taylor and genuine whole-power contraction give analytic normal-power reflection. -/
theorem mem_normal_power_mul_iff (d t : ℕ) (g : HolGerm (ComplexModel (d+t)))
    (w r : ℕ) (hr : 0 < r) :
    g^r ∈ normalIdeal d t^(w*r) ↔ g ∈ normalIdeal d t^w := by
  rw [mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow,map_pow,
    mem_formal_coordinate_power_mul_iff _ _ w r hr,
    ← mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow]

/-- The entire common-mark compressed ideal has exactly the original individual weighted centre conditions. -/
theorem weightedCompression_le_normal_power_iff {ι : Type*} [Fintype ι] (d t : ℕ)
    (w : ι → ℕ) (hw : ∀ i, 0 < w i) (c : ι → HolGerm (ComplexModel (d+t))) :
    weightedCompression w c ≤ normalIdeal d t^weightedCommonMark w ↔
      ∀ i, c i ∈ normalIdeal d t^w i := by
  change Ideal.span (range (fun i => c i^(weightedCommonMark w/w i))) ≤ _ ↔ _
  rw [Ideal.span_le]
  constructor
  · intro h i
    have hi := h (show c i^(weightedCommonMark w/w i) ∈
      range (fun i => c i^(weightedCommonMark w/w i)) from ⟨i,rfl⟩)
    change c i^(weightedCommonMark w/w i) ∈ normalIdeal d t^weightedCommonMark w at hi
    apply (mem_normal_power_mul_iff d t (c i) (w i) _ (compressionExponent_pos w hw i)).mp
    rw [weight_mul_compressionExponent]
    exact hi
  · intro h f hf
    obtain ⟨i,rfl⟩ := hf
    change c i^(weightedCommonMark w/w i) ∈ normalIdeal d t^weightedCommonMark w
    have hi := (mem_normal_power_mul_iff d t (c i) (w i) _ (compressionExponent_pos w hw i)).mpr (h i)
    simpa only [weight_mul_compressionExponent] using hi

end
end Hironaka.HironakaActualWeightedCoordinatePowerReflection
