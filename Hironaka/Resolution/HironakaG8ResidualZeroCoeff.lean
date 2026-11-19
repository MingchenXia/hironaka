import Hironaka.Resolution.HironakaG8ExceptionalSumCoeff

/-! # Zero coefficient exponents close the successor comparison -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ResidualZeroCoeff
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers GermIdealOrder DivisorExponentAlong HironakaG8SumExponents
open RestrictedIdealExtension (sumIdeal)

/-- A nonzero coefficient ideal of exponent zero forces its sum with any
holomorphic ideal to have exponent zero. -/
theorem sum_exp_zero_of_coeff_exp_zero
    {n : ℕ} {X : CMfd.{0} n} {N H : Set X} {C E : GermIdeal n X} {y : X}
    (hC : ∀ x g, C.mem x g → HolomorphicAt n g x)
    (hE : ∀ x g, E.mem x g → HolomorphicAt n g x)
    {r : X → X} (hr : IsLocalRetraction n N r y) (hyH : y ∈ H)
    (hnz : IsNonzeroAlongAt N C y) (hzero : divExpAlong n N C H y = 0) :
    divExpAlong n N (sumIdeal C E) H y = 0 := by
  classical
  have hnot : ¬ IsDivNearAlong n N C H 1 y := by
    intro hdiv
    have := (isDivNearAlong_iff_le_divExpAlong hr hyH hnz hC).mp hdiv
    omega
  have hsum : ¬ IsDivNearAlong n N (sumIdeal C E) H (0+1) y := fun hdiv =>
    hnot ((isDivNearAlong_sumIdeal_iff hC hE 1 y).mp hdiv).1
  have hex : ∃ e, ¬ IsDivNearAlong n N (sumIdeal C E) H (e+1) y := ⟨0,hsum⟩
  unfold divExpAlong
  rw [dif_pos hex]
  exact (Nat.find_eq_zero hex).mpr hsum

/-- Equal coefficient exponents through a positive mark close the sum
comparison when either coefficient exponent is zero. -/
theorem sum_exponents_equal_of_coeff_zero
    {n : ℕ} {X : CMfd.{0} n} {N N' H : Set X} {C C' E : GermIdeal n X} {y : X}
    (hC : ∀ x g, C.mem x g → HolomorphicAt n g x)
    (hC' : ∀ x g, C'.mem x g → HolomorphicAt n g x)
    (hE : ∀ x g, E.mem x g → HolomorphicAt n g x)
    {r r' : X → X} (hr : IsLocalRetraction n N r y) (hr' : IsLocalRetraction n N' r' y) (hyH : y ∈ H)
    (hnz : IsNonzeroAlongAt N C y) (hnz' : IsNonzeroAlongAt N' C' y)
    {d : ℕ} (hd : 1 ≤ d)
    (hcoeff : min (divExpAlong n N C H y) d = min (divExpAlong n N' C' H y) d)
    (hzero : divExpAlong n N C H y = 0 ∨ divExpAlong n N' C' H y = 0) :
    divExpAlong n N (sumIdeal C E) H y = divExpAlong n N' (sumIdeal C' E) H y := by
  have ha : divExpAlong n N C H y = 0 := by omega
  have hb : divExpAlong n N' C' H y = 0 := by omega
  rw [sum_exp_zero_of_coeff_exp_zero hC hE hr hyH hnz ha,
    sum_exp_zero_of_coeff_exp_zero hC' hE hr' hyH hnz' hb]

end
end Hironaka.HironakaG8ResidualZeroCoeff
