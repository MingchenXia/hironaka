import Hironaka.Resolution.HironakaG8ResidualVanishes
import Hironaka.Resolution.HironakaG8ResidualDivBoth
import Hironaka.Resolution.HironakaG8ResidualActualZeroReduction

/-! # The successor residual reduces to the positive mixed trace case -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ResidualPositiveMixed
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism GermIdealOrder DivisorExponentAlong
  HironakaG8LocalHistory HironakaG11InvBMLower HironakaG11InvBMMask
  HironakaG8ResidualActualNonzero StepOneValue ResolutionInvariantSpec HomogenizedIdealAlong
open HironakaG11InvBMClass (SameCarrierDim)

/-- All other successor residual branches close from the original data. -/
theorem actual_successor_exp_eq_of_positive_mixed_trace
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {A B : MarkedIdeal n X} {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hd : A.d = B.d) (hE : A.E = B.E) (hdim : SameCarrierDim A B)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked A) T) {a y : Y}
    (ha : a ∈ (geoTransformAlong (barMarked A) T).cosupp) (s : ℕ) (hreg : stepRegime A (s+1) T a)
    (O : Opens Y) (hOA : O ≤ maskBM A (s+1) T a) (hOB : O ≤ maskBM B (s+1) T a) {r r' : ℕ}
    (hdA : IsInvDomain r (MarkedIdeal.pullback (Subtype.val : O → Y) (lowerIdealBM A (s+1) T a)))
    (hdB : IsInvDomain r' (MarkedIdeal.pullback (Subtype.val : O → Y) (lowerIdealBM B (s+1) T a)))
    (hyO : y ∈ O) {H : Set Y} (hH : H ∈ (lowerIdealBM A (s+1) T a).E)
    (hy : y ∈ (lowerIdealBM A (s+1) T a).cosupp) (hyH : y ∈ H)
    (hbelow : ¬ IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (lowerIdealBM A (s+1) T a).ideal H (lowerIdealBM A (s+1) T a).d y)
    (hdiv : IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y ∨
      IsDivNearAlong n (lowerIdealBM B (s+1) T a).N
      (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y)
    (htrace : IsNonzeroAlongAt (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
        (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal y →
      IsNonzeroAlongAt (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N
        (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).ideal y →
      0 < divExpAlong n (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
        (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal H y →
      0 < divExpAlong n (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N
        (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).ideal H y →
      ¬ (IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
        (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y ∧
        IsDivNearAlong n (lowerIdealBM B (s+1) T a).N
        (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y) →
      ((∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N → z ∈ H →
        ∀ D ∈ throughMembers A T a, z ∈ D) ↔
        (∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N → z ∈ H →
        ∀ D ∈ throughMembers A T a, z ∈ D))) :
    divExpAlong n (lowerIdealBM A (s+1) T a).N (lowerIdealBM A (s+1) T a).ideal H y =
      divExpAlong n (lowerIdealBM B (s+1) T a).N (lowerIdealBM B (s+1) T a).ideal H y := by
  classical
  by_cases hnzA : IsNonzeroAlongAt (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
      (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal y
  swap
  · exact HironakaG8ResidualVanishes.actual_successor_exp_eq_of_coeff_vanishes hn hA hB hmA hmB h hd hE hdim
      T hT ha s hreg O hOA hOB hdA hdB hyO hH hy hyH hbelow hdiv (Or.inl hnzA)
  by_cases hnzB : IsNonzeroAlongAt (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N
      (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).ideal y
  swap
  · exact HironakaG8ResidualVanishes.actual_successor_exp_eq_of_coeff_vanishes hn hA hB hmA hmB h hd hE hdim
      T hT ha s hreg O hOA hOB hdA hdB hyO hH hy hyH hbelow hdiv (Or.inr hnzB)
  by_cases hzero : divExpAlong n (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
        (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal H y = 0 ∨
      divExpAlong n (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N
        (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).ideal H y = 0
  · exact HironakaG8ResidualActualZeroReduction.actual_successor_exp_eq_of_coeff_zero hn hA hB hmA hmB h hd hE hdim
      T hT ha s O hOA hOB hyO hH hy hyH hnzA hnzB hzero
  by_cases hboth : IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
        (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y ∧
      IsDivNearAlong n (lowerIdealBM B (s+1) T a).N
        (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y
  · exact HironakaG8ResidualDivBoth.actual_successor_exp_eq_of_div_both hn hA hB hmA hmB h hd hE hdim
      T hT ha s hreg O hOA hOB hdA hdB hyO hH hy hyH hbelow hboth.1 hboth.2
  have hposA : 0 < divExpAlong n (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
      (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal H y := by
    by_contra hn; exact hzero (Or.inl (Nat.eq_zero_of_not_pos hn))
  have hposB : 0 < divExpAlong n (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N
      (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).ideal H y := by
    by_contra hn; exact hzero (Or.inr (Nat.eq_zero_of_not_pos hn))
  exact actual_successor_exp_eq_of_trace_only hn hA hB hmA hmB h hd hE hdim
    T hT ha s hreg O hOA hOB hdA hdB hyO hH hy hyH hbelow hdiv
    (htrace hnzA hnzB hposA hposB hboth)

end
end Hironaka.HironakaG8ResidualPositiveMixed
