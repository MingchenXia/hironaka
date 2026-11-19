import Hironaka.Resolution.HironakaG8TraceCosuppExponent
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8GapNormalizedExponent
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec GermIdealOrder
  DivisorExponentAlong HironakaG8LocalHistory HironakaG8TraceCosuppExponent

/-- At each carrier point, positivity of the ideal's ordinary order implies
membership in the marked cosupport. -/
def HasCosupportGap {n : ℕ} {X : CMfd.{0} n} (A : MarkedIdeal n X) : Prop :=
  ∀ y ∈ A.N, y ∈ cosupport n A.N A.ideal 1 → y ∈ A.cosupp

/-- A positive divisor exponent of a gap record forces the corresponding
trace into the marked cosupport as a germ. -/
theorem trace_cosupp_of_gap_pos {n k : ℕ} {X : CMfd.{0} n}
    (A : MarkedIdeal n X) (hA : IsInvDomain k A) (hgap : HasCosupportGap A)
    (i : Fin A.E.length) {x : X} (hxN : x ∈ A.N) (hxH : x ∈ A.E.get i)
    (hpos : 0 < divExpAlong n A.N A.ideal (A.E.get i) x) :
    ∀ᶠ y in 𝓝 x, y ∈ A.N → y ∈ A.E.get i → y ∈ A.cosupp := by
  have hdiv := (isDivNearAlong_get_iff_le hA.isWellFormed.isClosedSubmanifold_N
    hA.isWellFormed.isCoherent i hxN hxH (hA.isNonzeroAlongAt x hxN)).2 hpos
  filter_upwards [hdiv] with y hy hyN hyH
  exact hgap y hyN (hy hyN hyH)

/-- Local equivalence preserves normalized divisor exponents for records
whose marked cosupport contains every positive-order carrier point. -/
theorem normalized_exponent_of_cosupport_gap {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {k l : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain k A) (hB : IsInvDomain l B)
    (hN : A.N = B.N) (hL : LocWPEquiv A B) (hgapA : HasCosupportGap A) (hgapB : HasCosupportGap B)
    (i : Fin A.E.length) (j : Fin B.E.length) (hH : A.E.get i = B.E.get j)
    {x : X} (hxN : x ∈ A.N) (hxH : x ∈ A.E.get i) :
    B.d * divExpAlong n A.N A.ideal (A.E.get i) x =
      A.d * divExpAlong n B.N B.ideal (B.E.get j) x := by
  by_cases hposA : 0 < divExpAlong n A.N A.ideal (A.E.get i) x
  · exact normalized_exponent_of_trace_cosupp hn A B hA hB hN hL i j hH hxN hxH
      (trace_cosupp_of_gap_pos A hA hgapA i hxN hxH hposA)
  · have hzeroA : divExpAlong n A.N A.ideal (A.E.get i) x = 0 := by omega
    by_cases hposB : 0 < divExpAlong n B.N B.ideal (B.E.get j) x
    · have hxBN : x ∈ B.N := hN ▸ hxN
      have hxBH : x ∈ B.E.get j := hH ▸ hxH
      exact (normalized_exponent_of_trace_cosupp hn B A hB hA hN.symm hL.symm j i hH.symm hxBN hxBH
        (trace_cosupp_of_gap_pos B hB hgapB j hxBN hxBH hposB)).symm
    · have hzeroB : divExpAlong n B.N B.ideal (B.E.get j) x = 0 := by omega
      simp only [hzeroA,hzeroB,Nat.mul_zero]

/-- The same conclusion follows from the numerical zero-or-mark gap at the
chosen member, with no global support-gap hypothesis. -/
theorem normalized_exponent_of_numeric_gap {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {k l : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain k A) (hB : IsInvDomain l B)
    (hN : A.N = B.N) (hL : LocWPEquiv A B)
    (i : Fin A.E.length) (j : Fin B.E.length) (hH : A.E.get i = B.E.get j)
    {x : X} (hxN : x ∈ A.N) (hxH : x ∈ A.E.get i)
    (hgapA : divExpAlong n A.N A.ideal (A.E.get i) x = 0 ∨
      A.d ≤ divExpAlong n A.N A.ideal (A.E.get i) x)
    (hgapB : divExpAlong n B.N B.ideal (B.E.get j) x = 0 ∨
      B.d ≤ divExpAlong n B.N B.ideal (B.E.get j) x) :
    B.d * divExpAlong n A.N A.ideal (A.E.get i) x =
      A.d * divExpAlong n B.N B.ideal (B.E.get j) x := by
  rcases hgapA with hzeroA | hhighA
  · rcases hgapB with hzeroB | hhighB
    · simp only [hzeroA,hzeroB,Nat.mul_zero]
    · exact (normalized_exponent_of_mark_le hn B A hB hA hN.symm hL.symm j i hH.symm
        (hN ▸ hxN) (hH ▸ hxH) hhighB).symm
  · exact normalized_exponent_of_mark_le hn A B hA hB hN hL i j hH hxN hxH hhighA

end
end Hironaka.HironakaG8GapNormalizedExponent
