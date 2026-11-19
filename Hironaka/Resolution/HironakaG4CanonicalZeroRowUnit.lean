import Hironaka.Resolution.HironakaG4UnitRowGeoTransform
import Hironaka.Invariant.MonomialStepAlong

set_option autoImplicit false

/-! Actual canonical zero rows produce their own ambient units. All actual
restricted and monomial presentations are derived, not supplied.
Blueprint: `hironaka-g4-canonical-zero-row-unit.tex`. -/

open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG4CanonicalZeroRowUnit

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  RelativePrincipalizationSpan InvertibleIdealQuotient MonomialStepAlong
  DivisorExponentAlong MonomialPartAlong NormalCrossings SimultaneousNormalCrossings

variable {n : ℕ} {X : CMfd.{u} n}

/-- A genuine relative unit at a point of the carrier internally yields a
nonvanishing actual member and hence the true ambient coherent unit. -/
theorem one_mem_of_restricted_span_one {N : Set X} {I : GermIdeal n X}
    (hI : I.IsCoherent) {x : X} (hx : x ∈ N)
    (hOne : IsInSpanOnAt (n := n) N (I.mem x) x (fun _ => (1 : ℂ))) :
    I.mem x (fun _ => (1 : ℂ)) := by
  obtain ⟨K, s, a, hs, _ha, hsum⟩ := hOne
  have hNonzero : ∃ i, s i x ≠ 0 := by
    by_contra hAll
    have hs0 : ∀ i, s i x = 0 := by
      intro i
      by_contra hi
      exact hAll ⟨i, hi⟩
    have hsum0 : ∑ i, a i x * s i x = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hs0 i, mul_zero]
    exact one_ne_zero ((hsum.self_of_nhds hx).trans hsum0)
  obtain ⟨i, hi⟩ := hNonzero
  exact CompanionReduction.one_mem_of_apply_ne_zero hI (hs i) hi

/-- The native canonical principal dictionary makes an actual zero exponent
row a relative unit; coherence then produces the true ambient unit internally. -/
theorem one_mem_of_zero_canonical_row (hn : 0 < n) {N : Set X}
    {E : List (Set X)} {I : GermIdeal n X} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) (hI : I.IsCoherent)
    (hne : ∀ y ∈ N, IsNonzeroAlongAt N I y) (hmono : IsMonomialAlong n N I E)
    {x : X} (hx : x ∈ N)
    (hZero : ∀ i : Fin E.length, divExpAlong n N I (E.get i) x = 0) :
    I.mem x (fun _ => (1 : ℂ)) := by
  obtain ⟨_k, _Φ, _σ, _hsrc, _h0, _hNflat, _hσk, _hinj, _hA, hgen⟩ :=
    isPrincipalAlongAt_of_isMonomialAlong hn hN hE hTr hI hne hmono hx
  apply one_mem_of_restricted_span_one hI hx
  apply (hgen (fun _ => (1 : ℂ))).mpr
  have hOne : IsInSpanOnAt (n := n) N (· = fun _ => (1 : ℂ)) x
      (fun _ => (1 : ℂ)) :=
    isInSpanOnAt_eq_iff.mpr ⟨1, holomorphicAt_const 1,
      Eventually.of_forall fun _ _ => by simp⟩
  simpa only [hZero, pow_zero, Finset.prod_const_one] using hOne

end

end Hironaka.HironakaG4CanonicalZeroRowUnit
