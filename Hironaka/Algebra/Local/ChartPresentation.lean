/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.ChartRing
public import Mathlib.RingTheory.Regular.RegularSequence
import Hironaka.Algebra.Local.BirationalTransform
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Scheme.BlowUp.LinearType

/-!
# The kernel of the chart presentation

Kollár asserts that `y₁ = x₁/x_r, …, y_{r-1} = x_{r-1}/x_r, y_r = x_r, …` "give local coordinates
on a chart" [Kol07, Definition 60]; Hauser states that for a regular sequence `g₁, …, g_k` the
only relations among the `gⱼ/gᵢ` over `R` are the trivial ones, so that
`R[g₁/gᵢ, …, g_k/gᵢ] ≅ R[t₁, …, t_k]/(gᵢ tⱼ − gⱼ)` [Hau14, Theorem 4.20 (b)].
`Hironaka/Algebra/Local/Chart.lean` gives the presentation `R[Y₀, …, Y_{r-1}] → R' = R[xᵢ/x_r]`,
`Yᵢ ↦ yᵢ`, and its surjectivity; this file proves that its kernel is exactly the ideal
`⟨x_r Yᵢ − xᵢ⟩` of the obvious relations:

* the list `[x_r, x₀, …, x_{r-1}]` is weakly regular on `R` — it is a prefix of a permutation of
  the regular system of parameters, which is a regular sequence
  (`Hironaka/Algebra/Local/RegularSystem.lean`);
* the assembly: `⟨x_r Yᵢ − xᵢ⟩ ⊆ ker` because `x_r yᵢ = xᵢ` in `R'`; for `p` in the kernel, the
  elimination lemma of `Hironaka/Scheme/BlowUp/LinearType.lean` gives `x_rᵈ p ≡ c (mod ⟨x_r Yᵢ −
  xᵢ⟩)` with `c ∈ R`, so `c = 0` in `R[1/x_r]`, hence `x_rᵏ c = 0` in `R` and `c = 0` (`x_r` is a
  nonzerodivisor); then `x_rᵈ p ∈ ⟨x_r Yᵢ − xᵢ⟩` and the torsion-freeness of the ideal of
  relations modulo `x_r` (`Hironaka/Scheme/BlowUp/LinearType.lean`, for a weakly regular sequence)
  gives `p ∈ ⟨x_r Yᵢ − xᵢ⟩`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing MvPolynomial RingTheory.Sequence AlgebraicGeometry.affineBlowUpAlgebra

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] {n : ℕ} (x : Fin n → R) (r : Fin n)

/-- The list `[x_r, x₀, …, x_{r-1}]`: the denominator first, then the divided coordinates. -/
noncomputable abbrev chartList : List R :=
  x r :: List.ofFn fun i : Fin r => x (Fin.castLE r.2.le i)

/-- The remaining parameters `x_{r+1}, …, x_{n-1}`. -/
noncomputable abbrev chartTail : List R :=
  List.ofFn fun i : Fin (n - r - 1) => x ⟨r + 1 + i, by omega⟩

omit [IsRegularLocalRing R] in
theorem ofList_chartList_append_chartTail :
    Ideal.ofList (chartList x r ++ chartTail x r) = Ideal.span (Set.range x) := by
  change Ideal.span {y | y ∈ chartList x r ++ chartTail x r} = _
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_cons, List.mem_ofFn, Set.mem_range]
  constructor
  · rintro ((rfl | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact ⟨r, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩
    rcases lt_trichotomy i.val r.val with hlt | heq | hgt
    · exact Or.inl (Or.inr ⟨⟨i.val, hlt⟩, rfl⟩)
    · exact Or.inl (Or.inl (congrArg x (Fin.ext heq)))
    · refine Or.inr ⟨⟨i.val - r.val - 1, by omega⟩, ?_⟩
      congr 1
      ext
      simp only []
      omega

omit [CommRing R] [IsRegularLocalRing R] in
theorem length_chartList_append_chartTail : (chartList x r ++ chartTail x r).length = n := by
  simp only [List.length_append, List.length_cons, List.length_ofFn]
  omega

/-- `[x_r, x₀, …, x_{r-1}]` is weakly regular on `R` (a prefix of a permutation of a regular
system of parameters; regular sequences as in [Sta, Tag 00LJ]). -/
theorem isWeaklyRegular_chartList (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) : IsWeaklyRegular R (chartList x r) := by
  have hreg := isRegular_of_span_eq_maximalIdeal (chartList x r ++ chartTail x r)
    (by rw [ofList_chartList_append_chartTail, hx])
    (by rw [length_chartList_append_chartTail]; exact hn)
  exact ((isWeaklyRegular_append_iff R _ _).mp hreg.toIsWeaklyRegular).1

/-- `x_r` is a nonzerodivisor of `R` (the head of the weakly regular list). -/
theorem isSMulRegular_x (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) : IsSMulRegular R (x r) :=
  isSMulRegular_head _ _ (isWeaklyRegular_chartList x r hx hn)

/-! ### The kernel of the presentation -/

omit [IsRegularLocalRing R] in
theorem chartPresentation_sub_eq_zero (i : Fin r) :
    chartPresentation x r (C (x r) * X i - C (x (Fin.castLE r.2.le i))) = 0 := by
  rw [chartPresentation, map_sub, map_mul, aeval_C, aeval_X, aeval_C,
    algebraMap_x_eq_mul_chartYR x r (show Fin.castLE r.2.le i < r from i.2), sub_self]

omit [IsRegularLocalRing R] in
/-- `⟨x_r Yᵢ − xᵢ⟩ ⊆ ker`. -/
theorem chartRelations_le_ker_chartPresentation :
    chartRelations x r ≤ RingHom.ker (chartPresentation x r) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact RingHom.mem_ker.mpr (chartPresentation_sub_eq_zero x r i)

theorem mem_presentationIdeal_of_C_pow_mul_mem {A : Type*} [CommRing A] {k : ℕ} (a : A)
    (g : Fin k → A) (h : IsWeaklyRegular A (a :: List.ofFn g)) (d : ℕ) (p : MvPolynomial (Fin k) A)
    (hp : C a ^ d * p ∈ presentationIdeal a g) : p ∈ presentationIdeal a g := by
  induction d generalizing p with
  | zero => simpa using hp
  | succ d ih =>
    rw [pow_succ, mul_assoc] at hp
    exact mem_presentationIdeal_of_C_mul_mem a g h p (ih _ hp)

/-- The kernel of the chart presentation is the ideal of the relations `x_r Yᵢ − xᵢ`
([Hau14, Theorem 4.20 (b)]; the coordinates of the chart of [Kol07, Definition 60]). -/
theorem ker_chartPresentation (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) :
    RingHom.ker (chartPresentation x r) = chartRelations x r := by
  refine le_antisymm ?_ (chartRelations_le_ker_chartPresentation x r)
  intro p hp
  rw [RingHom.mem_ker] at hp
  obtain ⟨d, c, hdc⟩ := exists_pow_mul_sub_C_mem (x r) (fun i : Fin r => x (Fin.castLE r.2.le i)) p
  -- the constant `c` is zero in `R'`, hence in `R[1/x_r]`, hence in `R`
  have hc0 : chartPresentation x r (C c) = 0 := by
    have h1 := chartRelations_le_ker_chartPresentation x r hdc
    rw [RingHom.mem_ker, map_sub, map_mul, hp, mul_zero, zero_sub, neg_eq_zero] at h1
    exact h1
  have hc : c = 0 := by
    rw [chartPresentation, aeval_C] at hc0
    have h2 : algebraMap R (Localization.Away (x r)) c = 0 := by
      have := congrArg (fun z : chartRing x r => (z : Localization.Away (x r))) hc0
      simpa using this
    obtain ⟨⟨m, hm⟩, hmc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (x r))
      (Localization.Away (x r)) c).mp h2
    obtain ⟨e, rfl⟩ := (Submonoid.mem_powers_iff m (x r)).mp hm
    exact ((isSMulRegular_x x r hx hn).pow e) (by simpa using hmc)
  rw [hc, map_zero, sub_zero, map_pow] at hdc
  exact mem_presentationIdeal_of_C_pow_mul_mem _ _ (isWeaklyRegular_chartList x r hx hn) d p hdc

end IsLocalRing
