/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.Invariant
public import Hironaka.Resolution.Algebraic.Balanced.Basic
public import Hironaka.Resolution.Algebraic.Tuning.Sheaf
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Resolution.Algebraic.MaximalContact.FormalEquivBridge
import Hironaka.Resolution.Algebraic.MaximalContact.GoingUpDown
import Hironaka.Resolution.Algebraic.Tuning.Assemble
import Hironaka.Scheme.IdealSheaf.Derivative.StalkCoords
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.TotalTransformOnCentre
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Tuning of ideals, II: Kollár's Corollary 101

Kollár's Corollary 101 [Kol07, Corollary 101] (Tuning of ideals, II): for `m = max-ord I ≥ 1` and
`s = r · lcm(2, …, m)` with `r ≥ m − 1`, the tuned ideal `W_s(I)` is MC-invariant and D-balanced,
and a smooth blow-up sequence is of order `≥ m` starting with `(X, I, m, E)` iff it is of order
`≥ s` starting with `(X, W_s(I), s, E)`. "Everything follows from (99) and (100), except for the
role played by `E`."

* **The properties of `W_s(I)`** ([Kol07, Proposition 99 (5) and (8)]; the maximal order is
  [Kol07, Theorem 54.2 (i)] for the tuned ideal). They are inclusions and orders of ideal sheaves,
  checked at stalks. An inclusion of ideal sheaves on a Jacobson scheme (every scheme locally of
  finite type over a field, `LocallyOfFiniteType.jacobsonSpace`) holds as soon as it holds at the
  closed points (`le_of_forall_stalkIdeal_le_of_isClosed`); at a closed point the residue field is
  algebraic over `k` (`isAlgebraic_residueField_of_isClosed`), so the stalk carries `k`-linear
  coordinates whose derivations span the `k`-derivations
  (`exists_regularCoords_stalk_of_isAlgebraic`), and the stalk bridges `stalkIdeal_W`,
  `stalkIdeal_MC`, `stalkIdeal_derivative`, `stalkIdeal_derivativeIter` with `derivative_eq_D`,
  `derivativeIter_eq_Dpow` turn the sheaf statements into the statements in coordinates of
  `Hironaka.Local` (`RegularCoords.isMCInvariant_W`, `RegularCoords.isDBalanced_W`,
  `RegularCoords.ord_W`, `RegularCoords.W_eq_top_of_ord_lt`), whose hypothesis `ord_p I ≤ m` is
  `m = max-ord I`. For `max-ord W_s(I) = s`: the order at any point is bounded by the order at a
  closed point it specializes to (`ord_le_ord_of_specializes`, `exists_closedPoint_specializes`),
  where it is `s` or `0`; and a point of order `m` exists because `max-ord I = m ≥ 1` is a supremum
  of naturals bounded by `m` (were every order `≤ m − 1`, so would be the supremum,
  `maxOrd_le_iff`), and it specializes to a closed point of order `m`, where `W_s(I)` has order
  exactly `s`.
* **The reduction to Theorem 100.** `m ∣ s` and `s ≥ 1` give `s = m s'` with `s' ≥ 1`, and
  `tuning_iff_W` of `Hironaka.Resolution.Algebraic.Tuning.Assemble` is the statement at `J =
  W_{ms'}(I)`.
* **The role of `E`.** A sequence of order `≥ m` for `(X, I, m, E)` is one for the empty family (its
  centres have simple normal crossings with the exceptional divisors, a sub-family of the induced
  families `E_i`: the `IsSubfamilyVia` lemmas of `Hironaka.Snc`) together with the snc clauses for
  `E_i`; conversely the two recombine. The clause is a condition on `(Z_i, E_i)` alone.
* **Corollary 101.** `s = r · Lcm m` is divisible by `m` (`dvd_Lcm`) and positive for `r ≥ 1`, so
  the reduction gives the equivalence; with the properties above, the corollary as printed, except
  for the added hypothesis `r ≥ 1`: Kollár's `r ≥ m − 1` allows `r = 0` when `m = 1`, where `s = 0`,
  `W_0(I) = 𝒪_X` and the equivalence fails. -/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence IsLocalRing

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (I : X.IdealSheafData) (m : ℕ)

/-- `m = max-ord I` bounds the order of every stalk (the hypothesis of the coordinate lemmas on
Proposition 99 at each point). -/
theorem ord_stalkIdeal_le_of_maxOrd_eq (hI : I.maxOrd = m) (p : X) :
    IsLocalRing.ord (I.stalkIdeal p) ≤ m := by
  rw [← ord_eq_ord_stalkIdeal]
  exact hI ▸ le_maxOrd I p

/-! ### The tuned ideal is MC-invariant, D-balanced, of maximal order `s` -/

include n in
/-- [Kol07, Corollary 101; Proposition 99 (5)]: for `m = max-ord I ≥ 1` and `s ≥ 1`, `W_s(I)` is
MC-invariant with respect to `s`, that is `MC_s(W_s(I)) · D(W_s(I)) ⊆ W_s(I)`. Proved in coordinates
at the stalk of every closed point (`RegularCoords.isMCInvariant_W`), through the closed-point
reduction and the stalk bridges. -/
theorem isMCInvariant_W (hI : I.maxOrd = m) (hm : 1 ≤ m) {s : ℕ} (hs : 1 ≤ s) :
    IsMCInvariant f (W f I m s) s := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsJacobsonRing k := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  unfold IsMCInvariant
  refine le_of_forall_stalkIdeal_le_of_isClosed fun p hp => ?_
  let _ := f.stalkAlgebra p
  let _ := f.stalkAlgebraRat p
  have := isRegularLocalRing_stalk f p
  obtain ⟨d, c, hk, hs'⟩ := exists_regularCoords_stalk_of_isAlgebraic f n p
    (isAlgebraic_residueField_of_isClosed f n hp)
  have hIp := ord_stalkIdeal_le_of_maxOrd_eq I m hI p
  rw [stalkIdeal_mul, stalkIdeal_MC f n (W f I m s) s p c hk hs', stalkIdeal_derivative,
    Ideal.derivative_eq_D c hk hs', stalkIdeal_W f n I m s p c hk hs']
  exact c.isMCInvariant_W hm hIp hs

include n in
/-- [Kol07, Corollary 101; Proposition 99 (8)]: for `m = max-ord I ≥ 1` and `r ≥ m − 1`,
`W_{r·lcm(2,…,m)}(I)` is D-balanced with respect to `r · lcm(2, …, m)`. Proved in coordinates at the
stalk of every closed point (`RegularCoords.isDBalanced_W`). -/
theorem isDBalanced_W (hI : I.maxOrd = m) (hm : 1 ≤ m) {r : ℕ} (hr : m - 1 ≤ r) :
    IsDBalanced f (W f I m (r * Lcm m)) (r * Lcm m) := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsJacobsonRing k := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  intro i hi
  refine le_of_forall_stalkIdeal_le_of_isClosed fun p hp => ?_
  let _ := f.stalkAlgebra p
  let _ := f.stalkAlgebraRat p
  have := isRegularLocalRing_stalk f p
  obtain ⟨d, c, hk, hs'⟩ := exists_regularCoords_stalk_of_isAlgebraic f n p
    (isAlgebraic_residueField_of_isClosed f n hp)
  have hIp := ord_stalkIdeal_le_of_maxOrd_eq I m hI p
  rw [stalkIdeal_pow, stalkIdeal_pow, stalkIdeal_derivativeIter,
    Ideal.derivativeIter_eq_Dpow c hk hs', stalkIdeal_W f n I m _ p c hk hs']
  exact c.isDBalanced_W hm hIp hr i hi

include n in
/-- The order of the tuned ideal at a closed point: at most `s`, and exactly `s` where `I` has order
`m` (`RegularCoords.ord_W`; where `ord I < m`, `W_s(I)_p = 𝒪_p` by
`RegularCoords.W_eq_top_of_ord_lt`). -/
theorem ord_W_of_isClosed (hI : I.maxOrd = m) (hm : 1 ≤ m) (s : ℕ) {p : X}
    (hp : IsClosed ({p} : Set X)) :
    (W f I m s).ord p ≤ s ∧ (I.ord p = m → (W f I m s).ord p = s) := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  let _ := f.stalkAlgebra p
  let _ := f.stalkAlgebraRat p
  have := isRegularLocalRing_stalk f p
  obtain ⟨d, c, hk, hs'⟩ := exists_regularCoords_stalk_of_isAlgebraic f n p
    (isAlgebraic_residueField_of_isClosed f n hp)
  have hIp := ord_stalkIdeal_le_of_maxOrd_eq I m hI p
  simp only [ord_eq_ord_stalkIdeal]
  rw [stalkIdeal_W f n I m s p c hk hs']
  rcases hIp.lt_or_eq with hlt | heq
  · refine ⟨?_, fun h => absurd h hlt.ne⟩
    rw [c.W_eq_top_of_ord_lt hm hlt s, IsLocalRing.ord_top]
    exact zero_le
  · exact ⟨(c.ord_W hm heq s).le, fun _ => c.ord_W hm heq s⟩

include n in
/-- For `m = max-ord I ≥ 1`, `max-ord W_s(I) = s` (the analogue of [Kol07, Theorem 54.2 (i)] for
`W_s`). The bound at any point comes from a closed point it specializes to; the value is attained at
a closed specialization of a point of order `m`, which exists because a supremum of naturals bounded
by `m` and equal to `m ≥ 1` is attained. -/
theorem maxOrd_W (hI : I.maxOrd = m) (hm : 1 ≤ m) (s : ℕ) : (W f I m s).maxOrd = s := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsJacobsonRing k := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  refine le_antisymm ((maxOrd_le_iff (W f I m s)).mpr fun x => ?_) ?_
  · obtain ⟨x₀, hspec, hx₀⟩ := exists_closedPoint_specializes x
    exact (ord_le_ord_of_specializes (W f I m s) f n hspec).trans
      (ord_W_of_isClosed f n I m hI hm s hx₀).1
  · have hex : ∃ η : X, I.ord η = m := by
      by_contra hne
      push Not at hne
      have hle : I.maxOrd ≤ ((m - 1 : ℕ) : ℕ∞) := (maxOrd_le_iff I).mpr fun x => by
        have h1 : I.ord x ≤ (m : ℕ∞) := hI ▸ le_maxOrd I x
        have h2 : I.ord x < (m : ℕ∞) := lt_of_le_of_ne h1 (hne x)
        have hm' : (m : ℕ∞) = ((m - 1 : ℕ) : ℕ∞) + 1 := by
          exact_mod_cast (Nat.sub_add_cancel hm).symm
        rw [hm'] at h2
        exact (ENat.lt_add_one_iff (ENat.natCast_ne_top _)).mp h2
      rw [hI] at hle
      have : m ≤ m - 1 := by exact_mod_cast hle
      omega
    obtain ⟨η, hη⟩ := hex
    obtain ⟨x₀, hspec, hx₀⟩ := exists_closedPoint_specializes η
    have hx₀m : I.ord x₀ = m :=
      le_antisymm (hI ▸ le_maxOrd I x₀) (hη ▸ ord_le_ord_of_specializes I f n hspec)
    rw [← (ord_W_of_isClosed f n I m hI hm s hx₀).2 hx₀m]
    exact le_maxOrd _ x₀

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Hironaka.Sequence

open Scheme.IdealSheafData

variable {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

/-! ### The role of `E` -/

/-- The role of `E` in the proof of [Kol07, Corollary 101]: a smooth blow-up sequence is of order
`≥ m` starting with `(X, I, m, E)` iff it is of order `≥ m` starting with `(X, I, m)` (the empty
family) and every centre has simple normal crossings with the total transform `E_i`. The direction
`→` drops `E` to the sub-family of exceptional divisors (`IsSubfamilyVia`), the direction `←`
recombines. -/
theorem isOrderGeSeq_iff_empty_and_hasSncWith (S : BlowUpSequence X) (I : X.IdealSheafData) (m : ℕ)
    (E : DivisorFamily X) :
    S.IsOrderGeSeq f I m E ↔
      S.IsOrderGeSeq f I m (DivisorFamily.empty X) ∧
        ∀ i : Fin S.length, (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i) := by
  constructor
  · intro h
    refine ⟨⟨h.1, fun i => ⟨?_, (h.2 i).2⟩⟩, fun i => (h.2 i).1⟩
    obtain ⟨τ, hτ⟩ :=
      exists_isSubfamilyVia_totalTransformSeq S _ (empty_isSubfamilyVia E) i.castSucc
    exact hasSncWith_of_isSubfamilyVia hτ (h.2 i).1
  · rintro ⟨h0, hsnc⟩
    exact ⟨h0.1, fun i => ⟨hsnc i, (h0.2 i).2⟩⟩

/-! ### The reduction to Theorem 100 and Corollary 101 -/

variable [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f] (S : BlowUpSequence X)
  (I : X.IdealSheafData) (E : DivisorFamily X) (m : ℕ)

include n in
/-- The reduction of [Kol07, Corollary 101] to Theorem 100: for `m ∣ s` and `s ≥ 1`, Theorem 100 at
the upper bound `J = W_{ms'}(I)` (`tuning_iff_W`) with `s = m s'`. -/
theorem tuning_iff_W_of_dvd (hI : I.maxOrd = m) {s : ℕ} (hs : 1 ≤ s) (hdvd : m ∣ s) :
    S.IsOrderGeSeq f I m E ↔ S.IsOrderGeSeq f (W f I m s) s E := by
  obtain ⟨s', rfl⟩ := hdvd
  have hs' : 1 ≤ s' := Nat.pos_of_ne_zero fun h => by subst h; simp at hs
  exact tuning_iff_W f n S I E m s' hI hs'

include n in
/-- **Kollár's Corollary 101** [Kol07, Corollary 101], the equivalence for every divisor family:
`s = r · lcm(2, …, m)` is divisible by `m` (`dvd_Lcm`) and, under the additional hypothesis `r ≥ 1`,
positive, so the reduction to Theorem 100 applies. Kollár's hypothesis `r ≥ m − 1` is part of his
statement and is kept so that the corollary reads as printed (the D-balanced clause of
`corollary101` needs it, `isDBalanced_W`); the equivalence does not need it, because Theorem 100
asks only that `s` be positive and divisible by `m`. The hypothesis `r ≥ 1` is not in Kollár's
statement: it excludes only `m = 1`, `r = 0`, where `s = 0`, `W_0(I) = 𝒪_X` and the printed
equivalence fails (every smooth blow-up sequence is of order `≥ 0` for `(𝒪_X, 0)`). -/
theorem tuning_iff_E (hI : I.maxOrd = m) (hm : 1 ≤ m) {r : ℕ} (_hr : m - 1 ≤ r) (hr1 : 1 ≤ r) :
    S.IsOrderGeSeq f I m E ↔ S.IsOrderGeSeq f (W f I m (r * Lcm m)) (r * Lcm m) E :=
  tuning_iff_W_of_dvd f n S I E m hI (Nat.mul_pos hr1 (Lcm_pos m))
    ((dvd_Lcm hm le_rfl).mul_left r)

include n in
/-- **Kollár's Corollary 101** [Kol07, Corollary 101] (Tuning of ideals, II) as printed: `W_s(I)` is
MC-invariant and D-balanced with respect to `s = r · lcm(2, …, m)`, and a smooth blow-up sequence is
of order `≥ m` starting with `(X, I, m, E)` iff it is of order `≥ s` starting with
`(X, W_s(I), s, E)` — with the additional hypothesis `r ≥ 1`, which excludes only `m = 1`, `r = 0`
(there `s = 0` and `W_0(I) = 𝒪_X`, and the equivalence fails: every smooth blow-up sequence is of
order `≥ 0` for `(𝒪_X, 0)`). Kollár's hypothesis "`E` snc" is part of his statement — a triple of
[Kol07, Notation 64] — and is kept so that the corollary reads as printed; the proof does not need
it, because tuning changes only the ideal: the three clauses hold for every divisor family, the
order-`≥ m` condition involving `E` only through the snc clauses on the centres, which are the same
on both sides of the equivalence. -/
theorem corollary101 (hI : I.maxOrd = m) (hm : 1 ≤ m) (_hE : E.IsSnc) {r : ℕ} (hr : m - 1 ≤ r)
    (hr1 : 1 ≤ r) :
    IsMCInvariant f (W f I m (r * Lcm m)) (r * Lcm m) ∧
      IsDBalanced f (W f I m (r * Lcm m)) (r * Lcm m) ∧
        ∀ S : BlowUpSequence X,
          (S.IsOrderGeSeq f I m E ↔ S.IsOrderGeSeq f (W f I m (r * Lcm m)) (r * Lcm m) E) :=
  ⟨isMCInvariant_W f n I m hI hm (Nat.mul_pos hr1 (Lcm_pos m)), isDBalanced_W f n I m hI hm hr,
    fun S => tuning_iff_E f n S I E m hI hm hr hr1⟩

end Hironaka.Sequence
