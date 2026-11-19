/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Order

/-!
# Colon ideals by powers of a nonzero element

The ideal-theoretic identities behind the transform of a marked ideal `(I, m)` under a blow-up,
`π_*^{-1}(I, m) = (𝒪(mF) · π^* I, m)` [Kol07, Definition 60], computed at a stalk where the
exceptional divisor `F` is cut out by a single element `u`: dividing by `𝒪(mF)` is taking the
colon `(A : u^m)`. In a commutative ring `R`:

* `Ideal.colon_coe_span_singleton_pow`: the colon by the ideal `(u)^k` is the colon by `{u^k}`;
* `Ideal.colon_singleton_pow_mono`: `(A : u^s) ⊆ (A : u^t)` for `s ≤ t`;
* `Ideal.span_pow_mul_colon_of_le`: exact division, `A = (u^a) · (A : u^a)` when `A ⊆ (u^a)`;

and, when `R` is a domain and `u ≠ 0`:

* `Ideal.colon_span_pow_mul_self`: cancellation, `((u^k) · C : u^k) = C`;
* `Ideal.colon_mul_pow_add`, `Ideal.colon_pow_pow_mul`, `Ideal.colon_sup_pow`: the colon of a
  product, a power or a sum of ideals contained in the corresponding powers of `(u)` is the
  product, power or sum of the colons — the stalk form of the rules for products and sums of
  marked ideals [Kol07, Definition 59].

In a Noetherian local ring whose order (`IsLocalRing.ord`) is multiplicative,
`J ⊆ (u^m)` with `u ∈ 𝔪` and `ord J ≤ m` forces `(J : u^m) = (1)`
(`IsLocalRing.colon_span_singleton_pow_eq_top_of_ord_le`).

None of these is stated in the sources; they are elementary. They are the local computations
behind the weak transform of an ideal sheaf [Hir64, Ch. 0, §5, p. 142] on the scheme side, and
behind the algebra of marked transforms of ideal sheaves on analytic manifolds.
-/

public section

/-! ### Colon algebra in a domain: exact division by a power of a nonzero element -/

namespace Ideal

variable {R : Type*} [CommRing R]

/-- The colon by the set of elements of the ideal `(u)^k` is the colon by the singleton
`{u ^ k}`: the form in which a colon stalk `(π⁻¹(J)_a : I_{F,a}^k)` meets a generator `u` of the
stalk `I_{F,a}` of the exceptional ideal. -/
theorem colon_coe_span_singleton_pow (A : Ideal R) (u : R) (k : ℕ) :
    A.colon (SetLike.coe (Ideal.span {u} ^ k)) = A.colon {u ^ k} := by
  rw [Ideal.span_singleton_pow, Submodule.colon_span]

/-- The colon by a smaller power is smaller: `(A : u^s) ⊆ (A : u^t)` for `s ≤ t`. At a stalk this
compares the transforms of one ideal under two markings, as in the proof of
[Kol07, Theorem 100]. -/
theorem colon_singleton_pow_mono (A : Ideal R) (u : R) {s t : ℕ} (hst : s ≤ t) :
    A.colon {u ^ s} ≤ A.colon {u ^ t} := by
  intro x hx
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx ⊢
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [pow_add, ← mul_assoc]
  exact Ideal.mul_mem_right _ _ hx

/-- Exact division: an ideal `A ⊆ (u^a)` is `u^a` times its colon, `A = (u^a) · (A : u^a)`.
This is the identity `π^* I = I_F^m · π_*^{-1}(I, m)` of [Kol07, Definition 60] at a stalk. -/
theorem span_pow_mul_colon_of_le (A : Ideal R) (u : R) (a : ℕ) (hA : A ≤ Ideal.span {u ^ a}) :
    Ideal.span {u ^ a} * A.colon {u ^ a} = A := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_singleton_mul_le_iff]
    intro x hx
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx
    rwa [mul_comm]
  · intro x hx
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp (hA hx)
    have hg : g ∈ A.colon {u ^ a} := Submodule.mem_colon_singleton.mpr (by rwa [smul_eq_mul])
    have hcomm : g * u ^ a = u ^ a * g := mul_comm _ _
    rw [hcomm]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hg

variable [IsDomain R]

/-- Cancellation in a domain: `((u^k) · C : u^k) = C` for `u ≠ 0`. The stalk form of the
statement that the weak transform is determined by dividing out the exceptional ideal exactly
[Hir64, Ch. 0, §5, p. 142]. -/
theorem colon_span_pow_mul_self (C : Ideal R) {u : R} (hu : u ≠ 0) (k : ℕ) :
    (Ideal.span {u ^ k} * C).colon {u ^ k} = C := by
  ext x
  rw [Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have hx : x = z := mul_left_cancel₀ (pow_ne_zero k hu) (by rw [hzx, mul_comm])
    rwa [hx]
  · intro hx
    exact ⟨x, hx, mul_comm _ _⟩

/-- The product rule for colons by powers of a nonzero element: for `A ⊆ (u^a)` and `B ⊆ (u^b)`,
`(A B : u^{a+b}) = (A : u^a) (B : u^b)`. The stalk form of the product of marked ideals
`(I₁, m₁) · (I₂, m₂) = (I₁ I₂, m₁ + m₂)` [Kol07, Definition 59]. -/
theorem colon_mul_pow_add (A B : Ideal R) {u : R} (hu : u ≠ 0) (a b : ℕ)
    (hA : A ≤ Ideal.span {u ^ a}) (hB : B ≤ Ideal.span {u ^ b}) :
    (A * B).colon {u ^ (a + b)} = A.colon {u ^ a} * B.colon {u ^ b} := by
  conv_lhs => rw [← span_pow_mul_colon_of_le A u a hA, ← span_pow_mul_colon_of_le B u b hB]
  rw [mul_mul_mul_comm, Ideal.span_singleton_mul_span_singleton, ← pow_add]
  exact colon_span_pow_mul_self _ hu _

/-- The power rule: for `A ⊆ (u^k)`, `(A^s : u^{ks}) = (A : u^k)^s`. At a stalk this is the
compatibility of the marked transform with powers, `(Π_*^{-1} I)^s = Π_*^{-1}(I^s)`, used in the
proof of [Kol07, Theorem 100]. -/
theorem colon_pow_pow_mul (A : Ideal R) {u : R} (hu : u ≠ 0) (k s : ℕ)
    (hA : A ≤ Ideal.span {u ^ k}) :
    (A ^ s).colon {u ^ (k * s)} = A.colon {u ^ k} ^ s := by
  conv_lhs => rw [← span_pow_mul_colon_of_le A u k hA]
  rw [mul_pow, Ideal.span_singleton_pow, ← pow_mul]
  exact colon_span_pow_mul_self _ hu _

/-- The sum rule: for `A, B ⊆ (u^k)`, `(A + B : u^k) = (A : u^k) + (B : u^k)`. The stalk form of
the sum of marked ideals with the same marking, `(I₁, m) + (I₂, m) = (I₁ + I₂, m)`
[Kol07, Definition 59]. -/
theorem colon_sup_pow (A B : Ideal R) {u : R} (hu : u ≠ 0) (k : ℕ)
    (hA : A ≤ Ideal.span {u ^ k}) (hB : B ≤ Ideal.span {u ^ k}) :
    (A ⊔ B).colon {u ^ k} = A.colon {u ^ k} ⊔ B.colon {u ^ k} := by
  conv_lhs => rw [← span_pow_mul_colon_of_le A u k hA, ← span_pow_mul_colon_of_le B u k hB]
  rw [← Ideal.mul_sup]
  exact colon_span_pow_mul_self _ hu _

end Ideal

/-! ### The colon by a power of a parameter of order `≤ m` -/

namespace IsLocalRing

section ColonOrder

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- In a Noetherian local ring with multiplicative order, if `J ⊆ (u^m)` for `u ∈ 𝔪` and
`ord J ≤ m`, the colon `(J : u^m)` is the unit ideal — `J = u^m · (J : u^m)`
(`Ideal.span_pow_mul_colon_of_le`), so `m + ord (J : u^m) ≤ ord (u^m) + ord (J : u^m) = ord J ≤ m`.
This is the algebra behind "the order of `I` along `E^{jk}` is reduced by `m`" in the proof of
[Kol07, Lemma 102] and in the one-dimensional case of the induction of [Kol07, 70]; not stated
in the sources. -/
theorem colon_span_singleton_pow_eq_top_of_ord_le
    (hmul : ∀ f g : R, ordElem (f * g) =
      ordElem f + ordElem g)
    {u : R} (hu : u ∈ IsLocalRing.maximalIdeal R) {J : Ideal R} {m : ℕ}
    (hle : J ≤ Ideal.span {u} ^ m)
    (hord : ord J ≤ m) : J.colon ↑(Ideal.span {u} ^ m) = ⊤ := by
  rw [Ideal.span_singleton_pow] at hle ⊢
  -- `J = u^m · (J : u^m)` (`Ideal.span_pow_mul_colon_of_le`)
  have hJ : J = Ideal.span {u ^ m} * J.colon ↑(Ideal.span {u ^ m}) := by
    rw [Submodule.colon_span]
    exact (Ideal.span_pow_mul_colon_of_le J u m hle).symm
  have hordJ : ord J =
      ordElem (u ^ m) + ord (J.colon ↑(Ideal.span {u ^ m})) := by
    conv_lhs => rw [hJ]
    exact ord_span_singleton_mul_of_ordElem_mul hmul _ _
  have hm_le : (m : ℕ∞) ≤ ordElem (u ^ m) := by
    rw [ordElem_pow_of_ordElem_mul hmul]
    calc (m : ℕ∞) = (m : ℕ∞) * 1 := (mul_one _).symm
      _ ≤ (m : ℕ∞) * ordElem u :=
        mul_le_mul_of_nonneg_left (one_le_ordElem_iff.mpr hu) zero_le
  have h0 : ord (J.colon ↑(Ideal.span {u ^ m})) = 0 := by
    have h1 : (m : ℕ∞) + ord (J.colon ↑(Ideal.span {u ^ m})) ≤ (m : ℕ∞) + 0 := by
      rw [add_zero]
      calc (m : ℕ∞) + ord (J.colon ↑(Ideal.span {u ^ m}))
          ≤ ordElem (u ^ m) + ord (J.colon ↑(Ideal.span {u ^ m})) :=
            add_le_add hm_le le_rfl
        _ = ord J := hordJ.symm
        _ ≤ m := hord
    exact le_antisymm ((WithTop.add_le_add_iff_left (ENat.natCast_ne_top m)).mp h1) bot_le
  exact ord_eq_zero_iff.mp h0

end ColonOrder

end IsLocalRing
