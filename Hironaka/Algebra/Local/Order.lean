/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# The order of an ideal in a local ring

Kollár defines, for a smooth variety `X`, a nonzero ideal sheaf `I` and a point `x` with ideal
sheaf `𝔪ₓ`, the *order* of `I` at `x` as `ord_x I := max {r : 𝔪ₓ^r 𝒪_{x,X} ⊇ I 𝒪_{x,X}}`; for a
principal ideal `(f)` it is the multiplicity of the hypersurface `f = 0` [Kol07, Definition 47].
The order `IsLocalRing.ord I` of an ideal of a local ring is the supremum in `ℕ∞` of the `r` with
`I ≤ 𝔪^r`, so that the zero ideal has order `⊤` (Kollár assumes `I ≠ 0`; Krull's intersection
theorem, recalled in [Kol07, Definition 55], is what makes the two readings agree). This file
defines the order of an element and proves the elementary calculus:

* `ordElem f`, the order of the principal ideal `(f)`;
* `le_ord_iff`: `r ≤ ord I ↔ I ≤ 𝔪^r`, the characterization everything else reduces to;
* `ord_eq_top_iff`, `ordElem_eq_top_iff`: Krull's intersection theorem, `ord I = ⊤` iff `I = 0`
  for a Noetherian local ring;
* `ord_eq_iInf`, `ord_span`, `exists_ord_span_eq_ordElem`: the order of an ideal is the infimum
  of the orders of its elements, or of any generating set, attained by a generator when the set
  is finite and nonempty;
* `ord_top`, `ord_eq_zero_iff`, `one_le_ordElem_iff`, `ordElem_eq_one_iff`.

In `K⟦X⟧` with finitely many variables the order of an element is Mathlib's
`MvPowerSeries.order` (`MvPowerSeries.ordElem_eq_order`, in
`Hironaka/Algebra/Local/PowerSeries.lean`).

## The calculus of the order

The local forms of the elementary properties (1)–(4) of the cosupport of a marked ideal listed
in [Kol07, Definition 59]:

* `ord_anti` (property (1)): `I ≤ J → ord J ≤ ord I`.
* `le_ord_mul` (property (2)): `ord I + ord J ≤ ord (I * J)`.
* `ord_sup` (property (4)): `ord (I ⊔ J) = min (ord I) (ord J)`.
* `le_ord_pow` (property (3), one inclusion): `c * ord I ≤ ord (I ^ c)`.
* `ord_pow_of_ordElem_mul` (property (3), the converse) and
  `ord_span_singleton_mul_of_ordElem_mul`: both need multiplicativity of the order on
  elements, `ord (f g) = ord f + ord g` (used silently by Kollár in property (3) and in
  [Kol07, Theorem 54.2]), which holds in every regular local ring and, for rings containing `ℚ`,
  is `ordElem_mul_of_algebraRat` of `Hironaka/Algebra/Local/CohenIso.lean`, through `R̂ ≅ K⟦x⟧`;
  here they take it as an explicit hypothesis.
* `ord_le_ord_map` (the proof of [Wlo05, Lemma 2.10.3]: "the order of an ideal does not drop
  but may rise after restriction"): for a local homomorphism `φ`, `ord I ≤ ord (I.map φ)`; the
  quotient `R/(x₁)` is the case `φ = Ideal.Quotient.mk`.
* `ordAlong` (Kollár's `ord_Z I := ord_η I` at the generic point, [Kol07, Definition 47]): the
  order of `I` in the localization at a prime.

The scheme-level statements of Definition 47 (upper semicontinuity, `ord_Z`, `max-ord`) are
proved for the order of an ideal sheaf, `Scheme.IdealSheafData.ord`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- **The order of an element**: `ord f = ord (f)`, the multiplicity of the hypersurface `f = 0`
[Kol07, Definition 47]. -/
noncomputable def ordElem (f : R) : ℕ∞ :=
  ord (Ideal.span {f})

theorem le_ord_of_le {I : Ideal R} {r : ℕ} (h : I ≤ maximalIdeal R ^ r) : (r : ℕ∞) ≤ ord I :=
  le_iSup₂_of_le r h le_rfl

/-- `r ≤ ord I` iff `I ≤ 𝔪^r`; uses that the powers of `𝔪` decrease. -/
theorem le_ord_iff {I : Ideal R} {r : ℕ} : (r : ℕ∞) ≤ ord I ↔ I ≤ maximalIdeal R ^ r := by
  refine ⟨fun h => ?_, le_ord_of_le⟩
  by_contra hI
  have hs : ∀ s : ℕ, I ≤ maximalIdeal R ^ s → s < r := by
    intro s hs
    by_contra hrs
    push Not at hrs
    exact hI (hs.trans (Ideal.pow_le_pow_right hrs))
  have hr : r ≠ 0 := by
    rintro rfl
    exact hI (by simp)
  have hle : ord I ≤ ((r - 1 : ℕ) : ℕ∞) :=
    iSup₂_le fun s hs' => by exact_mod_cast Nat.le_sub_one_of_lt (hs s hs')
  have hlt : ((r - 1 : ℕ) : ℕ∞) < r := by exact_mod_cast Nat.sub_one_lt hr
  exact absurd (h.trans hle) (not_le.mpr hlt)

theorem mem_maximalIdeal_pow_iff_le_ordElem {f : R} {r : ℕ} :
    f ∈ maximalIdeal R ^ r ↔ (r : ℕ∞) ≤ ordElem f := by
  rw [ordElem, le_ord_iff, Ideal.span_singleton_le_iff_mem]

/-- The order is antitone: `I ≤ J → ord J ≤ ord I` (property (1) of the cosupport in
[Kol07, Definition 59]). -/
theorem ord_anti {I J : Ideal R} (h : I ≤ J) : ord J ≤ ord I := by
  rw [← ENat.forall_natCast_le_iff_le]
  intro r hr
  exact le_ord_iff.mpr (h.trans (le_ord_iff.mp hr))

/-- The unit ideal has order `0`. -/
@[simp]
theorem ord_top : ord (⊤ : Ideal R) = 0 := by
  refine le_antisymm (iSup₂_le fun r hr => ?_) bot_le
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp
  · exfalso
    have : maximalIdeal R = ⊤ := top_le_iff.mp (hr.trans (Ideal.pow_le_self hr0.ne'))
    exact (maximalIdeal.isMaximal R).ne_top this

/-- `ord I = 0` iff `I` is the unit ideal (in a local ring a proper ideal lies in `𝔪`). -/
theorem ord_eq_zero_iff {I : Ideal R} : ord I = 0 ↔ I = ⊤ := by
  constructor
  · intro h
    by_contra hI
    have h1 : ((1 : ℕ) : ℕ∞) ≤ ord I :=
      le_ord_iff.mpr (by rw [pow_one]; exact le_maximalIdeal hI)
    rw [h] at h1
    exact absurd h1 (by simp)
  · rintro rfl
    exact ord_top

/-- `1 ≤ ord f` iff `f ∈ 𝔪`. -/
theorem one_le_ordElem_iff {f : R} : 1 ≤ ordElem f ↔ f ∈ maximalIdeal R := by
  rw [← Nat.cast_one, ← mem_maximalIdeal_pow_iff_le_ordElem, pow_one]

/-- `ord f = 1` iff `f ∈ 𝔪 ∖ 𝔪²`. -/
theorem ordElem_eq_one_iff {f : R} :
    ordElem f = 1 ↔ f ∈ maximalIdeal R ∧ f ∉ maximalIdeal R ^ 2 := by
  rw [← one_le_ordElem_iff, mem_maximalIdeal_pow_iff_le_ordElem]
  induction ordElem f using ENat.recTopCoe with
  | top => simp
  | coe m =>
    constructor
    · intro h
      rw [h]
      exact ⟨le_rfl, by norm_num⟩
    · rintro ⟨h1, h2⟩
      have h1' : 1 ≤ m := by exact_mod_cast h1
      have h2' : ¬ 2 ≤ m := fun h => h2 (by exact_mod_cast h)
      exact_mod_cast (show m = 1 by omega)

/-- The order of an ideal is the infimum of the orders of its elements. -/
theorem ord_eq_iInf (I : Ideal R) : ord I = ⨅ f ∈ I, ordElem f := by
  refine le_antisymm (le_iInf₂ fun f hf => ord_anti ((Ideal.span_singleton_le_iff_mem _).mpr hf)) ?_
  rw [← ENat.forall_natCast_le_iff_le]
  intro r hr
  refine le_ord_iff.mpr fun f hf => ?_
  exact mem_maximalIdeal_pow_iff_le_ordElem.mpr (hr.trans (iInf₂_le f hf))

/-- The order of `⟨S⟩` is the infimum of the orders of the generators. -/
theorem ord_span (S : Set R) : ord (Ideal.span S) = ⨅ f ∈ S, ordElem f := by
  refine le_antisymm (le_iInf₂ fun f hf => ord_anti ?_) ?_
  · exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span hf)
  · rw [← ENat.forall_natCast_le_iff_le]
    intro r hr
    refine le_ord_iff.mpr (Ideal.span_le.mpr fun f hf => ?_)
    exact mem_maximalIdeal_pow_iff_le_ordElem.mpr (hr.trans (iInf₂_le f hf))

/-- For a finite nonempty generating set the infimum is attained by a generator. -/
theorem exists_ord_span_eq_ordElem {S : Set R} (hS : S.Finite) (hne : S.Nonempty) :
    ∃ f ∈ S, ord (Ideal.span S) = ordElem f := by
  obtain ⟨f, hf, hmin⟩ := hS.toFinset.exists_min_image ordElem (by simpa using hne)
  rw [hS.mem_toFinset] at hf
  refine ⟨f, hf, ?_⟩
  rw [ord_span]
  refine le_antisymm (iInf₂_le f hf) (le_iInf₂ fun g hg => ?_)
  exact hmin g (hS.mem_toFinset.mpr hg)

section Noetherian

variable [IsNoetherianRing R]

/-- In a Noetherian local ring the only ideal of infinite order is the zero ideal (Krull's
intersection theorem, recalled in [Kol07, Definition 55]). -/
theorem ord_eq_top_iff {I : Ideal R} : ord I = ⊤ ↔ I = ⊥ := by
  constructor
  · intro h
    have hle : ∀ r : ℕ, I ≤ maximalIdeal R ^ r := fun r => le_ord_iff.mp (h ▸ le_top)
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (I := maximalIdeal R)
      (maximalIdeal.isMaximal R).ne_top]
    exact le_iInf hle
  · rintro rfl
    rw [ENat.eq_top_iff_forall_ge]
    exact fun r => le_ord_of_le bot_le

/-- The only element of infinite order is `0`. -/
theorem ordElem_eq_top_iff {f : R} : ordElem f = ⊤ ↔ f = 0 := by
  rw [ordElem, ord_eq_top_iff, Ideal.span_singleton_eq_bot]

end Noetherian

section Calculus

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Superadditivity, `ord I + ord J ≤ ord (I J)`, from `𝔪^a 𝔪^b = 𝔪^(a+b)` (property (2) of the
cosupport in [Kol07, Definition 59]). -/
theorem le_ord_mul (I J : Ideal R) : ord I + ord J ≤ ord (I * J) := by
  rw [← ENat.forall_natCast_le_iff_le]
  intro r hr
  rw [le_ord_iff]
  by_cases hI : ord I = ⊤
  · exact Ideal.mul_le_left.trans (le_ord_iff.mp (by rw [hI]; exact le_top))
  by_cases hJ : ord J = ⊤
  · exact Ideal.mul_le_right.trans (le_ord_iff.mp (by rw [hJ]; exact le_top))
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hI
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hJ
  have hIa : I ≤ maximalIdeal R ^ a := le_ord_iff.mp ha.le
  have hJb : J ≤ maximalIdeal R ^ b := le_ord_iff.mp hb.le
  have hr' : r ≤ a + b := by
    rw [← ha, ← hb] at hr
    exact_mod_cast hr
  calc I * J ≤ maximalIdeal R ^ a * maximalIdeal R ^ b := Ideal.mul_mono hIa hJb
    _ = maximalIdeal R ^ (a + b) := (pow_add _ _ _).symm
    _ ≤ maximalIdeal R ^ r := Ideal.pow_le_pow_right hr'

/-- `ord (I + J) = min (ord I) (ord J)` (property (4) of the cosupport in
[Kol07, Definition 59]). -/
theorem ord_sup (I J : Ideal R) : ord (I ⊔ J) = min (ord I) (ord J) := by
  refine le_antisymm ?_ ?_ <;> rw [← ENat.forall_natCast_le_iff_le] <;> intro r hr
  · rw [le_ord_iff, sup_le_iff] at hr
    exact le_min_iff.mpr ⟨le_ord_iff.mpr hr.1, le_ord_iff.mpr hr.2⟩
  · rw [le_min_iff] at hr
    exact le_ord_iff.mpr (sup_le (le_ord_iff.mp hr.1) (le_ord_iff.mp hr.2))

/-- `c · ord I ≤ ord (I ^ c)` (one inclusion of property (3) of the cosupport in
[Kol07, Definition 59]). -/
theorem le_ord_pow (I : Ideal R) (c : ℕ) : (c : ℕ∞) * ord I ≤ ord (I ^ c) := by
  induction c with
  | zero => simp
  | succ c ih =>
    calc ((c + 1 : ℕ) : ℕ∞) * ord I = (c : ℕ∞) * ord I + ord I := by push_cast; ring
      _ ≤ ord (I ^ c) + ord I := add_le_add ih le_rfl
      _ ≤ ord (I ^ c * I) := le_ord_mul _ _
      _ = ord (I ^ (c + 1)) := by rw [pow_succ]

/-- The order does not drop under a local homomorphism, `ord I ≤ ord (I.map φ)` (the proof of
[Wlo05, Lemma 2.10.3]; the inclusion (58.2) of [Kol07, 58] is its sheaf form);
restriction to `R/(x₁)` is the case `φ = Ideal.Quotient.mk`. -/
theorem ord_le_ord_map {S : Type*} [CommRing S] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ]
    (I : Ideal R) : ord I ≤ ord (I.map φ) := by
  rw [← ENat.forall_natCast_le_iff_le]
  intro r hr
  rw [le_ord_iff] at hr ⊢
  calc I.map φ ≤ (maximalIdeal R ^ r).map φ := Ideal.map_mono hr
    _ = (maximalIdeal R).map φ ^ r := Ideal.map_pow _ _ _
    _ ≤ maximalIdeal S ^ r := Ideal.pow_right_mono (map_maximalIdeal_le φ) r

theorem ordElem_one : ordElem (1 : R) = 0 := by
  rw [ordElem, Ideal.span_singleton_one, ord_top]

/-- Multiplicativity of the order on elements implies `ord (f ^ n) = n · ord f`. -/
theorem ordElem_pow_of_ordElem_mul
    (hmul : ∀ f g : R, ordElem (f * g) = ordElem f + ordElem g) (f : R) (n : ℕ) :
    ordElem (f ^ n) = (n : ℕ∞) * ordElem f := by
  induction n with
  | zero => simp [ordElem_one]
  | succ n ih =>
    rw [pow_succ, hmul, ih]
    push_cast
    ring

theorem ord_bot : ord (⊥ : Ideal R) = ⊤ := by
  rw [ENat.eq_top_iff_forall_ge]
  exact fun r => le_ord_of_le bot_le

variable [IsNoetherianRing R]

/-- Given multiplicativity of the order on elements, `ord (I ^ c) = c · ord I` for `c ≥ 1` (the
equality behind property (3) of the cosupport in [Kol07, Definition 59]).  Pick a generator `f`
of `I` with `ord f = ord I`; then `f ^ c ∈ I ^ c` has order `c · ord I`. -/
theorem ord_pow_of_ordElem_mul (hmul : ∀ f g : R, ordElem (f * g) = ordElem f + ordElem g)
    (I : Ideal R) {c : ℕ} (hc : 1 ≤ c) : ord (I ^ c) = (c : ℕ∞) * ord I := by
  refine le_antisymm ?_ (le_ord_pow I c)
  have hc0 : (c : ℕ∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hc)
  by_cases hI : I = ⊥
  · subst hI
    rw [Ideal.bot_pow (Nat.one_le_iff_ne_zero.mp hc), ord_bot, ENat.mul_top hc0]
  obtain ⟨S, hSfin, hS'⟩ := Submodule.fg_def.mp (IsNoetherian.noetherian I)
  have hS : Ideal.span S = I := hS'
  have hne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · exact absurd (by rw [← hS, h, Ideal.span_empty]) hI
    · exact h
  obtain ⟨f, hf, hord⟩ := exists_ord_span_eq_ordElem hSfin hne
  rw [hS] at hord
  have hfI : f ∈ I := hS ▸ Ideal.subset_span hf
  calc ord (I ^ c) ≤ ordElem (f ^ c) :=
        ord_anti ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.pow_mem_pow hfI c))
    _ = (c : ℕ∞) * ordElem f := ordElem_pow_of_ordElem_mul hmul f c
    _ = (c : ℕ∞) * ord I := by rw [hord]

/-- Given multiplicativity of the order on elements, `ord (f I) = ord f + ord I`. -/
theorem ord_span_singleton_mul_of_ordElem_mul
    (hmul : ∀ f g : R, ordElem (f * g) = ordElem f + ordElem g) (f : R) (I : Ideal R) :
    ord (Ideal.span {f} * I) = ordElem f + ord I := by
  refine le_antisymm ?_ (le_ord_mul _ _)
  by_cases hI : I = ⊥
  · subst hI
    rw [Ideal.mul_bot, ord_bot, add_top]
  obtain ⟨S, hSfin, hS'⟩ := Submodule.fg_def.mp (IsNoetherian.noetherian I)
  have hS : Ideal.span S = I := hS'
  have hne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · exact absurd (by rw [← hS, h, Ideal.span_empty]) hI
    · exact h
  obtain ⟨g, hg, hord⟩ := exists_ord_span_eq_ordElem hSfin hne
  rw [hS] at hord
  have hgI : g ∈ I := hS ▸ Ideal.subset_span hg
  calc ord (Ideal.span {f} * I) ≤ ordElem (f * g) :=
        ord_anti ((Ideal.span_singleton_le_iff_mem _).mpr
          (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self f) hgI))
    _ = ordElem f + ordElem g := hmul f g
    _ = ordElem f + ord I := by rw [hord]

end Calculus

section Along

variable {R : Type*} [CommRing R]

/-- The order of `I` along the prime `P`, computed in the local ring `R_P`: Kollár's
`ord_Z I := ord_η I` at the generic point `η` of `Z` [Kol07, Definition 47]. -/
noncomputable def ordAlong (P : Ideal R) [P.IsPrime] (I : Ideal R) : ℕ∞ :=
  ord (I.map (algebraMap R (Localization.AtPrime P)))

end Along

end IsLocalRing
