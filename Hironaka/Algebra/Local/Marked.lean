/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Order
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Marked ideals and their cosupport

A *marked ideal* [Kol07, Definitions 48 and 59] is a pair `(I, m)` of an ideal and a natural
number, the mark being the order one pretends `I` has; a *marked element* (Kollár: marked
function) is a pair `(f, m)`.  This file gives the local, ring-level forms: the cosupport
predicate says `m ≤ ord I` ("the closed point lies in `cosupp (I, m)`"); products add the marks
and sums are defined for equal marks only; the four elementary properties of the cosupport
listed in [Kol07, Definition 59] are restatements of the calculus of the order
(`Hironaka/Algebra/Local/Order.lean`).  The marked derivative `D(I, m) = (D(I), m - 1)` acts on this
structure in `Hironaka/Algebra/Local/Derivative.lean`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

/-- **A marked ideal** [Kol07, Definitions 48 and 59]: an ideal `I` together with a mark
`m : ℕ`. -/
@[ext]
structure MarkedIdeal (R : Type*) [CommRing R] where
  /-- The ideal. -/
  I : Ideal R
  /-- The mark. -/
  m : ℕ

/-- **A marked element** (Kollár's "marked function", [Kol07, Definition 59]): an element `f`
together with a mark `m : ℕ`. -/
@[ext]
structure MarkedElem (R : Type*) where
  /-- The element. -/
  f : R
  /-- The mark. -/
  m : ℕ

namespace MarkedIdeal

variable {R : Type*} [CommRing R]

/-- The product `(I₁, m₁) · (I₂, m₂) = (I₁ I₂, m₁ + m₂)` [Kol07, Definition 59]. -/
instance : Mul (MarkedIdeal R) := ⟨fun J K => ⟨J.I * K.I, J.m + K.m⟩⟩

@[simp] theorem mul_I (J K : MarkedIdeal R) : (J * K).I = J.I * K.I := rfl

@[simp] theorem mul_m (J K : MarkedIdeal R) : (J * K).m = J.m + K.m := rfl

theorem mul_def (J K : MarkedIdeal R) : J * K = ⟨J.I * K.I, J.m + K.m⟩ := rfl

/-- The sum `(I₁, m) + (I₂, m) = (I₁ + I₂, m)`, "only sensible when the markings are the same"
[Kol07, Definition 59]. -/
def add (J K : MarkedIdeal R) (_h : J.m = K.m) : MarkedIdeal R := ⟨J.I ⊔ K.I, J.m⟩

@[simp] theorem add_I (J K : MarkedIdeal R) (h : J.m = K.m) : (J.add K h).I = J.I ⊔ K.I := rfl

@[simp] theorem add_m (J K : MarkedIdeal R) (h : J.m = K.m) : (J.add K h).m = J.m := rfl

section Local

variable [IsLocalRing R]

/-- The local cosupport predicate: "the closed point lies in `cosupp (I, m)`"
[Kol07, Definition 59], i.e. `m ≤ ord I`. -/
def InCosupp (J : MarkedIdeal R) : Prop := (J.m : ℕ∞) ≤ ord J.I

theorem inCosupp_iff_le_pow (J : MarkedIdeal R) : J.InCosupp ↔ J.I ≤ maximalIdeal R ^ J.m :=
  le_ord_iff

/-- `cosupp (J, m) ⊆ cosupp (I, m)` for `I ≤ J` (property (1) of [Kol07, Definition 59]). -/
theorem inCosupp_anti {I J : Ideal R} {m : ℕ} (h : I ≤ J) (hJ : InCosupp ⟨J, m⟩) :
    InCosupp ⟨I, m⟩ :=
  hJ.trans (ord_anti h)

/-- `cosupp (I₁, m₁) ∩ cosupp (I₂, m₂) ⊆ cosupp (I₁ I₂, m₁ + m₂)` (property (2) of
[Kol07, Definition 59]). -/
theorem inCosupp_mul {J K : MarkedIdeal R} (hJ : J.InCosupp) (hK : K.InCosupp) :
    (J * K).InCosupp := by
  unfold InCosupp at *
  rw [mul_I, mul_m, Nat.cast_add]
  exact (add_le_add hJ hK).trans (le_ord_mul _ _)

/-- `cosupp (I, m) ⊆ cosupp (I^c, mc)`: the inclusion of property (3) of [Kol07, Definition 59]
valid in every local ring. -/
theorem inCosupp_pow {J : MarkedIdeal R} (c : ℕ) (h : J.InCosupp) :
    InCosupp ⟨J.I ^ c, J.m * c⟩ := by
  unfold InCosupp at *
  dsimp only
  rw [Nat.cast_mul, mul_comm]
  exact (mul_le_mul_of_nonneg_left h zero_le).trans (le_ord_pow _ _)

/-- `cosupp (I₁ + I₂, m) = cosupp (I₁, m) ∩ cosupp (I₂, m)` (property (4) of
[Kol07, Definition 59]). -/
theorem inCosupp_add_iff {J K : MarkedIdeal R} (h : J.m = K.m) :
    (J.add K h).InCosupp ↔ J.InCosupp ∧ K.InCosupp := by
  unfold InCosupp
  rw [add_I, add_m, ord_sup, le_min_iff, h]

end Local

section Regular

variable [IsRegularLocalRing R]

/-- `cosupp (I, m) = cosupp (I^c, mc)` for `c ≥ 1` (property (3) of [Kol07, Definition 59]),
given multiplicativity of the order on elements (through `ord (I^c) = c · ord I`,
`ord_pow_of_ordElem_mul`). -/
theorem inCosupp_pow_iff_of_ordElem_mul
    (hmul : ∀ f g : R, ordElem (f * g) = ordElem f + ordElem g) (J : MarkedIdeal R) {c : ℕ}
    (hc : 1 ≤ c) : J.InCosupp ↔ InCosupp ⟨J.I ^ c, J.m * c⟩ := by
  refine ⟨inCosupp_pow c, fun h => ?_⟩
  unfold InCosupp at *
  dsimp only at h
  rw [ord_pow_of_ordElem_mul hmul J.I hc, Nat.cast_mul, mul_comm] at h
  exact (ENat.mul_le_mul_left_iff (by exact_mod_cast (show c ≠ 0 by omega))
    (ENat.natCast_ne_top c)).mp h

end Regular

end MarkedIdeal

namespace MarkedElem

variable {R : Type*}

/-- `(f₁, m₁) · (f₂, m₂) = (f₁ f₂, m₁ + m₂)` [Kol07, Definition 59]. -/
instance [Mul R] : Mul (MarkedElem R) := ⟨fun a b => ⟨a.f * b.f, a.m + b.m⟩⟩

@[simp] theorem mul_f [Mul R] (a b : MarkedElem R) : (a * b).f = a.f * b.f := rfl

@[simp] theorem mul_m [Mul R] (a b : MarkedElem R) : (a * b).m = a.m + b.m := rfl

theorem mul_def [Mul R] (a b : MarkedElem R) : a * b = ⟨a.f * b.f, a.m + b.m⟩ := rfl

/-- `(f₁, m) + (f₂, m) = (f₁ + f₂, m)` for equal marks [Kol07, Definition 59]. -/
def add [Add R] (a b : MarkedElem R) (_h : a.m = b.m) : MarkedElem R := ⟨a.f + b.f, a.m⟩

@[simp] theorem add_f [Add R] (a b : MarkedElem R) (h : a.m = b.m) : (a.add b h).f = a.f + b.f :=
  rfl

@[simp] theorem add_m [Add R] (a b : MarkedElem R) (h : a.m = b.m) : (a.add b h).m = a.m := rfl

variable [CommRing R]

/-- The marked ideal `(⟨f⟩, m)` of a marked element `(f, m)`. -/
def toMarkedIdeal (a : MarkedElem R) : MarkedIdeal R := ⟨Ideal.span {a.f}, a.m⟩

@[simp] theorem toMarkedIdeal_I (a : MarkedElem R) : a.toMarkedIdeal.I = Ideal.span {a.f} := rfl

@[simp] theorem toMarkedIdeal_m (a : MarkedElem R) : a.toMarkedIdeal.m = a.m := rfl

theorem toMarkedIdeal_mul (a b : MarkedElem R) :
    (a * b).toMarkedIdeal = a.toMarkedIdeal * b.toMarkedIdeal :=
  MarkedIdeal.ext (Ideal.span_singleton_mul_span_singleton _ _).symm rfl

variable [IsLocalRing R]

/-- The cosupport predicate for marked elements: `m ≤ ord f`. -/
def InCosupp (a : MarkedElem R) : Prop := (a.m : ℕ∞) ≤ ordElem a.f

theorem inCosupp_toMarkedIdeal (a : MarkedElem R) : a.toMarkedIdeal.InCosupp ↔ a.InCosupp :=
  Iff.rfl

theorem inCosupp_iff_mem_pow (a : MarkedElem R) : a.InCosupp ↔ a.f ∈ maximalIdeal R ^ a.m :=
  mem_maximalIdeal_pow_iff_le_ordElem.symm

end MarkedElem

end IsLocalRing
