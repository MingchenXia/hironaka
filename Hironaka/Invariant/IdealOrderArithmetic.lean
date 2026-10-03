/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.OrderTaylor
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Derivative ideals of sums and products; cosupports of sums, products and powers

Sources: Włodarczyk 2005 §2.6 and §2.9 (arithmetical operations on marked ideals, Lemma `le:operations`),
Bierstone--Milman 2008 §3.2--3.3.

## Main results

For ideals `𝔞, 𝔟` of holomorphic germs (`sumIdeal` is the sum ideal of `RestrictedIdealExtension`):

* **cosupports** (along any subset `N`): `cosupport_sumIdeal`:
  `cosupp(𝔞 + 𝔟, μ) = cosupp(𝔞, μ) ∩ cosupp(𝔟, μ)`; `inter_cosupport_subset_cosupport_mul`:
  `cosupp(𝔞, μ) ∩ cosupp(𝔟, ν) ⊆ cosupp(𝔞𝔟, μ + ν)`; `cosupport_subset_cosupport_idealPow`:
  `cosupp(𝔞, μ) ⊆ cosupp(𝔞^ν, μν)`.

The reverse inclusion `cosupp(𝔞^ν, μν) ⊆ cosupp(𝔞, μ)` (multiplicativity of the order) is not proved here.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.IdealOrderArithmetic

open Hironaka.HolomorphicIdealSheaves
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder Hironaka.DerivativeIdeal Hironaka.OrderTaylor Hironaka.RestrictedIdealExtension

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

variable {𝔞 𝔟 : GermIdeal n M}

/-! ### Span lemmas -/

theorem mem_mul_iff {𝔭 𝔮 : GermIdeal n M} {x : M} {g : M → ℂ} :
    (𝔭.mul 𝔮).mem x g ↔
      IsInSpanAt (n := n) (fun s => ∃ a b, 𝔭.mem x a ∧ 𝔮.mem x b ∧ s = a * b) x g :=
  Iff.rfl

theorem mem_sumIdeal_iff {𝔭 𝔮 : GermIdeal n M} {x : M} {g : M → ℂ} :
    (sumIdeal 𝔭 𝔮).mem x g ↔ IsInSpanAt (n := n) (fun s => 𝔭.mem x s ∨ 𝔮.mem x s) x g :=
  Iff.rfl

/-- A product `a b` with `a ∈ 𝔭` and `b ∈ 𝔮` is a germ of `𝔭𝔮`. -/
theorem mul_mem_mul {𝔭 𝔮 : GermIdeal n M} {x : M} {a b : M → ℂ} (ha : 𝔭.mem x a) (hb : 𝔮.mem x b)
    (hab : HolomorphicAt n (fun p => a p * b p) x) : (𝔭.mul 𝔮).mem x (fun p => a p * b p) :=
  mem_mul_iff.mpr (isInSpanAt_of_eq_mul (s := a * b) ⟨a, b, ha, hb, rfl⟩ hab (holomorphicAt_const 1)
    (Eventually.of_forall fun p => by simp))

/-- The left summand lies in the sum ideal (for an ideal of holomorphic germs). -/
theorem le_sumIdeal_left' (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) : 𝔞.Le (sumIdeal 𝔞 𝔟) :=
  fun x g hg => mem_sumIdeal_iff.mpr (isInSpanAt_of_eq_mul (Or.inl hg) (h𝔞 x g hg)
    (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm))

/-- The right summand lies in the sum ideal (for an ideal of holomorphic germs). -/
theorem le_sumIdeal_right' (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x) : 𝔟.Le (sumIdeal 𝔞 𝔟) :=
  fun x g hg => mem_sumIdeal_iff.mpr (isInSpanAt_of_eq_mul (Or.inr hg) (h𝔟 x g hg)
    (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm))

/-! ### Cosupports of sums, products and powers -/

section Cosupport

variable {N : Set M} {x : M}

/-- Functions vanishing to order `μ` along `N` at `x` are closed under holomorphic combinations. -/
theorem vanishesToOrderOn_sum_mul {K : ℕ} {c s : Fin K → M → ℂ} {μ : ℕ}
    (hc : ∀ k, HolomorphicAt n (c k) x) (hs : ∀ k, VanishesToOrderOn n N x μ (s k)) :
    VanishesToOrderOn n N x μ (fun p => ∑ k, c k p * s k p) := by
  choose h hh hsh using hs
  refine ⟨fun p => ∑ k, c k p * h k p, mem_idealPow_sum _ fun k _ =>
    mul_mem_idealPow (hc k) (hh k), ?_⟩
  filter_upwards [eventually_all.2 hsh] with p hp hpN
  exact Finset.sum_congr rfl fun k _ => by rw [hp k hpN]

/-- A germ in the span of germs vanishing to order `μ` along `N` vanishes to order `μ`. -/
theorem IsInSpanAt.vanishesToOrderOn {S : (M → ℂ) → Prop} {g : M → ℂ} {μ : ℕ}
    (hg : IsInSpanAt (n := n) S x g) (hS : ∀ s, S s → VanishesToOrderOn n N x μ s) :
    VanishesToOrderOn n N x μ g := by
  obtain ⟨-, K, s, c, hs, hc, hsum⟩ := hg
  obtain ⟨h, hh, hgh⟩ := vanishesToOrderOn_sum_mul (N := N) hc fun k => hS _ (hs k)
  exact ⟨h, hh, by filter_upwards [hsum, hgh] with p hp hp' hpN; rw [hp, hp' hpN]⟩

/-- **The cosupport of a sum** (Włodarczyk `le:operations`(1), equal marks):
`cosupp(𝔞 + 𝔟, μ) = cosupp(𝔞, μ) ∩ cosupp(𝔟, μ)`. -/
theorem cosupport_sumIdeal (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x) (μ : ℕ) :
    cosupport n N (sumIdeal 𝔞 𝔟) μ = cosupport n N 𝔞 μ ∩ cosupport n N 𝔟 μ := by
  ext x
  constructor
  · rintro ⟨hxN, hx⟩
    exact ⟨⟨hxN, fun g hg => hx g (le_sumIdeal_left' h𝔞 x g hg)⟩,
      ⟨hxN, fun g hg => hx g (le_sumIdeal_right' h𝔟 x g hg)⟩⟩
  · rintro ⟨⟨hxN, hx𝔞⟩, ⟨-, hx𝔟⟩⟩
    exact ⟨hxN, fun g hg => IsInSpanAt.vanishesToOrderOn (mem_sumIdeal_iff.mp hg)
      fun s hs => hs.elim (hx𝔞 s) (hx𝔟 s)⟩

/-- **The cosupport of a product** (Włodarczyk `le:operations`(2)):
`cosupp(𝔞, μ) ∩ cosupp(𝔟, ν) ⊆ cosupp(𝔞𝔟, μ + ν)`. -/
theorem inter_cosupport_subset_cosupport_mul (μ ν : ℕ) :
    cosupport n N 𝔞 μ ∩ cosupport n N 𝔟 ν ⊆ cosupport n N (𝔞.mul 𝔟) (μ + ν) := by
  rintro x ⟨⟨hxN, hx𝔞⟩, ⟨-, hx𝔟⟩⟩
  refine ⟨hxN, fun g hg => IsInSpanAt.vanishesToOrderOn (mem_mul_iff.mp hg) ?_⟩
  rintro s ⟨a, b, ha, hb, rfl⟩
  exact (hx𝔞 a ha).mul (hx𝔟 b hb)

/-- **The cosupport of a power**: `cosupp(𝔞, μ) ⊆ cosupp(𝔞^ν, μν)`. -/
theorem cosupport_subset_cosupport_idealPow (μ : ℕ) :
    ∀ ν : ℕ, cosupport n N 𝔞 μ ⊆ cosupport n N (idealPow 𝔞 ν) (μ * ν)
  | 0 => fun x hx => ⟨hx.1, fun g hg => by
      simpa using vanishesToOrderOn_zero (N := N) (holomorphicAt_of_mem_idealPow (q := 0) hg)⟩
  | ν + 1 => fun x hx => by
    have h := inter_cosupport_subset_cosupport_mul (𝔞 := idealPow 𝔞 ν) (𝔟 := 𝔞) (μ * ν) μ
      ⟨cosupport_subset_cosupport_idealPow μ ν hx, hx⟩
    rwa [Nat.mul_succ]

end Cosupport

end

end Hironaka.IdealOrderArithmetic
