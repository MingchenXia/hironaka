import Hironaka.Invariant.OrderTaylor
import Hironaka.MarkedIdeal.RestrictedIdealExtension

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Derivative ideals of sums and products; cosupports of sums, products and powers

Blueprint `hir:derivative-leibniz`, `hir:cosupport-operations` (`blueprint/src/hironaka.tex`, Hironaka phase H1).
Sources: Włodarczyk 2005 §2.6 and §2.9 (arithmetical operations on marked ideals, Lemma `le:operations`),
Bierstone--Milman 2008 §3.2--3.3.

## Main results

For ideals `𝔞, 𝔟` of holomorphic germs (`sumIdeal` is the sum ideal of `RestrictedIdealExtension`):

* **Leibniz** `derivIdeal_mul_le`: `𝓓(𝔞𝔟) ⊆ 𝓓(𝔞)·𝔟 + 𝔞·𝓓(𝔟)`;
* **sums** `derivIdeal_sumIdeal_le` / `sumIdeal_le_derivIdeal_sumIdeal`: `𝓓(𝔞 + 𝔟) = 𝓓(𝔞) + 𝓓(𝔟)`;
* **cosupports** (along any subset `N`): `cosupport_sumIdeal`:
  `cosupp(𝔞 + 𝔟, μ) = cosupp(𝔞, μ) ∩ cosupp(𝔟, μ)`; `inter_cosupport_subset_cosupport_mul`:
  `cosupp(𝔞, μ) ∩ cosupp(𝔟, ν) ⊆ cosupp(𝔞𝔟, μ + ν)`; `cosupport_subset_cosupport_idealPow`:
  `cosupp(𝔞, μ) ⊆ cosupp(𝔞^ν, μν)`.

The reverse inclusion `cosupp(𝔞^ν, μν) ⊆ cosupp(𝔞, μ)` (multiplicativity of the order) is not proved here.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.IdealOrderArithmetic

open Hironaka.HolomorphicIdealSheaves
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.DerivativeIdeal Hironaka.OrderTaylor
  Hironaka.RestrictedIdealExtension

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

theorem mem_derivIdeal_iff {x : M} {g : M → ℂ} :
    (derivIdeal 𝔞).mem x g ↔ IsInSpanAt (n := n) (DerivGen 𝔞 x) x g :=
  Iff.rfl

/-- A holomorphic multiple of a generator lies in the span. -/
theorem isInSpanAt_mul_of_mem {S : (M → ℂ) → Prop} {x : M} {c s : M → ℂ} (hs : S s)
    (hc : HolomorphicAt n c x) (hsh : HolomorphicAt n s x) :
    IsInSpanAt (n := n) S x (fun p => c p * s p) :=
  isInSpanAt_of_eq_mul hs (hc.mul hsh) hc (Eventually.of_forall fun _ => rfl)

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

/-! ### Leibniz rule for derivative ideals -/

/-- **Leibniz rule**: `𝓓(𝔞𝔟) ⊆ 𝓓(𝔞)·𝔟 + 𝔞·𝓓(𝔟)`. -/
theorem derivIdeal_mul_le (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x) :
    (derivIdeal (𝔞.mul 𝔟)).Le (sumIdeal ((derivIdeal 𝔞).mul 𝔟) (𝔞.mul (derivIdeal 𝔟))) := by
  intro x g hg
  refine mem_sumIdeal_iff.mpr (RelativePrincipalizationSpan.IsInSpanAt.trans ?_ (mem_derivIdeal_iff.mp hg))
  rintro s (hs | ⟨e, v, f, hx, hf, rfl⟩)
  · -- a germ of `𝔞𝔟` is a germ of `𝓓(𝔞)·𝔟`
    have hP : ((derivIdeal 𝔞).mul 𝔟).mem x s := mem_mul_iff.mpr
      ((mem_mul_iff.mp hs).mono fun t ⟨a, b, ha, hb, ht⟩ => ⟨a, b, le_derivIdeal h𝔞 x a ha, hb, ht⟩)
    exact isInSpanAt_of_eq_mul (Or.inl hP) (mem_mul_iff.mp hs).holomorphicAt (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => (one_mul _).symm)
  · obtain ⟨-, K, r, c, hr, hc, hsum⟩ := mem_mul_iff.mp hf
    choose a b ha hb hab using hr
    have hahol : ∀ k, HolomorphicAt n (a k) x := fun k => h𝔞 x _ (ha k)
    have hbhol : ∀ k, HolomorphicAt n (b k) x := fun k => h𝔟 x _ (hb k)
    have hrhol : ∀ k, HolomorphicAt n (r k) x := fun k => by
      rw [hab k]
      exact (hahol k).mul (hbhol k)
    have hprod := chartDeriv_eventuallyEq_sum_mul (e := e) (v := v) hx hc hrhol hsum
    have hab' : ∀ k, chartDeriv e v (r k) =ᶠ[𝓝 x] fun p =>
        chartDeriv e v (a k) p * b k p + a k p * chartDeriv e v (b k) p := by
      intro k
      have h1 := chartDeriv_eventuallyEq_sum_mul (e := e) (v := v) (f := r k) (N := 1)
        (a := fun _ => a k) (s := fun _ => b k) hx (fun _ => hahol k) (fun _ => hbhol k)
        (by rw [hab k]; exact Eventually.of_forall fun p => by simp)
      simpa using h1
    have hexp : (fun p => ∑ k, (chartDeriv e v (c k) p * (a k p * b k p) +
        c k p * (chartDeriv e v (a k) p * b k p) + c k p * (a k p * chartDeriv e v (b k) p)))
        =ᶠ[𝓝 x] chartDeriv e v f := by
      filter_upwards [hprod, eventually_all.2 hab'] with p hp hp'
      rw [hp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hp' k, hab k]
      simp only [Pi.mul_apply]
      ring
    refine isInSpanAt_congr ?_ hexp
    refine RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun k _ => ?_
    have hda := holomorphicAt_chartDeriv (v := v) hx (hahol k)
    have hdb := holomorphicAt_chartDeriv (v := v) hx (hbhol k)
    have hdc := holomorphicAt_chartDeriv (v := v) hx (hc k)
    refine RelativePrincipalizationSpan.IsInSpanAt.add
      (RelativePrincipalizationSpan.IsInSpanAt.add ?_ ?_) ?_
    · exact isInSpanAt_mul_of_mem (Or.inl (mul_mem_mul (le_derivIdeal h𝔞 x _ (ha k)) (hb k)
        ((hahol k).mul (hbhol k)))) hdc ((hahol k).mul (hbhol k))
    · exact isInSpanAt_mul_of_mem (Or.inl (mul_mem_mul (chartDeriv_mem_derivIdeal h𝔞 hx (ha k))
        (hb k) (hda.mul (hbhol k)))) (hc k) (hda.mul (hbhol k))
    · exact isInSpanAt_mul_of_mem (Or.inr (mul_mem_mul (ha k) (chartDeriv_mem_derivIdeal h𝔟 hx (hb k))
        ((hahol k).mul hdb))) (hc k) ((hahol k).mul hdb)

/-- **Derivative ideal of a sum**, one inclusion: `𝓓(𝔞 + 𝔟) ⊆ 𝓓(𝔞) + 𝓓(𝔟)`. -/
theorem derivIdeal_sumIdeal_le (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x) :
    (derivIdeal (sumIdeal 𝔞 𝔟)).Le (sumIdeal (derivIdeal 𝔞) (derivIdeal 𝔟)) := by
  intro x g hg
  refine mem_sumIdeal_iff.mpr (RelativePrincipalizationSpan.IsInSpanAt.trans ?_ (mem_derivIdeal_iff.mp hg))
  have hgen : ∀ s, (𝔞.mem x s ∨ 𝔟.mem x s) →
      IsInSpanAt (n := n) (fun t => (derivIdeal 𝔞).mem x t ∨ (derivIdeal 𝔟).mem x t) x s := by
    rintro s (hs | hs)
    · exact isInSpanAt_of_eq_mul (Or.inl (le_derivIdeal h𝔞 x s hs)) (h𝔞 x s hs)
        (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm)
    · exact isInSpanAt_of_eq_mul (Or.inr (le_derivIdeal h𝔟 x s hs)) (h𝔟 x s hs)
        (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm)
  rintro s (hs | ⟨e, v, f, hx, hf, rfl⟩)
  · exact RelativePrincipalizationSpan.IsInSpanAt.trans hgen (mem_sumIdeal_iff.mp hs)
  · obtain ⟨-, K, r, c, hr, hc, hsum⟩ := mem_sumIdeal_iff.mp hf
    have hrhol : ∀ k, HolomorphicAt n (r k) x := fun k => (hr k).elim (h𝔞 x _) (h𝔟 x _)
    have hprod := chartDeriv_eventuallyEq_sum_mul (e := e) (v := v) hx hc hrhol hsum
    refine isInSpanAt_congr ?_ hprod.symm
    refine RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun k _ => ?_
    refine RelativePrincipalizationSpan.IsInSpanAt.add ?_ ?_
    · exact RelativePrincipalizationSpan.IsInSpanAt.mul_left
        (holomorphicAt_chartDeriv hx (hc k)) (hgen _ (hr k))
    · have hd : (derivIdeal 𝔞).mem x (chartDeriv e v (r k)) ∨
          (derivIdeal 𝔟).mem x (chartDeriv e v (r k)) :=
        (hr k).elim (fun h => Or.inl (chartDeriv_mem_derivIdeal h𝔞 hx h))
          (fun h => Or.inr (chartDeriv_mem_derivIdeal h𝔟 hx h))
      exact isInSpanAt_mul_of_mem hd (hc k) (holomorphicAt_chartDeriv hx (hrhol k))

/-- **Derivative ideal of a sum**, the other inclusion: `𝓓(𝔞) + 𝓓(𝔟) ⊆ 𝓓(𝔞 + 𝔟)`. -/
theorem sumIdeal_le_derivIdeal_sumIdeal (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x) :
    (sumIdeal (derivIdeal 𝔞) (derivIdeal 𝔟)).Le (derivIdeal (sumIdeal 𝔞 𝔟)) := by
  intro x g hg
  refine mem_derivIdeal_iff.mpr (RelativePrincipalizationSpan.IsInSpanAt.trans ?_ (mem_sumIdeal_iff.mp hg))
  rintro s (hs | hs)
  · exact mem_derivIdeal_iff.mp (derivIdeal_mono (le_sumIdeal_left' h𝔞) x s hs)
  · exact mem_derivIdeal_iff.mp (derivIdeal_mono (le_sumIdeal_right' h𝔟) x s hs)

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
