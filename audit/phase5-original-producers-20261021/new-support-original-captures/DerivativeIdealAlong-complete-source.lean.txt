import TranscendentalNakamaye.Pending.DerivativeIdeal

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Derivative ideals along a submanifold

Hironaka phase H3 (TN23-ENVELOPES; review finding R-2 on I-0981, agreed with TN-CLASSICAL in
C-0007); blueprint `mc:derivative-along` (`blueprint/src/maximal-contact.tex`).  Sources:
Bierstone--Milman 2008, §3.2 (`𝓓(𝓘)` is the image of `Der_N × 𝓘 → 𝒪_N`), Włodarczyk 2005, §2.6.

For a marked ideal `(M, N, E, 𝔞, d)` with `N ⊊ M` the derivative ideal of the algorithm is that of
the ideal `𝔞|_N` of `𝒪_N`, taken with the derivations of `N`.  In the ambient encoding of the
marked ideals (design note D1) it is represented by the ambient ideal `derivIdealAlong N 𝔞`,
generated at `x` by

* the germs of `𝔞_x` and of `𝓘_N` at `x`, and
* the derivatives `ξ(f) = ∑ₘ ξₘ ∂^e_{eₘ} f` (`f ∈ 𝔞_x`, `e` a chart at `x`) along holomorphic vector
  fields `ξ` **tangent to `N`** at `x`: `ξ(𝓘_N) ⊆ 𝓘_N` at `x` (`IsTangentField`).

Restricted to `N` this is the derivative ideal of `𝔞|_N` (derivations of `𝒪_N` are the ambient
derivations preserving `𝓘_N`, modulo `𝓘_N · Der`); it is NOT the restriction of the ambient
`𝓓(𝔞)`: for `N = {u = 0}` and `𝔞 = (u)`, `𝔞|_N = 0` but `1 = ∂ᵤ u ∈ 𝓓(𝔞)`, while
`derivIdealAlong N 𝔞 = (u)`.

* `derivIdealAlong_univ`: for `N = M` it is TN-CLASSICAL's `derivIdeal`.
* `le_derivIdealAlong`, `vanishingIdeal_le_derivIdealAlong`, `derivIdealAlong_mono`.
* `iterDerivIdealAlong N 𝔞 j`, `iterDerivIdealAlong_univ`.
* `derivIdealAlong_vanishingIdeal`: `𝓓_N(𝓘_N) = 𝓘_N` (the example of review finding R-2:
  `𝔞|_N = 0` stays `0` under derivatives along `N`).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold

namespace TranscendentalNakamaye.Pending.DerivativeIdealAlong

open FirstPass FirstPass.HolomorphicIdealSheaves DerivativeIdeal

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The derivative of `f` along the vector field `ξ = ∑ₘ ξₘ ∂/∂eₘ` written in the chart `e`. -/
def fieldDeriv (e : ComplexChart n M) (ξ : Fin n → M → ℂ) (f : M → ℂ) : M → ℂ :=
  fun p => ∑ m, ξ m p * chartDeriv e (EuclideanSpace.single m 1) f p

/-- **A holomorphic vector field tangent to `N` at `x`** (written in the chart `e`): holomorphic
coefficients, and the derivation `ξ` maps germs of `𝓘_N` at `x` to germs of `𝓘_N` at `x`. -/
structure IsTangentField (N : Set M) (e : ComplexChart n M) (ξ : Fin n → M → ℂ) (x : M) :
    Prop where
  mem_source : x ∈ e.val.source
  holomorphicAt : ∀ m, HolomorphicAt n (ξ m) x
  preserves : ∀ g, (vanishingIdeal (n := n) N).mem x g →
    (vanishingIdeal (n := n) N).mem x (fieldDeriv e ξ g)

/-- The generators of `𝓓_N(𝔞)` at `x`. -/
def DerivGenAlong (N : Set M) (𝔞 : GermIdeal n M) (x : M) (s : M → ℂ) : Prop :=
  𝔞.mem x s ∨ (vanishingIdeal (n := n) N).mem x s ∨
    ∃ (e : ComplexChart n M) (ξ : Fin n → M → ℂ) (f : M → ℂ),
      IsTangentField N e ξ x ∧ 𝔞.mem x f ∧ s = fieldDeriv e ξ f

/-- **The derivative ideal of `𝔞` along `N`** (ambient representative of `𝓓(𝔞|_N)`). -/
def derivIdealAlong (N : Set M) (𝔞 : GermIdeal n M) : GermIdeal n M where
  mem x := IsInSpanAt (n := n) (DerivGenAlong N 𝔞 x) x

/-- Iterated derivative ideals along `N`. -/
def iterDerivIdealAlong (N : Set M) (𝔞 : GermIdeal n M) : ℕ → GermIdeal n M
  | 0 => 𝔞
  | j + 1 => derivIdealAlong N (iterDerivIdealAlong N 𝔞 j)

variable {N : Set M} {𝔞 𝔟 : GermIdeal n M}

theorem holomorphicAt_fieldDeriv {e : ComplexChart n M} {ξ : Fin n → M → ℂ} {f : M → ℂ} {x : M}
    (hx : x ∈ e.val.source) (hξ : ∀ m, HolomorphicAt n (ξ m) x) (hf : HolomorphicAt n f x) :
    HolomorphicAt n (fieldDeriv e ξ f) x :=
  HolomorphicAt.sum _ fun m _ => (hξ m).mul (holomorphicAt_chartDeriv hx hf)

/-- `𝔞 ⊆ 𝓓_N(𝔞)`. -/
theorem le_derivIdealAlong (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    𝔞.Le (derivIdealAlong N 𝔞) :=
  fun x g hg => isInSpanAt_of_eq_mul (Or.inl hg) (h𝔞 x g hg) (holomorphicAt_const 1)
    (Eventually.of_forall fun _ => (one_mul _).symm)

/-- `𝓘_N ⊆ 𝓓_N(𝔞)`. -/
theorem vanishingIdeal_le_derivIdealAlong : (vanishingIdeal (n := n) N).Le (derivIdealAlong N 𝔞) :=
  fun _ _ hg => isInSpanAt_of_eq_mul (Or.inr (Or.inl hg)) hg.1 (holomorphicAt_const 1)
    (Eventually.of_forall fun _ => (one_mul _).symm)

/-- `𝓓_N` is monotone. -/
theorem derivIdealAlong_mono (h : 𝔞.Le 𝔟) : (derivIdealAlong N 𝔞).Le (derivIdealAlong N 𝔟) := by
  intro x g hg
  refine hg.mono fun s hs => ?_
  rcases hs with hs | hs | ⟨e, ξ, f, hξ, hf, rfl⟩
  · exact Or.inl (h x s hs)
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr ⟨e, ξ, f, hξ, h x f hf, rfl⟩)

/-- Every vector field is tangent to `N = M` (`𝓘_M` consists of the germs vanishing near `x`). -/
theorem isTangentField_univ {e : ComplexChart n M} {ξ : Fin n → M → ℂ} {x : M}
    (hx : x ∈ e.val.source) (hξ : ∀ m, HolomorphicAt n (ξ m) x) : IsTangentField univ e ξ x := by
  refine ⟨hx, hξ, fun g hg => ⟨?_, ?_⟩⟩
  · have hg0 : g =ᶠ[𝓝 x] fun _ => 0 := hg.2.mono fun p hp => hp (mem_univ p)
    exact holomorphicAt_fieldDeriv hx hξ ((holomorphicAt_const 0).congr hg0.symm)
  · have hg0 : g =ᶠ[𝓝 x] fun _ => 0 := hg.2.mono fun p hp => hp (mem_univ p)
    have hd : ∀ m, chartDeriv e (EuclideanSpace.single m 1) g =ᶠ[𝓝 x]
        chartDeriv e (EuclideanSpace.single m 1) (fun _ => (0 : ℂ)) := fun m => chartDeriv_congr hx hg0
    filter_upwards [eventually_all.2 hd] with p hp _
    have h0 : ∀ m : Fin n, chartDeriv e (EuclideanSpace.single m 1) (fun _ => (0 : ℂ)) p = 0 :=
      fun m => by simp [chartDeriv, Function.comp_def]
    simp only [fieldDeriv, hp, h0, mul_zero, Finset.sum_const_zero]

/-- **Along `N = M` the derivative ideal is the ambient one**: `𝓓_M(𝔞) = 𝓓(𝔞)`. -/
theorem derivIdealAlong_univ (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    derivIdealAlong univ 𝔞 = derivIdeal 𝔞 := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · refine RelativePrincipalizationSpan.IsInSpanAt.trans ?_ hg
    rintro s (hs | hs | ⟨e, ξ, f, hξ, hf, rfl⟩)
    · exact isInSpanAt_of_eq_mul (Or.inl hs) (h𝔞 x s hs) (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => (one_mul _).symm)
    · -- a germ vanishing near `x` is `0 · 1`
      have hs0 : s =ᶠ[𝓝 x] fun _ => 0 := hs.2.mono fun p hp => hp (mem_univ p)
      exact ⟨hs.1, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simpa using hs0⟩
    · refine RelativePrincipalizationSpan.IsInSpanAt.sum _ fun m _ => ?_
      exact isInSpanAt_of_eq_mul (Or.inr ⟨e, EuclideanSpace.single m 1, f, hξ.mem_source, hf, rfl⟩)
        ((hξ.holomorphicAt m).mul (holomorphicAt_chartDeriv hξ.mem_source (h𝔞 x f hf)))
        (hξ.holomorphicAt m) (Eventually.of_forall fun _ => rfl)
  · refine RelativePrincipalizationSpan.IsInSpanAt.trans ?_ hg
    rintro s (hs | ⟨e, v, f, hx, hf, rfl⟩)
    · exact isInSpanAt_of_eq_mul (Or.inl hs) (h𝔞 x s hs) (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => (one_mul _).symm)
    · -- `∂_v f = ∑ₘ vₘ ∂_{eₘ} f`, the field with constant coefficients `vₘ`
      refine isInSpanAt_of_eq_mul (s := fieldDeriv e (fun m _ => v m) f)
        (Or.inr (Or.inr ⟨e, fun m _ => v m, f,
          isTangentField_univ hx fun m => holomorphicAt_const _, hf, rfl⟩))
        (holomorphicAt_chartDeriv hx (h𝔞 x f hf)) (holomorphicAt_const 1) ?_
      refine Eventually.of_forall fun p => ?_
      simp only [fieldDeriv, chartDeriv, one_mul]
      conv_lhs => rw [← sum_smul_single v]
      rw [map_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [map_smul, smul_eq_mul]

/-- `𝓓^j_M(𝔞) = 𝓓^j(𝔞)`. -/
theorem iterDerivIdealAlong_univ (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    ∀ j, iterDerivIdealAlong univ 𝔞 j = iterDerivIdeal 𝔞 j
  | 0 => rfl
  | j + 1 => by
    rw [iterDerivIdealAlong, iterDerivIdealAlong_univ h𝔞 j, iterDerivIdeal_succ,
      derivIdealAlong_univ (holomorphicAt_of_mem_iterDerivIdeal h𝔞 j)]

/-- The germs vanishing on `N` near `x` are closed under holomorphic combinations. -/
theorem vanishingIdeal_mem_of_isInSpanAt {x : M} {g : M → ℂ}
    (hg : IsInSpanAt (n := n) ((vanishingIdeal (n := n) N).mem x) x g) :
    (vanishingIdeal (n := n) N).mem x g := by
  obtain ⟨hgh, K, s, a, hs, -, hsum⟩ := hg
  refine ⟨hgh, ?_⟩
  filter_upwards [hsum, eventually_all.2 fun k => (hs k).2] with p hp hp' hpN
  rw [hp]
  exact Finset.sum_eq_zero fun k _ => by rw [hp' k hpN, mul_zero]

/-- **The derivative ideal of `𝓘_N` along `N` is `𝓘_N`** (derivations tangent to `N` preserve
`𝓘_N`), whereas the ambient `𝓓(𝓘_N)` is the unit ideal near a hypersurface `N`. -/
theorem derivIdealAlong_vanishingIdeal :
    derivIdealAlong N (vanishingIdeal (n := n) N) = vanishingIdeal (n := n) N := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun hg => ?_,
    fun hg => vanishingIdeal_le_derivIdealAlong x g hg⟩)
  refine vanishingIdeal_mem_of_isInSpanAt (hg.mono ?_)
  rintro s (hs | hs | ⟨e, ξ, f, hξ, hf, rfl⟩)
  · exact hs
  · exact hs
  · exact hξ.preserves f hf

end

end TranscendentalNakamaye.Pending.DerivativeIdealAlong
