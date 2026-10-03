/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.HolomorphicGermAlgebra
set_option autoImplicit false

/-!
# Division of a coherent ideal by an invertible ideal

That is the only content of this module, in the germ-ideal encoding of
`Hironaka.HolomorphicIdealSheaves`: an ideal contained in an invertible one is
the invertible one times a **coherent** ideal, namely the colon ideal
`(𝔞 : 𝔩)`.  Nothing here is about blowups, the strict transform, or
principalization; it is the local division step those need.

The proof is local.  Fix `x`, take finitely many generators `s i` of `𝔞` on
`U₁ ∋ x` and a single generator `h` of `𝔩` on `U₂ ∋ x`.  Because
`𝔞 ⊆ 𝔩`, each `s i` is `c i · h` for a germ `c i` at `x`; shrinking to an
open `U ⊆ U₁ ∩ U₂` on which all `N` divisions hold turns the `c i` into
honest holomorphic functions, and they generate `(𝔞 : 𝔩)` on `U`.  The only
nonformal ingredient is the cancellation of `h`, which uses invertibility in
the exact form recorded by `GermIdeal.IsInvertible`: the local generator
vanishes identically on no nonempty open subset, hence `{h ≠ 0}` is dense and
two continuous functions agreeing there agree.

No Hironaka input, no compactness, no Kähler hypothesis.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.InvertibleIdealQuotient

open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-! ## Elementary transfers -/

/-- A function differentiable on an open set is holomorphic at each of its
points, in the germ sense used by `GermIdeal`. -/
theorem holomorphicAt_of_mdifferentiableOn {U : Set M} (hU : IsOpen U) {g : M → ℂ}
    (hg : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g U) {y : M} (hy : y ∈ U) :
    HolomorphicAt n g y := by
  filter_upwards [hU.mem_nhds hy] with z hz
  exact (hg z hz).mdifferentiableAt (hU.mem_nhds hz)

/-- Span membership only depends on the germ. -/
theorem IsInSpanAt.congr' {S : (M → ℂ) → Prop} {x : M} {g g' : M → ℂ}
    (hg : IsInSpanAt (n := n) S x g) (h : g =ᶠ[𝓝 x] g') :
    IsInSpanAt (n := n) S x g' := by
  obtain ⟨hhol, N, s, a, hs, ha, hsum⟩ := hg
  refine ⟨hhol.congr h, N, s, a, hs, ha, ?_⟩
  filter_upwards [hsum, h] with y hy hy'
  rw [← hy']
  exact hy

/-- A generator of an ideal lies in that ideal. -/
theorem isInSpanAt_self {S : (M → ℂ) → Prop} {x : M} {g : M → ℂ} (hS : S g)
    (hg : HolomorphicAt n g x) : IsInSpanAt (n := n) S x g :=
  isInSpanAt_of_eq_mul hS hg (holomorphicAt_const 1)
    (Eventually.of_forall fun _ => by simp)

/-- **Cancellation of an invertible local generator.**  If `h` vanishes
identically on no nonempty open subset of `U`, then `h · F = h · G` near a
point of `U` forces `F = G` near that point, for holomorphic `F`, `G`.  This is
the only place where the nonvanishing clause of `GermIdeal.IsInvertible` is
used. -/
theorem eventuallyEq_of_mul_eventuallyEq {U : Set M} (hU : IsOpen U) {h : M → ℂ}
    (hnon : ∀ W : Set M, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, h y ≠ 0)
    {x : M} (hxU : x ∈ U) {F G : M → ℂ}
    (hF : HolomorphicAt n F x) (hG : HolomorphicAt n G x)
    (heq : ∀ᶠ y in 𝓝 x, h y * F y = h y * G y) :
    F =ᶠ[𝓝 x] G := by
  have hmem : {y | y ∈ U ∧ HolomorphicAt n F y ∧ HolomorphicAt n G y ∧
      h y * F y = h y * G y} ∈ 𝓝 x := by
    filter_upwards [hU.mem_nhds hxU, hF.eventually, hG.eventually, heq] with y h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hmem
  have hall : ∀ y ∈ V, F y = G y := by
    intro z hzV
    by_contra hz
    have hWopen : IsOpen {y ∈ V | F y ≠ G y} := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      have hyV : y ∈ V := hy.1
      have hFy : HolomorphicAt n F y := (hVsub hyV).2.1
      have hGy : HolomorphicAt n G y := (hVsub hyV).2.2.1
      have hne : ∀ᶠ w in 𝓝 y, F w ≠ G w := by
        have hcont : ContinuousAt (fun w => F w - G w) y :=
          hFy.continuousAt.sub hGy.continuousAt
        filter_upwards [hcont.eventually_ne (sub_ne_zero_of_ne hy.2)] with w hw
        exact fun hcontra => hw (by rw [hcontra]; ring)
      filter_upwards [hVopen.mem_nhds hyV, hne] with w h1 h2
      exact ⟨h1, h2⟩
    obtain ⟨y, hyW, hy0⟩ :=
      hnon _ hWopen (fun y hy => (hVsub hy.1).1) ⟨z, hzV, hz⟩
    exact hyW.2 (mul_left_cancel₀ hy0 (hVsub hyW.1).2.2.2)
  filter_upwards [hVopen.mem_nhds hxV] with y hy
  exact hall y hy

/-! ## The colon ideal -/

variable (𝔞 𝔩 : GermIdeal n M)

/-- The colon ideal `(𝔞 : 𝔩)`: germs `f` with `g · f ∈ 𝔞` for every `g ∈ 𝔩`. -/
def colon : GermIdeal n M where
  mem x f := HolomorphicAt n f x ∧ ∀ g, 𝔩.mem x g → 𝔞.mem x (fun y => g y * f y)

variable {𝔞 𝔩}

theorem mem_colon_iff {x : M} {f : M → ℂ} :
    (colon 𝔞 𝔩).mem x f ↔
      HolomorphicAt n f x ∧ ∀ g, 𝔩.mem x g → 𝔞.mem x (fun y => g y * f y) :=
  Iff.rfl

theorem mem_mul_iff {𝔟 : GermIdeal n M} {x : M} {g : M → ℂ} :
    (𝔞.mul 𝔟).mem x g ↔
      IsInSpanAt (n := n) (fun t => ∃ p q, 𝔞.mem x p ∧ 𝔟.mem x q ∧ t = p * q) x g :=
  Iff.rfl

/-- The colon ideal is what it should be: `𝔩 · (𝔞 : 𝔩) ⊆ 𝔞`.  Only coherence of
`𝔞` is used, to know that `𝔞` is closed under holomorphic combinations. -/
theorem mul_colon_le (h𝔞 : 𝔞.IsCoherent) : (𝔩.mul (colon 𝔞 𝔩)).Le 𝔞 := by
  intro x g hg
  obtain ⟨U, hU, hxU, N, s, hs, hgen⟩ := h𝔞 x
  refine (hgen x hxU g).mpr (IsInSpanAt.trans ?_ (mem_mul_iff.mp hg))
  rintro t ⟨p, q, hp, hq, rfl⟩
  exact (hgen x hxU _).mp ((mem_colon_iff.mp hq).2 p hp)

/-- The other inclusion: an ideal inside an invertible ideal is recovered from
its colon ideal, `𝔞 ⊆ 𝔩 · (𝔞 : 𝔩)`. -/
theorem le_mul_colon (h𝔞 : 𝔞.IsCoherent) (h𝔩 : 𝔩.IsInvertible) (hle : 𝔞.Le 𝔩) :
    𝔞.Le (𝔩.mul (colon 𝔞 𝔩)) := by
  intro x g hg
  obtain ⟨U, hU, hxU, h, hh, hnon, hgen⟩ := h𝔩 x
  have hhhol : HolomorphicAt n h x := holomorphicAt_of_mdifferentiableOn hU hh hxU
  have hhmem : 𝔩.mem x h := (hgen x hxU h).mpr (isInSpanAt_self rfl hhhol)
  obtain ⟨-, a, ha, haeq⟩ := isInSpanAt_eq_iff.mp ((hgen x hxU g).mp (hle x g hg))
  -- `a` is the quotient `g / h`, and it lies in the colon ideal.
  have hacolon : (colon 𝔞 𝔩).mem x a := by
    refine mem_colon_iff.mpr ⟨ha, fun g' hg' => ?_⟩
    obtain ⟨-, b, hb, hbeq⟩ := isInSpanAt_eq_iff.mp ((hgen x hxU g').mp hg')
    obtain ⟨U₁, hU₁, hxU₁, N, s, hs, hgen₁⟩ := h𝔞 x
    refine (hgen₁ x hxU₁ _).mpr
      (IsInSpanAt.congr' (IsInSpanAt.mul_left hb ((hgen₁ x hxU₁ g).mp hg)) ?_)
    filter_upwards [haeq, hbeq] with y hy hy'
    show b y * g y = g' y * a y
    rw [hy', hy]
    ring
  refine mem_mul_iff.mpr (isInSpanAt_of_eq_mul (s := h * a)
    ⟨h, a, hhmem, hacolon, rfl⟩
    (GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) (holomorphicAt_const 1) ?_)
  filter_upwards [haeq] with y hy
  show g y = 1 * (h y * a y)
  rw [hy]
  ring

theorem isCoherent_colon (h𝔞 : 𝔞.IsCoherent) (h𝔩 : 𝔩.IsInvertible) (hle : 𝔞.Le 𝔩) :
    (colon 𝔞 𝔩).IsCoherent := by
  intro x
  obtain ⟨U₁, hU₁, hxU₁, N, s, hs, hgen₁⟩ := h𝔞 x
  obtain ⟨U₂, hU₂, hxU₂, h, hh, hnon, hgen₂⟩ := h𝔩 x
  have hshol : ∀ (i : Fin N), ∀ y ∈ U₁, HolomorphicAt n (s i) y :=
    fun i _ hy => holomorphicAt_of_mdifferentiableOn hU₁ (hs i) hy
  have hhhol : ∀ y ∈ U₂, HolomorphicAt n h y :=
    fun _ hy => holomorphicAt_of_mdifferentiableOn hU₂ hh hy
  -- Divide each generator of `𝔞` by the local generator of `𝔩`.
  have hdiv : ∀ i : Fin N, ∃ c : M → ℂ, HolomorphicAt n c x ∧
      s i =ᶠ[𝓝 x] fun y => c y * h y := by
    intro i
    have hsi : 𝔞.mem x (s i) :=
      (hgen₁ x hxU₁ _).mpr (isInSpanAt_self ⟨i, rfl⟩ (hshol i x hxU₁))
    obtain ⟨-, c, hc, hceq⟩ := isInSpanAt_eq_iff.mp ((hgen₂ x hxU₂ _).mp (hle x _ hsi))
    exact ⟨c, hc, hceq⟩
  choose c hc hceq using hdiv
  -- Shrink to an open set on which all `N` divisions are valid.
  have hmem : {y | y ∈ U₁ ∧ y ∈ U₂ ∧ ∀ i, HolomorphicAt n (c i) y ∧
      s i y = c i y * h y} ∈ 𝓝 x := by
    have hall : ∀ᶠ y in 𝓝 x, ∀ i, HolomorphicAt n (c i) y ∧ s i y = c i y * h y :=
      eventually_all.mpr fun i => ((hc i).eventually.and (hceq i))
    filter_upwards [hU₁.mem_nhds hxU₁, hU₂.mem_nhds hxU₂, hall] with y h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hmem
  refine ⟨U, hUopen, hxU, N, c, ?_, ?_⟩
  · intro i y hy
    exact ((hUsub hy).2.2 i).1.mdifferentiableAt.mdifferentiableWithinAt
  intro y hy f
  have hyU₁ : y ∈ U₁ := (hUsub hy).1
  have hyU₂ : y ∈ U₂ := (hUsub hy).2.1
  have hdivU : ∀ᶠ z in 𝓝 y, ∀ i, s i z = c i z * h z := by
    filter_upwards [hUopen.mem_nhds hy] with z hz i
    exact ((hUsub hz).2.2 i).2
  constructor
  · -- `f ∈ (𝔞 : 𝔩)` implies `f` is a combination of the quotients `c i`.
    intro hfc
    obtain ⟨hfhol, hf⟩ := mem_colon_iff.mp hfc
    have hhmem : 𝔩.mem y h := (hgen₂ y hyU₂ h).mpr (isInSpanAt_self rfl (hhhol y hyU₂))
    obtain ⟨-, K, t, a, ht, ha, hsum⟩ := (hgen₁ y hyU₁ _).mp (hf h hhmem)
    choose σ hσ using fun j => ht j
    -- `h · f = h · ∑ aⱼ c (σ j)` near `y`, so the factor `h` cancels.
    have hGhol : HolomorphicAt n (fun z => ∑ j, a j z * c (σ j) z) y :=
      HolomorphicAt.sum _ fun j _ => (ha j).mul ((hUsub hy).2.2 (σ j)).1
    have hcancel : f =ᶠ[𝓝 y] fun z => ∑ j, a j z * c (σ j) z := by
      refine eventuallyEq_of_mul_eventuallyEq hU₂ hnon hyU₂ hfhol hGhol ?_
      filter_upwards [hsum, hdivU] with z hz hz'
      rw [hz, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hσ j, hz' (σ j)]
      ring
    refine IsInSpanAt.congr' ?_ hcancel.symm
    refine IsInSpanAt.sum (S := (· ∈ range c)) Finset.univ fun j _ => ?_
    exact IsInSpanAt.mul_left (ha j)
      (isInSpanAt_self ⟨σ j, rfl⟩ ((hUsub hy).2.2 (σ j)).1)
  · -- A combination of the quotients multiplies every element of `𝔩` into `𝔞`.
    intro hf
    refine mem_colon_iff.mpr ⟨hf.holomorphicAt, fun g hg => ?_⟩
    obtain ⟨-, b, hb, hbeq⟩ := isInSpanAt_eq_iff.mp ((hgen₂ y hyU₂ g).mp hg)
    obtain ⟨hfhol, K, t, a, ht, ha, hsum⟩ := hf
    choose σ hσ using fun j => ht j
    -- `h · f = ∑ aⱼ s (σ j) ∈ 𝔞`, hence `g · f = b · (h · f) ∈ 𝔞`.
    have hhf : IsInSpanAt (n := n) (· ∈ range s) y (fun z => h z * f z) := by
      refine IsInSpanAt.congr'
        (IsInSpanAt.sum (S := (· ∈ range s)) Finset.univ fun j _ =>
          IsInSpanAt.mul_left (ha j) (isInSpanAt_self ⟨σ j, rfl⟩ (hshol (σ j) y hyU₁))) ?_
      filter_upwards [hsum, hdivU] with z hz hz'
      rw [hz, Finset.mul_sum]
      refine (Finset.sum_congr rfl fun j _ => ?_).symm
      rw [hz' (σ j), ← hσ j]
      ring
    refine (hgen₁ y hyU₁ _).mpr (IsInSpanAt.congr' (IsInSpanAt.mul_left hb hhf) ?_)
    filter_upwards [hbeq] with z hz
    show b z * (h z * f z) = g z * f z
    rw [hz]
    ring

end

end Hironaka.InvertibleIdealQuotient
