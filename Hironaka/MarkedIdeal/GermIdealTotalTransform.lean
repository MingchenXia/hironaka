/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Analytic.PullbackNonvanishing
import Hironaka.Analytic.InvertibleIdealCoherent
import Hironaka.Coherence.VanishingIdealCoherent
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Total transforms and the composition of the relative-principalization identity

> If `g : Y'' → Y'` is a further sequence of blowups adapted to `W'`, with
> divisor `H''` satisfying (i) for `W'`, then `g^* H + H''` satisfies (i) for the
> composition `f ∘ g` and `W`.

There was no total transform `g^* H` of an effective divisor, and `GermIdeal.mul` had neither associativity nor
compatibility with pullback.

Contents:

* `pullback_comp` — `𝔞 𝒪_Z = (𝔞 𝒪_Y) 𝒪_Z` for `Z → Y → X`.
* `pullback_mul` — `(𝔞𝔟) 𝒪_Y = (𝔞 𝒪_Y)(𝔟 𝒪_Y)`.  The inclusion `⊆` is
  `GermIdealPullbackCalculus.pullback_mul_le`; the reverse is the double
  expansion of a product of two spans.
* `mul_assoc` — associativity of `GermIdeal.mul` for coherent factors.  A
  `GermIdeal` is a bare membership predicate, so this is genuinely a theorem
  about spans and not a rearrangement.
* `isInvertible_mul` — `𝒪(-D)·𝒪(-D')` is again invertible, i.e. `D + D'` exists.
* `isInvertible_pullback` and `EffectiveDivisor.totalTransform` — **the total
  transform**, available along any holomorphic map whose exceptional locus has
  empty interior.  The nonvanishing clause is
  `MeteredDivisorOperations.exists_ne_zero_comp`.
* `pullback_vanishingIdeal_mul_comp` — the composition remark itself.

No Hironaka input, no compactness, no Kähler hypothesis.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.GermIdealTotalTransform

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences RelativePrincipalizationSpan GermIdealPullbackCalculus IdealWeightPowers InvertibleIdealQuotient

noncomputable section

section Algebra

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A coherent ideal absorbs spans of its own members. -/
theorem mem_of_isInSpanAt_mem {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {x : M} {g : M → ℂ}
    (hg : IsInSpanAt (n := n) (𝔞.mem x) x g) : 𝔞.mem x g := by
  obtain ⟨U, hU, hxU, N, s, hs, hgen⟩ := h𝔞 x
  exact (hgen x hxU g).mpr (IsInSpanAt.trans (fun t ht => (hgen x hxU t).mp ht) hg)

/-- Every member of a product ideal's generating family is a member of the
product ideal. -/
theorem mem_mul_of_mem_mem {𝔞 𝔟 : GermIdeal n M} {x : M} {a b : M → ℂ}
    (ha : 𝔞.mem x a) (hb : 𝔟.mem x b)
    (hhol : HolomorphicAt n (fun y => a y * b y) x) :
    (𝔞.mul 𝔟).mem x (fun y => a y * b y) :=
  mem_mul_iff.mpr
    (isInSpanAt_self ⟨a, b, ha, hb, rfl⟩ hhol)

/-- **Associativity of `GermIdeal.mul` for coherent factors.** -/
theorem mul_assoc {𝔞 𝔟 𝔠 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (h𝔟 : 𝔟.IsCoherent)
    (h𝔠 : 𝔠.IsCoherent) : (𝔞.mul 𝔟).mul 𝔠 = 𝔞.mul (𝔟.mul 𝔠) := by
  have hhol𝔞 : ∀ {x : M} {g : M → ℂ}, 𝔞.mem x g → HolomorphicAt n g x :=
    fun {_ _} h => GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 h
  have hhol𝔟 : ∀ {x : M} {g : M → ℂ}, 𝔟.mem x g → HolomorphicAt n g x :=
    fun {_ _} h => GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 h
  have hhol𝔠 : ∀ {x : M} {g : M → ℂ}, 𝔠.mem x g → HolomorphicAt n g x :=
    fun {_ _} h => GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 h
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · refine mem_mul_iff.mpr
      (IsInSpanAt.trans ?_ (mem_mul_iff.mp hg))
    rintro t ⟨p, q, hp, hq, rfl⟩
    obtain ⟨-, K, s, γ, hs, hγ, hsum⟩ := mem_mul_iff.mp hp
    choose a b ha hb hab using hs
    have hq' : HolomorphicAt n q x := hhol𝔠 hq
    have hterm : ∀ i : Fin K,
        IsInSpanAt (n := n)
          (fun s => ∃ p' q', 𝔞.mem x p' ∧ (𝔟.mul 𝔠).mem x q' ∧ s = p' * q') x
          (fun y => γ i y * (a i y * (b i y * q y))) := by
      intro i
      have hbq : (𝔟.mul 𝔠).mem x (fun y => b i y * q y) :=
        mem_mul_of_mem_mem (hb i) hq ((hhol𝔟 (hb i)).mul hq')
      have h0 : IsInSpanAt (n := n)
          (fun s => ∃ p' q', 𝔞.mem x p' ∧ (𝔟.mul 𝔠).mem x q' ∧ s = p' * q') x
          (fun y => a i y * (b i y * q y)) :=
        isInSpanAt_self ⟨a i, fun y => b i y * q y, ha i, hbq, rfl⟩
          ((hhol𝔞 (ha i)).mul ((hhol𝔟 (hb i)).mul hq'))
      exact IsInSpanAt.mul_left (hγ i) h0
    refine IsInSpanAt.congr'
      (IsInSpanAt.sum Finset.univ fun i _ => hterm i) ?_
    filter_upwards [hsum] with y hy
    show (∑ i, γ i y * (a i y * (b i y * q y))) = p y * q y
    rw [hy, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hab i]
    show γ i y * (a i y * (b i y * q y)) = γ i y * (a i y * b i y) * q y
    ring
  · refine mem_mul_iff.mpr
      (IsInSpanAt.trans ?_ (mem_mul_iff.mp hg))
    rintro t ⟨p, q, hp, hq, rfl⟩
    obtain ⟨-, K, s, γ, hs, hγ, hsum⟩ := mem_mul_iff.mp hq
    choose a b ha hb hab using hs
    have hp' : HolomorphicAt n p x := hhol𝔞 hp
    have hterm : ∀ i : Fin K,
        IsInSpanAt (n := n)
          (fun s => ∃ p' q', (𝔞.mul 𝔟).mem x p' ∧ 𝔠.mem x q' ∧ s = p' * q') x
          (fun y => γ i y * (p y * a i y * b i y)) := by
      intro i
      have hpa : (𝔞.mul 𝔟).mem x (fun y => p y * a i y) :=
        mem_mul_of_mem_mem hp (ha i) (hp'.mul (hhol𝔟 (ha i)))
      have h0 : IsInSpanAt (n := n)
          (fun s => ∃ p' q', (𝔞.mul 𝔟).mem x p' ∧ 𝔠.mem x q' ∧ s = p' * q') x
          (fun y => p y * a i y * b i y) :=
        isInSpanAt_self ⟨fun y => p y * a i y, b i, hpa, hb i, rfl⟩
          ((hp'.mul (hhol𝔟 (ha i))).mul (hhol𝔠 (hb i)))
      exact IsInSpanAt.mul_left (hγ i) h0
    refine IsInSpanAt.congr'
      (IsInSpanAt.sum Finset.univ fun i _ => hterm i) ?_
    filter_upwards [hsum] with y hy
    show (∑ i, γ i y * (p y * a i y * b i y)) = p y * q y
    rw [hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hab i]
    show γ i y * (p y * a i y * b i y) = p y * (γ i y * (a i y * b i y))
    ring

/-- **The product of two invertible ideals is invertible**: the sum `D + D'` of
two effective divisors exists. -/
theorem isInvertible_mul {𝔞 𝔟 : GermIdeal n M} (h𝔞 : 𝔞.IsInvertible)
    (h𝔟 : 𝔟.IsInvertible) : (𝔞.mul 𝔟).IsInvertible := by
  intro x
  obtain ⟨U, hU, hxU, h, hh, hnon, hgen⟩ := h𝔞 x
  obtain ⟨U', hU', hxU', h', hh', hnon', hgen'⟩ := h𝔟 x
  have hhhol : ∀ y ∈ U, HolomorphicAt n h y := fun y hy =>
    holomorphicAt_of_mdifferentiableOn hU hh hy
  have hh'hol : ∀ y ∈ U', HolomorphicAt n h' y := fun y hy =>
    holomorphicAt_of_mdifferentiableOn hU' hh' hy
  refine ⟨U ∩ U', hU.inter hU', ⟨hxU, hxU'⟩, fun y => h y * h' y, ?_, ?_, ?_⟩
  · intro y hy
    exact ((hhhol y hy.1).mul (hh'hol y hy.2)).mdifferentiableAt.mdifferentiableWithinAt
  · -- the product vanishes identically on no nonempty open subset
    intro W hW hWU hWne
    obtain ⟨y₁, hy₁W, hy₁⟩ := hnon W hW (fun z hz => (hWU hz).1) hWne
    have hWopen : IsOpen (W ∩ {z | h z ≠ 0}) := by
      rw [isOpen_iff_mem_nhds]
      intro z hz
      filter_upwards [hW.mem_nhds hz.1,
        (hhhol z (hWU hz.1).1).continuousAt.eventually_ne hz.2] with w h1 h2
      exact ⟨h1, h2⟩
    obtain ⟨y, hyW, hy⟩ := hnon' _ hWopen (fun z hz => (hWU hz.1).2) ⟨y₁, hy₁W, hy₁⟩
    exact ⟨y, hyW.1, mul_ne_zero hyW.2 hy⟩
  intro y hy v
  constructor
  · intro hv
    refine IsInSpanAt.trans ?_ (mem_mul_iff.mp hv)
    rintro t ⟨p, q, hp, hq, rfl⟩
    obtain ⟨-, α, hα, hαeq⟩ := isInSpanAt_eq_iff.mp ((hgen y hy.1 p).mp hp)
    obtain ⟨-, β, hβ, hβeq⟩ := isInSpanAt_eq_iff.mp ((hgen' y hy.2 q).mp hq)
    refine isInSpanAt_of_eq_mul rfl
      ((GermIdeal.IsInvertible.holomorphicAt_mem h𝔞 hp).mul
        (GermIdeal.IsInvertible.holomorphicAt_mem h𝔟 hq)) (hα.mul hβ) ?_
    filter_upwards [hαeq, hβeq] with z hz hz'
    show p z * q z = α z * β z * (h z * h' z)
    rw [hz, hz']
    ring
  · intro hv
    obtain ⟨hvhol, α, hα, hαeq⟩ := isInSpanAt_eq_iff.mp hv
    refine mem_mul_iff.mpr
      (isInSpanAt_of_eq_mul (s := fun z => h z * h' z)
        ⟨h, h', (hgen y hy.1 h).mpr
            (isInSpanAt_self rfl (hhhol y hy.1)),
          (hgen' y hy.2 h').mpr
            (isInSpanAt_self rfl (hh'hol y hy.2)), rfl⟩
        hvhol hα ?_)
    filter_upwards [hαeq] with z hz
    exact hz

end Algebra

/-! ## Functoriality of the pullback -/

section Functorial

variable {n : ℕ}
  {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z]

/-- **The pullback of a product is the product of the pullbacks.** -/
theorem pullback_mul {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {𝔞 𝔟 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) (h𝔟 : 𝔟.IsCoherent) :
    GermIdeal.pullback (m := n) f (𝔞.mul 𝔟) =
      (GermIdeal.pullback (m := n) f 𝔞).mul (GermIdeal.pullback (m := n) f 𝔟) := by
  have hhol𝔞 : ∀ {x : X} {g : X → ℂ}, 𝔞.mem x g → HolomorphicAt n g x :=
    fun {_ _} h => GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 h
  have hhol𝔟 : ∀ {x : X} {g : X → ℂ}, 𝔟.mem x g → HolomorphicAt n g x :=
    fun {_ _} h => GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 h
  refine GermIdeal.ext (funext fun y => funext fun g => propext
    ⟨fun hg => pullback_mul_le hf hhol𝔞 hhol𝔟 y g hg, fun hg => ?_⟩)
  have hfat : ∀ᶠ z in 𝓝 y, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f z :=
    Eventually.of_forall fun z => hf.contMDiffAt
  refine GermIdeal.mem_pullback_iff.mpr
    (IsInSpanAt.trans ?_ (mem_mul_iff.mp hg))
  rintro t ⟨p, q, hp, hq, rfl⟩
  obtain ⟨-, K, s, γ, hs, hγ, hsum⟩ := GermIdeal.mem_pullback_iff.mp hp
  obtain ⟨-, L, s', δ, hs', hδ, hsum'⟩ := GermIdeal.mem_pullback_iff.mp hq
  choose a ha hsa using hs
  choose b hb hsb using hs'
  have hterm : ∀ r : Fin K × Fin L,
      IsInSpanAt (n := n) (fun u => ∃ c, (𝔞.mul 𝔟).mem (f y) c ∧ u = c ∘ f) y
        (fun z => γ r.1 z * δ r.2 z * (s r.1 z * s' r.2 z)) := by
    rintro ⟨i, j⟩
    have hab : (𝔞.mul 𝔟).mem (f y) (fun x => a i x * b j x) :=
      mem_mul_of_mem_mem (ha i) (hb j) ((hhol𝔞 (ha i)).mul (hhol𝔟 (hb j)))
    have heq : (fun z => s i z * s' j z) = (fun x => a i x * b j x) ∘ f := by
      funext z
      rw [hsa i, hsb j]
      rfl
    have hhol : HolomorphicAt n (fun z => s i z * s' j z) y := by
      rw [heq]
      exact ((hhol𝔞 (ha i)).mul (hhol𝔟 (hb j))).comp_contMDiff hfat
    have h0 : IsInSpanAt (n := n) (fun u => ∃ c, (𝔞.mul 𝔟).mem (f y) c ∧ u = c ∘ f) y
        (fun z => s i z * s' j z) :=
      isInSpanAt_self ⟨_, hab, heq⟩ hhol
    exact IsInSpanAt.mul_left ((hγ i).mul (hδ j)) h0
  refine IsInSpanAt.congr'
    (IsInSpanAt.sum Finset.univ fun r _ => hterm r) ?_
  filter_upwards [hsum, hsum'] with z hz hz'
  show (∑ r : Fin K × Fin L, γ r.1 z * δ r.2 z * (s r.1 z * s' r.2 z)) = p z * q z
  rw [hz, hz', Finset.sum_mul_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The pullback is functorial**: `𝔞 𝒪_Z = (𝔞 𝒪_Y) 𝒪_Z`. -/
theorem pullback_comp {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) :
    GermIdeal.pullback (m := n) (f ∘ g) 𝔞 =
      GermIdeal.pullback (m := n) g (GermIdeal.pullback (m := n) f 𝔞) := by
  refine GermIdeal.ext (funext fun z => funext fun v => propext ⟨fun hv => ?_, fun hv => ?_⟩)
  · have hfat : ∀ᶠ y in 𝓝 (g z),
        ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f y :=
      Eventually.of_forall fun y => hf.contMDiffAt
    refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c, hc, rfl⟩
    have hchol : HolomorphicAt n c (f (g z)) :=
      GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hc
    have hcfhol : HolomorphicAt n (c ∘ f) (g z) := hchol.comp_contMDiff hfat
    have hcf : (GermIdeal.pullback (m := n) f 𝔞).mem (g z) (c ∘ f) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul ⟨c, hc, rfl⟩ hcfhol
        (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm))
    exact ⟨c ∘ f, hcf, rfl⟩
  · refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c, hc, rfl⟩
    refine IsInSpanAt.mono ?_
      (isInSpanAt_comp hg (GermIdeal.mem_pullback_iff.mp hc))
    rintro u' ⟨σ, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨d, hd, rfl⟩

/-- **The total transform of an invertible ideal is invertible**, along any
holomorphic map whose exceptional locus has empty interior.  This is what makes
`g^* H` an effective divisor. -/
theorem isInvertible_pullback {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hint : interior (exceptionalLocus n g) = ∅)
    {𝔞 : GermIdeal n Y} (h𝔞 : 𝔞.IsInvertible) :
    (GermIdeal.pullback (m := n) g 𝔞).IsInvertible := by
  intro z
  obtain ⟨U, hU, hzU, h, hh, hnon, hgen⟩ := h𝔞 (g z)
  have hhhol : ∀ y ∈ U, HolomorphicAt n h y := fun y hy =>
    holomorphicAt_of_mdifferentiableOn hU hh hy
  have hgat : ∀ {z' : Z}, ∀ᶠ w in 𝓝 z',
      ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g w :=
    fun {_} => Eventually.of_forall fun w => hg.contMDiffAt
  refine ⟨g ⁻¹' U, hU.preimage hg.continuous, hzU, h ∘ g, ?_, ?_, ?_⟩
  · intro w hw
    exact ((hhhol (g w) hw).comp_contMDiff hgat).mdifferentiableAt.mdifferentiableWithinAt
  · exact fun W hW hWU hWne =>
      MeteredDivisorOperations.exists_ne_zero_comp hg hint hnon hW hWU hWne
  intro w hw v
  constructor
  · intro hv
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hv)
    rintro u ⟨c, hc, rfl⟩
    refine IsInSpanAt.mono ?_ (isInSpanAt_comp hg ((hgen (g w) hw c).mp hc))
    rintro u' ⟨σ, rfl, rfl⟩
    rfl
  · intro hv
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ hv)
    rintro u rfl
    exact ⟨h, (hgen (g w) hw h).mpr
      (isInSpanAt_self rfl (hhhol (g w) hw)), rfl⟩

/-- The total transform `g^* D` of an effective divisor. -/
def EffectiveDivisor.totalTransform {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hint : interior (exceptionalLocus n g) = ∅) (D : EffectiveDivisor n Y) :
    EffectiveDivisor n Z where
  ideal := GermIdeal.pullback (m := n) g D.ideal
  isInvertible := isInvertible_pullback hg hint D.isInvertible

/-- The sum `D + D'` of two effective divisors, i.e. the product of their
ideals. -/
def EffectiveDivisor.add (D D' : EffectiveDivisor n Z) : EffectiveDivisor n Z where
  ideal := D.ideal.mul D'.ideal
  isInvertible := isInvertible_mul D.isInvertible D'.isInvertible

end Functorial

end

end Hironaka.GermIdealTotalTransform
