/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictLe
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Restricted inclusions of ideal sheaves: pullback, cancellation, powers, zero loci

In the germ-ideal encoding, "an inclusion on `V`" is `RestrictLe V` (`RestrictedIdealWeight`); this module supplies
the calculus that Step 1 performs on it:

* `restrictLe_pullback` — a restricted inclusion on `V` pulls back to one on any `W` with
  `π(W) ⊆ V` (on `W₁`: `(𝔅 𝔅_m^p) 𝒪 ⊆ 𝔅_M 𝒪` along `W₁`);
* `restrictLe_of_restrictLe_mul_mul` — **cancellation** of an ideal invertible along `W`
  (`RestrictedIdealQuotient.IsInvertibleAlong`): `Res_W(𝔞 𝔩) ⊆ Res_W(𝔟 𝔩)` gives
  `Res_W 𝔞 ⊆ Res_W 𝔟`.  On `W₁`, where `𝔅_m 𝒪 = 𝒪(-G̃_m)` is invertible, this turns
  `𝔅 𝒪(-p G_m) ⊆ 𝒪(-G_M)` into `𝔅 ⊆ 𝒪(-(G_M - p G_m))`;
* the algebra of `GermIdeal.mul` the bookkeeping needs: `mul_comm'`, `mul_unitIdeal`,
  `idealPow_add`, and zero loci of products and powers.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.RestrictLeCalculus

noncomputable section

open Hironaka.HolomorphicIdealSheaves
open RelativePrincipalizationSpan InvertibleIdealQuotient RestrictedIdealWeight RestrictedIdealQuotient IdealWeightPowers GermIdealTotalTransform

section Algebra

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **`GermIdeal.mul` is commutative** (no coherence needed: the generating products are the
same functions). -/
theorem mul_comm' (𝔞 𝔟 : GermIdeal n M) : 𝔞.mul 𝔟 = 𝔟.mul 𝔞 := by
  have key : ∀ (𝔞 𝔟 : GermIdeal n M) (x : M) (g : M → ℂ),
      (𝔞.mul 𝔟).mem x g → (𝔟.mul 𝔞).mem x g := by
    intro 𝔞 𝔟 x g h
    refine mem_mul_iff.mpr (IsInSpanAt.mono ?_ (mem_mul_iff.mp h))
    rintro s ⟨a, b, ha, hb, rfl⟩
    exact ⟨b, a, hb, ha, mul_comm a b⟩
  exact GermIdeal.ext (funext fun x => funext fun g => propext ⟨key 𝔞 𝔟 x g, key 𝔟 𝔞 x g⟩)

/-- **The unit ideal is neutral** for a coherent ideal. -/
theorem mul_unitIdeal {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) :
    𝔞.mul (unitIdeal n M) = 𝔞 := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · refine mem_of_isInSpanAt_mem h𝔞 (IsInSpanAt.trans ?_ (mem_mul_iff.mp hg))
    rintro s ⟨a, b, ha, hb, rfl⟩
    refine isInSpanAt_self ?_ ((GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 ha).mul hb)
    refine mem_of_isInSpanAt_mem h𝔞 (isInSpanAt_of_eq_mul ha
      ((GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 ha).mul hb) hb
      (Eventually.of_forall fun y => ?_))
    show a y * b y = b y * a y
    ring
  · have hghol := GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
    refine mem_mul_iff.mpr (isInSpanAt_of_eq_mul ⟨g, fun _ => (1 : ℂ), hg,
      holomorphicAt_const (n := n) (x := x) (1 : ℂ), rfl⟩ hghol (holomorphicAt_const 1)
      (Eventually.of_forall fun y => ?_))
    show g y = 1 * (g y * 1)
    ring

/-- **`𝔞^(r+p) = 𝔞^r 𝔞^p`** for a coherent ideal. -/
theorem idealPow_add {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (r : ℕ) :
    ∀ p : ℕ, idealPow 𝔞 (r + p) = (idealPow 𝔞 r).mul (idealPow 𝔞 p)
  | 0 => by
      rw [Nat.add_zero, idealPow_zero, mul_unitIdeal (GermIdealPullbackCalculus.isCoherent_idealPow h𝔞 r)]
  | p + 1 => by
      rw [← Nat.add_assoc, idealPow_succ, idealPow_succ, idealPow_add h𝔞 r p,
        GermIdealTotalTransform.mul_assoc (GermIdealPullbackCalculus.isCoherent_idealPow h𝔞 r)
          (GermIdealPullbackCalculus.isCoherent_idealPow h𝔞 p) h𝔞]

/-! ### Zero loci of products and powers -/

/-- A point where every germ of `𝔟` vanishes is in the zero locus of `𝔞 𝔟`. -/
theorem zeroLocus_right_subset_mul (𝔞 𝔟 : GermIdeal n M) :
    𝔟.zeroLocus ⊆ (𝔞.mul 𝔟).zeroLocus := by
  intro y hy g hg
  obtain ⟨-, K, u, c, hu, -, husum⟩ := mem_mul_iff.mp hg
  choose a b ha hb hab using hu
  rw [husum.self_of_nhds]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [hab j]
  simp [hy (b j) (hb j)]

/-- Off both zero loci, off the zero locus of the product. -/
theorem notMem_zeroLocus_mul {𝔞 𝔟 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (h𝔟 : 𝔟.IsCoherent)
    {y : M} (h𝔞y : y ∉ 𝔞.zeroLocus) (h𝔟y : y ∉ 𝔟.zeroLocus) : y ∉ (𝔞.mul 𝔟).zeroLocus := by
  obtain ⟨a, ha, hay⟩ : ∃ a, 𝔞.mem y a ∧ a y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h𝔞y hcon
  obtain ⟨b, hb, hby⟩ : ∃ b, 𝔟.mem y b ∧ b y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h𝔟y hcon
  intro hZ
  have hmem := mem_mul_of_mem_mem ha hb ((GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 ha).mul
    (GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hb))
  exact mul_ne_zero hay hby (hZ _ hmem)

end Algebra

/-! ### Restricted inclusions -/

section Restricted

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Cancellation along `W`.**  If `𝔩` is invertible along `W` and `Res_W(𝔞 𝔩) ⊆ Res_W(𝔟 𝔩)`,
then `Res_W 𝔞 ⊆ Res_W 𝔟`.  For `g ∈ 𝔞` and the local generator `h` of `𝔩`, `g h ∈ 𝔞 𝔩` is
on `W` a combination of germs of `𝔟 𝔩`, each of which is `h` times a germ of `𝔟`; the factor
`h` is then cancelled along `W` (`eventuallyEq_within_of_mul_eventuallyEq_within`). -/
theorem restrictLe_of_restrictLe_mul_mul {W : Set M} {𝔞 𝔟 𝔩 : GermIdeal n M}
    (h𝔞 : 𝔞.IsCoherent) (h𝔟 : 𝔟.IsCoherent) (h𝔩 : IsInvertibleAlong n W 𝔩)
    (h : RestrictLe W (𝔞.mul 𝔩) (𝔟.mul 𝔩)) : RestrictLe W 𝔞 𝔟 := by
  intro x hx g hg
  obtain ⟨U, hU, hxU, h₀, hh₀d, hnon, hgen⟩ := h𝔩 x hx
  have hh₀ : HolomorphicAt n h₀ x := holomorphicAt_of_mdifferentiableOn hU hh₀d hxU
  have hh₀mem : 𝔩.mem x h₀ := (hgen x hxU h₀).mpr (isInSpanAt_self rfl hh₀)
  have hghol : HolomorphicAt n g x := GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  obtain ⟨N, s, a, hs, ha, hsum⟩ :=
    h x hx _ (mem_mul_of_mem_mem hg hh₀mem (hghol.mul hh₀))
  -- each `s i` is `h₀` times a germ of `𝔟`
  have hfac : ∀ i, ∃ t : M → ℂ, 𝔟.mem x t ∧ s i =ᶠ[𝓝 x] fun y => h₀ y * t y := by
    intro i
    obtain ⟨-, K, u, c, hu, hc, husum⟩ := mem_mul_iff.mp (hs i)
    choose p q hp hq hpq using hu
    choose e he hee using fun j => (isInSpanAt_eq_iff.mp ((hgen x hxU (q j)).mp (hq j))).2
    have hphol : ∀ j, HolomorphicAt n (p j) x :=
      fun j => GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 (hp j)
    refine ⟨fun y => ∑ j, (c j y * e j y) * p j y, ?_, ?_⟩
    · exact mem_of_isInSpanAt_mem h𝔟
        ⟨HolomorphicAt.sum _ fun j _ => ((hc j).mul (he j)).mul (hphol j), K, p,
          fun j y => c j y * e j y, hp, fun j => (hc j).mul (he j),
          Eventually.of_forall fun _ => rfl⟩
    · filter_upwards [husum, eventually_all.mpr hee] with y hy hy'
      rw [hy, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hpq j]
      show c j y * (p j y * q j y) = h₀ y * (c j y * e j y * p j y)
      rw [hy' j]
      ring
  choose t ht hteq using hfac
  have hthol : ∀ i, HolomorphicAt n (t i) x :=
    fun i => GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 (ht i)
  refine ⟨N, t, a, ht, ha, ?_⟩
  have hcancel : ∀ᶠ y in 𝓝 x, y ∈ W → h₀ y * g y = h₀ y * ∑ i, a i y * t i y := by
    filter_upwards [hsum, eventually_all.mpr hteq] with y hy hy' hyW
    rw [mul_comm (h₀ y) (g y), hy hyW, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hy' i]
    ring
  exact eventuallyEq_within_of_mul_eventuallyEq_within hU hnon hxU hghol
    (HolomorphicAt.sum _ fun i _ => (ha i).mul (hthol i)) hcancel

/-- Restricted inclusions compose. -/
theorem RestrictLe.trans {W : Set M} {𝔞 𝔟 𝔠 : GermIdeal n M} (h𝔞𝔟 : RestrictLe W 𝔞 𝔟)
    (h𝔟𝔠 : RestrictLe W 𝔟 𝔠) : RestrictLe W 𝔞 𝔠 := fun x hx g hg =>
  IsInSpanOnAt.trans (fun s hs => h𝔟𝔠 x hx s hs) (h𝔞𝔟 x hx g hg)

/-- An ambient inclusion is a restricted one, for a coherent target. -/
theorem restrictLe_of_le {W : Set M} {𝔞 𝔟 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent)
    (h : 𝔞.Le 𝔟) : RestrictLe W 𝔞 𝔟 := fun x _ g hg =>
  IsInSpanAt.restrict (isInSpanAt_self (h x g hg)
    (GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 (h x g hg)))

/-- Restricted inclusions are reflexive for coherent ideals. -/
theorem restrictLe_refl {W : Set M} {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) :
    RestrictLe W 𝔞 𝔞 :=
  restrictLe_of_le h𝔞 fun _ _ h => h

end Restricted

/-! ### Pulling back a restricted inclusion -/

section Pullback

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **A restricted inclusion pulls back.**  If `Res_V 𝔞 ⊆ Res_V 𝔟` and `f(W) ⊆ V`, then
`Res_W (𝔞 𝒪_Y) ⊆ Res_W (𝔟 𝒪_Y)`: a relation `a = ∑ dᵢ bᵢ` on `V` near `f y` composes with
`f` to one on `f⁻¹ V ⊇ W` near `y`. -/
theorem restrictLe_pullback {f : Y → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {V : Set M} {W : Set Y} (hWV : ∀ y ∈ W, f y ∈ V) {𝔞 𝔟 : GermIdeal n M}
    (h𝔟 : 𝔟.IsCoherent) (h : RestrictLe V 𝔞 𝔟) :
    RestrictLe W (GermIdeal.pullback (m := n) f 𝔞) (GermIdeal.pullback (m := n) f 𝔟) := by
  intro y hy G hG
  refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict (GermIdeal.mem_pullback_iff.mp hG))
  rintro s ⟨a, ha, rfl⟩
  obtain ⟨N, b, d, hb, hd, hsum⟩ := h (f y) (hWV y hy) a ha
  have hfy : ∀ᶠ z in 𝓝 y, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f z :=
    Eventually.of_forall fun _ => hf.contMDiffAt
  refine ⟨N, fun i => b i ∘ f, fun i => d i ∘ f, fun i => ?_,
    fun i => (hd i).comp_contMDiff hfy, ?_⟩
  · exact GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self (S := fun s => ∃ a, 𝔟.mem (f y) a ∧ s = a ∘ f) ⟨b i, hb i, rfl⟩
        ((GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 (hb i)).comp_contMDiff hfy))
  · filter_upwards [hf.continuous.continuousAt.eventually hsum] with z hz hzW
    exact hz (hWV z hzW)

end Pullback

end

end Hironaka.RestrictLeCalculus
