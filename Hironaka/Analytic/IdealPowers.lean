import Hironaka.Analytic.IdealProducts

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Products and powers of ideals present sums and multiples of weights

Source: Copy-4, `sec:qpsh` and `lem:ideal-comparison`
(`transcendental-nakamaye-copy4-20260911`).

`Pending/IdealWeightProducts` proves `ψ_{𝔞𝔟} = ψ_𝔞 + ψ_𝔟 + O(1)` in the form
that takes a presenting function for the product ideal as a *hypothesis*.  That
is enough to compare two given potentials, but `lem:ideal-comparison` needs the
constructive form as well, because it reads the inclusion

  `𝔅 · 𝔅̄_m^p ⊆ 𝔅̄_M`

off against `ψ_{𝔅̄_M} ≤ ψ_𝔅 + p ψ_{𝔅̄_m} + O(1)`, and no potential presenting
`𝔅 · 𝔅̄_m^p` has been named anywhere: the whole point is that `ψ_𝔅 + p ψ_{𝔅̄_m}`
*is* one.

This module supplies it.  The two statements are

* `hasAnalyticSingularitiesOfType_mul`: the sum of a potential of type `(c, 𝔞)`
  and one of type `(c, 𝔟)` has type `(c, 𝔞𝔟)`;
* `hasAnalyticSingularitiesOfType_pow`: `p • φ` has type `(c, 𝔞^p)`.

Both are honest strengthenings, not restatements: they carry the *coherence* of
the product ideal, which `sameSingularityTypeAt_mul` assumed as part of its third
hypothesis.  The content is the local identification

  `(𝔞𝔟)_y = ⟨gᵢhⱼ⟩_y`   for generators `g` of `𝔞` and `h` of `𝔟` on `U ∋ y`,

whose nontrivial direction expands a germ `∑ₜ aₜ (αₜ βₜ)` of the product ideal by
substituting the expansions of `αₜ` and `βₜ` — that is `IsInSpanAt.trans`
together with the pairwise-product span lemma below.  The weight identity is then
the exact family identity `generatorLog (mulFamily g h) = generatorLog g +
generatorLog h` of `Pending/IdealWeightProducts`, with the two bounded remainders
added.

The multiple is recorded as the `ℕ`-scalar multiple `p • φ` of `EReal`, i.e. as an
iterated sum.  That is deliberate: `((p : ℝ) : EReal) * φ` would force a case
analysis at `φ = ⊥` for `p = 0`, and nothing downstream needs the real scalar.

The unit ideal `unitIdeal` (every holomorphic germ) is recorded here too, since
it is `𝔞^0` and is presented by the constant `0`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.IdealWeightPowers

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
open Hironaka.IdealWeightComparison
open Hironaka.IdealWeightProducts
open Hironaka.RelativePrincipalizationSpan

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-! ### Span algebra of the family of pairwise products -/

/-- Span membership only depends on the germ. -/
theorem isInSpanAt_congr {S : (M → ℂ) → Prop} {x : M} {v v' : M → ℂ}
    (hv : IsInSpanAt (n := n) S x v) (hvv : v' =ᶠ[𝓝 x] v) :
    IsInSpanAt (n := n) S x v' := by
  obtain ⟨hhol, N, s, a, hs, ha, hsum⟩ := hv
  exact ⟨hhol.congr hvv.symm, N, s, a, hs, ha, hvv.trans hsum⟩

/-- A pairwise product of members of the two families is a member of the product
family. -/
theorem mem_range_mulFamily {N P : ℕ} (g : Fin N → M → ℂ) (h : Fin P → M → ℂ)
    (i : Fin N) (j : Fin P) :
    (fun y => g i y * h j y) ∈ range (mulFamily g h) :=
  ⟨finProdFinEquiv (i, j), funext fun y => mulFamily_apply g h i j y⟩

/-- **The product of two spanned germs is spanned by the product family.**  This
is the step that makes span transitivity applicable to the product ideal: the
double expansion `(∑ᵢ αᵢ sᵢ)(∑ⱼ βⱼ tⱼ) = ∑_{i,j} (αᵢβⱼ)(sᵢtⱼ)` is a finite sum
of multiples of members of `mulFamily g h`. -/
theorem isInSpanAt_mulFamily_mul {N P : ℕ} {g : Fin N → M → ℂ} {h : Fin P → M → ℂ}
    {x : M} (hgh : ∀ i, HolomorphicAt n (g i) x) (hhh : ∀ j, HolomorphicAt n (h j) x)
    {a b : M → ℂ}
    (ha : IsInSpanAt (n := n) (· ∈ range g) x a)
    (hb : IsInSpanAt (n := n) (· ∈ range h) x b) :
    IsInSpanAt (n := n) (· ∈ range (mulFamily g h)) x (fun y => a y * b y) := by
  obtain ⟨hah, K, s, α, hs, hα, hsum⟩ := ha
  obtain ⟨hbh, L, t, β, ht, hβ, hsum'⟩ := hb
  have hshol : ∀ i, HolomorphicAt n (s i) x := by
    intro i; obtain ⟨σ, hσ⟩ := hs i; exact hσ ▸ hgh σ
  have hthol : ∀ j, HolomorphicAt n (t j) x := by
    intro j; obtain ⟨τ, hτ⟩ := ht j; exact hτ ▸ hhh τ
  have hterm : ∀ q : Fin K × Fin L,
      IsInSpanAt (n := n) (· ∈ range (mulFamily g h)) x
        (fun y => α q.1 y * β q.2 y * (s q.1 y * t q.2 y)) := by
    rintro ⟨i, j⟩
    obtain ⟨σ, hσ⟩ := hs i
    obtain ⟨τ, hτ⟩ := ht j
    have hmem : (fun y => s i y * t j y) ∈ range (mulFamily g h) := by
      rw [← hσ, ← hτ]; exact mem_range_mulFamily g h σ τ
    exact isInSpanAt_of_eq_mul hmem
      (((hα i).mul (hβ j)).mul ((hshol i).mul (hthol j)))
      ((hα i).mul (hβ j)) (Eventually.of_forall fun _ => rfl)
  have hsum2 : IsInSpanAt (n := n) (· ∈ range (mulFamily g h)) x
      (fun y => ∑ q : Fin K × Fin L, α q.1 y * β q.2 y * (s q.1 y * t q.2 y)) :=
    IsInSpanAt.sum (n := n) Finset.univ fun q _ => hterm q
  refine isInSpanAt_congr hsum2 ?_
  filter_upwards [hsum, hsum'] with y hy hy'
  rw [hy, hy', Finset.sum_mul_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### The product ideal is locally generated by the product family -/

/-- **The local presentation of a product ideal.**  If `g` presents `𝔞` and `h`
presents `𝔟` on the same open set `U`, then `mulFamily g h` presents `𝔞𝔟` on
`U`. -/
theorem mem_mul_iff_isInSpanAt_mulFamily {𝔞 𝔟 : GermIdeal n M} {U : Set M}
    (hU : IsOpen U) {N P : ℕ} {g : Fin N → M → ℂ} {h : Fin P → M → ℂ}
    (hgdiff : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g i) U)
    (hhdiff : ∀ j, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (h j) U)
    (hgiff : ∀ y ∈ U, ∀ k, 𝔞.mem y k ↔ IsInSpanAt (n := n) (· ∈ range g) y k)
    (hhiff : ∀ y ∈ U, ∀ k, 𝔟.mem y k ↔ IsInSpanAt (n := n) (· ∈ range h) y k)
    {y : M} (hy : y ∈ U) (v : M → ℂ) :
    (𝔞.mul 𝔟).mem y v ↔ IsInSpanAt (n := n) (· ∈ range (mulFamily g h)) y v := by
  have hgh : ∀ i, HolomorphicAt n (g i) y := fun i =>
    Filter.eventually_of_mem (hU.mem_nhds hy) fun z hz =>
      (hgdiff i z hz).mdifferentiableAt (hU.mem_nhds hz)
  have hhh : ∀ j, HolomorphicAt n (h j) y := fun j =>
    Filter.eventually_of_mem (hU.mem_nhds hy) fun z hz =>
      (hhdiff j z hz).mdifferentiableAt (hU.mem_nhds hz)
  constructor
  · intro hv
    refine IsInSpanAt.trans ?_ (mem_mul_iff.mp hv)
    rintro w ⟨a, b, hamem, hbmem, rfl⟩
    exact isInSpanAt_mulFamily_mul hgh hhh ((hgiff y hy a).mp hamem)
      ((hhiff y hy b).mp hbmem)
  · intro hv
    refine mem_mul_iff.mpr (IsInSpanAt.mono ?_ hv)
    rintro w ⟨k, rfl⟩
    exact ⟨g (finProdFinEquiv.symm k).1, h (finProdFinEquiv.symm k).2,
      mem_of_isPresentation hU hy hgdiff hgiff _,
      mem_of_isPresentation hU hy hhdiff hhiff _, rfl⟩

/-- **Coherence is stable under products.** -/
theorem isCoherent_mul {𝔞 𝔟 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (h𝔟 : 𝔟.IsCoherent) :
    (𝔞.mul 𝔟).IsCoherent := by
  intro x
  obtain ⟨U, hU, hxU, N, g, hgdiff, hgiff⟩ := h𝔞 x
  obtain ⟨U', hU', hxU', P, h, hhdiff, hhiff⟩ := h𝔟 x
  refine ⟨U ∩ U', hU.inter hU', ⟨hxU, hxU'⟩, N * P, mulFamily g h, ?_, ?_⟩
  · intro k z hz
    exact ((hgdiff _ z hz.1).mono inter_subset_left).mul
      ((hhdiff _ z hz.2).mono inter_subset_right)
  · intro z hz k
    exact mem_mul_iff_isInSpanAt_mulFamily (hU.inter hU')
      (fun i z hz => (hgdiff i z hz.1).mono inter_subset_left)
      (fun j z hz => (hhdiff j z hz.2).mono inter_subset_right)
      (fun z hz => hgiff z hz.1) (fun z hz => hhiff z hz.2) hz k

/-! ### The weight of a product, constructively -/

/-- **`ψ_𝔞 + ψ_𝔟` presents `𝔞𝔟`.**  Unlike
`IdealWeightProducts.sameSingularityTypeAt_mul` this does not assume a presenting
function for the product ideal; it produces one, together with the coherence of
`𝔞𝔟`. -/
theorem hasAnalyticSingularitiesOfType_mul {φ φ' : M → EReal} {c : ℚ}
    {𝔞 𝔟 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hφ' : HasAnalyticSingularitiesOfType (n := n) φ' c 𝔟) :
    HasAnalyticSingularitiesOfType (n := n) (fun y => φ y + φ' y) c (𝔞.mul 𝔟) := by
  obtain ⟨hc, hcoh, hpres⟩ := hφ
  obtain ⟨-, hcoh', hpres'⟩ := hφ'
  refine ⟨hc, isCoherent_mul hcoh hcoh', fun x => ?_⟩
  obtain ⟨U, hU, hxU, N, g, hgdiff, hgiff, R, C₀, hRb, hφeq⟩ := hpres x
  obtain ⟨U', hU', hxU', P, h, hhdiff, hhiff, R', C₀', hR'b, hφ'eq⟩ := hpres' x
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  refine ⟨U ∩ U', hU.inter hU', ⟨hxU, hxU'⟩, N * P, mulFamily g h, ?_, ?_,
    fun y => R y + R' y, C₀ + C₀', ?_, ?_⟩
  · intro k z hz
    exact ((hgdiff _ z hz.1).mono inter_subset_left).mul
      ((hhdiff _ z hz.2).mono inter_subset_right)
  · intro z hz k
    exact mem_mul_iff_isInSpanAt_mulFamily (hU.inter hU')
      (fun i z hz => (hgdiff i z hz.1).mono inter_subset_left)
      (fun j z hz => (hhdiff j z hz.2).mono inter_subset_right)
      (fun z hz => hgiff z hz.1) (fun z hz => hhiff z hz.2) hz k
  · intro y hy
    have h1 := abs_le.mp (hRb y hy.1)
    have h2 := abs_le.mp (hR'b y hy.2)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · intro y hy
    dsimp only
    rw [hφeq y hy.1, hφ'eq y hy.2, generatorLog_mulFamily,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hcR.le)
        (EReal.coe_ne_top _), EReal.coe_add]
    exact add_add_add_comm _ _ _ _

/-! ### The unit ideal and powers -/

variable (n M) in
/-- The unit ideal: every germ holomorphic at the point. -/
def unitIdeal : GermIdeal n M where
  mem x v := HolomorphicAt n v x

theorem mem_unitIdeal_iff {x : M} {v : M → ℂ} :
    (unitIdeal n M).mem x v ↔
      IsInSpanAt (n := n) (· ∈ range (fun _ : Fin 1 => (1 : M → ℂ))) x v := by
  constructor
  · intro hv
    exact isInSpanAt_of_eq_mul ⟨0, rfl⟩ hv hv (Eventually.of_forall fun _ => by simp)
  · exact fun hv => hv.holomorphicAt

theorem isCoherent_unitIdeal : (unitIdeal n M).IsCoherent := fun x =>
  ⟨univ, isOpen_univ, mem_univ x, 1, fun _ => (1 : M → ℂ),
    fun _ => (mdifferentiable_const (I := 𝓘(ℂ, ComplexModel n)) (I' := 𝓘(ℂ, ℂ))
      (c := (1 : ℂ))).mdifferentiableOn,
    fun _ _ _ => mem_unitIdeal_iff⟩

/-- The `p`-th power `𝔞^p` of an ideal sheaf, with `𝔞^0` the unit ideal. -/
def idealPow (𝔞 : GermIdeal n M) : ℕ → GermIdeal n M
  | 0 => unitIdeal n M
  | p + 1 => (idealPow 𝔞 p).mul 𝔞

@[simp] theorem idealPow_zero (𝔞 : GermIdeal n M) : idealPow 𝔞 0 = unitIdeal n M := rfl

@[simp] theorem idealPow_succ (𝔞 : GermIdeal n M) (p : ℕ) :
    idealPow 𝔞 (p + 1) = (idealPow 𝔞 p).mul 𝔞 := rfl

/-- The constant `0` presents the unit ideal, for any positive exponent `c`. -/
theorem hasAnalyticSingularitiesOfType_unitIdeal {c : ℚ} (hc : 0 < c) :
    HasAnalyticSingularitiesOfType (n := n) (fun _ : M => (0 : EReal)) c
      (unitIdeal n M) := by
  refine ⟨hc, isCoherent_unitIdeal, fun x => ⟨univ, isOpen_univ, mem_univ x, 1,
    fun _ => (1 : M → ℂ), fun _ => (mdifferentiable_const
      (I := 𝓘(ℂ, ComplexModel n)) (I' := 𝓘(ℂ, ℂ)) (c := (1 : ℂ))).mdifferentiableOn,
    fun _ _ _ => mem_unitIdeal_iff, fun _ => (0 : ℝ), 0, fun _ _ => by simp,
    fun y _ => ?_⟩⟩
  have hlog : generatorLog (fun _ : Fin 1 => (1 : M → ℂ)) y = 0 := by
    rw [generatorLog_eq_log_sum]
    simp
  rw [hlog]
  simp

/-- **`p • ψ_𝔞` presents `𝔞^p`** (Copy-4, `sec:qpsh`).  This is the form
`lem:ideal-comparison` consumes: it converts an inclusion `𝔟 · 𝔞^p ⊆ 𝔠` into the
weight inequality `ψ_𝔠 ≤ ψ_𝔟 + p ψ_𝔞 + O(1)` with no potential for `𝔞^p` named
anywhere. -/
theorem hasAnalyticSingularitiesOfType_pow {φ : M → EReal} {c : ℚ}
    {𝔞 : GermIdeal n M} (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞) :
    ∀ p : ℕ, HasAnalyticSingularitiesOfType (n := n) (fun y => p • φ y) c
      (idealPow 𝔞 p)
  | 0 => by
    simpa using hasAnalyticSingularitiesOfType_unitIdeal (n := n) (M := M) hφ.1
  | p + 1 => by
    have ih := hasAnalyticSingularitiesOfType_pow hφ p
    have := hasAnalyticSingularitiesOfType_mul ih hφ
    simpa [succ_nsmul] using this

/-! ### The `O(1)` consequences -/

/-- **`ψ_{𝔞^p} = p ψ_𝔞 + O(1)` on a compact manifold**, with one constant. -/
theorem sameSingularityTypeOn_univ_pow [CompactSpace M] {φ φp : M → EReal} {c : ℚ}
    {𝔞 : GermIdeal n M} {p : ℕ}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hφp : HasAnalyticSingularitiesOfType (n := n) φp c (idealPow 𝔞 p)) :
    SameSingularityTypeOn φp (fun y => p • φ y) univ :=
  sameSingularityTypeOn_univ_of_eq_type hφp (hasAnalyticSingularitiesOfType_pow hφ p)

/-- **`lem:ideal-comparison`, weight form.**  An inclusion `𝔟 · 𝔞^p ⊆ 𝔠` of
coherent ideals is exactly the inequality `ψ_𝔟 + p ψ_𝔞 ≤ ψ_𝔠 + O(1)` between the
potentials that present them, with one constant on a compact manifold. -/
theorem moreSingularOn_univ_add_nsmul_of_mul_pow_le [CompactSpace M]
    {φ ψ χ : M → EReal} {c : ℚ} {𝔞 𝔟 𝔠 : GermIdeal n M} {p : ℕ}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hψ : HasAnalyticSingularitiesOfType (n := n) ψ c 𝔟)
    (hχ : HasAnalyticSingularitiesOfType (n := n) χ c 𝔠)
    (hle : (𝔟.mul (idealPow 𝔞 p)).Le 𝔠) :
    MoreSingularOn (fun y => ψ y + p • φ y) χ univ :=
  moreSingularOn_univ_of_le
    (hasAnalyticSingularitiesOfType_mul hψ (hasAnalyticSingularitiesOfType_pow hφ p))
    hχ hle

end

end Hironaka.IdealWeightPowers
