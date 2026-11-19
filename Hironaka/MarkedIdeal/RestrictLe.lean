import Hironaka.Analytic.IdealPresentation

set_option autoImplicit false

/-!
# Ideal weights compared along a subset: the restriction calculus

Source: Copy-4, Step 1 of `prop:principalization`, equations `eq:Pmov-restriction`
and `eq:PF-restriction`, and Step 4, equation `eq:DL-restriction`
(`transcendental-nakamaye-copy4-20260911`).

`Pending/IdealWeightComparison` compares two ideal weights on a *neighbourhood* of a
point: if `𝔞 ⊆ 𝔟` then `ψ_𝔞 ≤ ψ_𝔟 + O(1)`.  Copy-4 also needs the comparison that
only holds **along a submanifold**: the identity `P^{mov}|_{W_1} = G_M - \frac Mm G_m`
compares two divisors *after restriction to the strict transform*, and it is used
only through the weights, in the form

  `ψ_{P^{mov}} = ψ_{𝔠_M} ∘ f + O(1)`  on `W_1`.

The hypothesis available for it is exactly what
`RelativePrincipalization.exists_relativePrincipalization` produces: the two ideals
have the *same image* in `𝒪_{W'}`, i.e. every germ of the one agrees **on `W'`, near
the point** with a combination of germs of the other.  That is `IsInSpanOnAt`, not
`IsInSpanAt`, so none of `IdealWeightComparison` applies: its `DominatedAt` demands an
inequality on a full neighbourhood, whereas here it is available only on the
subset.

This module supplies the missing layer.  Everything is stated **along a filter**:
`DominatedAlong l g v` and `MoreSingularAlong u v l` specialise to the existing
`DominatedAt`/`MoreSingularAt` at `l = 𝓝 x` and to the new restricted notions at
`l = 𝓝[W] x`, and the whole chain

  span relation ⟹ domination ⟹ comparison of `generatorLog` ⟹ comparison of the
  presented functions

goes through verbatim, because every step of it is a `filter_upwards`.  The one
place where a genuine neighbourhood is still needed is the continuity of the
coefficients produced by the span relation, and there `l ≤ 𝓝 x` is enough.

The conclusion is packaged as `RestrictLe W 𝔞 𝔟` ("`𝔞` restricts into `𝔟` along `W`",
i.e. `Res_W 𝔞 ⊆ Res_W 𝔟`) and, for a **compact** `W`, as a comparison with one
constant on `W` — the `O(1)` of `eq:Pmov-restriction`.  Note that `W` is compact in
every application (it is a closed subset of a compact `Y`), while the ambient
manifold need not be, and that nothing here assumes `W` is a submanifold: the
statements are about the subset only.

Everything here is sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.RestrictedIdealWeight

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
open Hironaka.IdealWeightComparison
open Hironaka.RelativePrincipalizationSpan

/-! ### Domination along a filter -/

section Along

variable {X : Type*} [TopologicalSpace X]

/-- `v` is **dominated along the filter `l`** by the family `g`: `|v|² ≤ B ∑ⱼ|gⱼ|²`
eventually along `l`, for some `B > 0`.  At `l = 𝓝 x` this is
`IdealWeightComparison.DominatedAt`; the case used below is `l = 𝓝[W] x`, where the
inequality is only claimed on `W`. -/
def DominatedAlong {P : ℕ} (l : Filter X) (g : Fin P → X → ℂ) (v : X → ℂ) : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∀ᶠ y in l, ‖v y‖ ^ 2 ≤ B * generatorNormSq g y

/-- Additive comparison of singularities **along a filter**, with one real
constant.  At `l = 𝓝 x` this is `MoreSingularAt`. -/
def MoreSingularAlong (u v : X → EReal) (l : Filter X) : Prop :=
  ∃ C : ℝ, ∀ᶠ y in l, u y ≤ v y + (C : EReal)

theorem moreSingularAt_iff_moreSingularAlong {u v : X → EReal} {x : X} :
    MoreSingularAt u v x ↔ MoreSingularAlong u v (𝓝 x) := Iff.rfl

omit [TopologicalSpace X] in
theorem DominatedAlong.mono {P : ℕ} {l l' : Filter X} {g : Fin P → X → ℂ}
    {v : X → ℂ} (h : DominatedAlong l g v) (hl : l' ≤ l) : DominatedAlong l' g v := by
  obtain ⟨B, hB, hBy⟩ := h
  exact ⟨B, hB, hBy.filter_mono hl⟩

omit [TopologicalSpace X] in
theorem MoreSingularAlong.mono {u v : X → EReal} {l l' : Filter X}
    (h : MoreSingularAlong u v l) (hl : l' ≤ l) : MoreSingularAlong u v l' := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, hC.filter_mono hl⟩

omit [TopologicalSpace X] in
/-- A member of the family is dominated by it, along any filter. -/
theorem dominatedAlong_of_eq {P : ℕ} {l : Filter X} {g : Fin P → X → ℂ} {v : X → ℂ}
    (hv : ∃ j, v = g j) : DominatedAlong l g v := by
  obtain ⟨j, rfl⟩ := hv
  exact ⟨1, one_pos, Eventually.of_forall fun y => by
    simpa using norm_sq_le_generatorNormSq g y j⟩

/-- **Domination along `l` is stable under holomorphic combinations.**  The
coefficients are only required to be continuous at a point `x` with `l ≤ 𝓝 x`, and
the defining identity is only required to hold along `l`. -/
theorem DominatedAlong.sum {P K : ℕ} {l : Filter X} {x : X} (hl : l ≤ 𝓝 x)
    {g : Fin P → X → ℂ} {a s : Fin K → X → ℂ} {v : X → ℂ}
    (ha : ∀ k, ContinuousAt (a k) x) (hs : ∀ k, DominatedAlong l g (s k))
    (heq : ∀ᶠ y in l, v y = ∑ k, a k y * s k y) :
    DominatedAlong l g v := by
  choose B hB hBy using hs
  set A : ℝ := (∑ k, ‖a k x‖ ^ 2) + 1 with hAdef
  have hA : 0 < A := by
    have : (0 : ℝ) ≤ ∑ k, ‖a k x‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hSB : (0 : ℝ) ≤ ∑ k, B k := Finset.sum_nonneg fun k _ => (hB k).le
  have hcont : ContinuousAt (fun y => ∑ k, ‖a k y‖ ^ 2) x :=
    tendsto_finsetSum _ fun k _ => ((ha k).norm).pow 2
  have hAy : ∀ᶠ y in l, (∑ k, ‖a k y‖ ^ 2) ≤ A :=
    ((hcont.eventually_lt continuousAt_const (by rw [hAdef]; exact lt_add_one _)).mono
      fun _ hy => hy.le).filter_mono hl
  have hpos : 0 < A * (∑ k, B k) + 1 := by nlinarith
  refine ⟨A * (∑ k, B k) + 1, hpos, ?_⟩
  have hall : ∀ᶠ y in l, ∀ k, ‖s k y‖ ^ 2 ≤ B k * generatorNormSq g y :=
    eventually_all.mpr hBy
  filter_upwards [heq, hAy, hall] with y hy hyA hyB
  have hQ : (0 : ℝ) ≤ generatorNormSq g y := generatorNormSq_nonneg g y
  have hss : (∑ k, ‖s k y‖ ^ 2) ≤ (∑ k, B k) * generatorNormSq g y := by
    calc (∑ k, ‖s k y‖ ^ 2) ≤ ∑ k, B k * generatorNormSq g y :=
          Finset.sum_le_sum fun k _ => hyB k
      _ = (∑ k, B k) * generatorNormSq g y := by rw [Finset.sum_mul]
  have hssnn : (0 : ℝ) ≤ ∑ k, ‖s k y‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs : ‖v y‖ ^ 2 ≤ (∑ k, ‖a k y‖ ^ 2) * ∑ k, ‖s k y‖ ^ 2 := by
    rw [hy]
    calc ‖∑ k, a k y * s k y‖ ^ 2 ≤ (∑ k, ‖a k y * s k y‖) ^ 2 := by
          gcongr
          exact norm_sum_le _ _
      _ = (∑ k, ‖a k y‖ * ‖s k y‖) ^ 2 := by simp_rw [norm_mul]
      _ ≤ (∑ k, ‖a k y‖ ^ 2) * ∑ k, ‖s k y‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hstep : (∑ k, ‖a k y‖ ^ 2) * (∑ k, ‖s k y‖ ^ 2)
      ≤ A * ((∑ k, B k) * generatorNormSq g y) :=
    mul_le_mul hyA hss hssnn hA.le
  nlinarith

omit [TopologicalSpace X] in
/-- A finite family, each member of which is dominated along `l`, is dominated as a
family. -/
theorem exists_generatorNormSq_le_of_forall_dominatedAlong {Q P : ℕ} {l : Filter X}
    {g : Fin Q → X → ℂ} {h : Fin P → X → ℂ} (hg : ∀ i, DominatedAlong l h (g i)) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ y in l, generatorNormSq g y ≤ B * generatorNormSq h y := by
  choose B hB hBy using hg
  have hsum : (0 : ℝ) ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => (hB i).le
  refine ⟨(∑ i, B i) + 1, by linarith, ?_⟩
  have hall : ∀ᶠ y in l, ∀ i, ‖g i y‖ ^ 2 ≤ B i * generatorNormSq h y :=
    eventually_all.mpr hBy
  filter_upwards [hall] with y hy
  calc generatorNormSq g y = ∑ i, ‖g i y‖ ^ 2 := rfl
    _ ≤ ∑ i, B i * generatorNormSq h y := Finset.sum_le_sum fun i _ => hy i
    _ = (∑ i, B i) * generatorNormSq h y := by rw [Finset.sum_mul]
    _ ≤ ((∑ i, B i) + 1) * generatorNormSq h y := by
      have := generatorNormSq_nonneg h y
      nlinarith

omit [TopologicalSpace X] in
/-- **The comparison of generator weights along `l`**, in its domination form. -/
theorem moreSingularAlong_generatorLog_of_forall_dominatedAlong {Q P : ℕ}
    {l : Filter X} {g : Fin Q → X → ℂ} {h : Fin P → X → ℂ}
    (hg : ∀ i, DominatedAlong l h (g i)) :
    MoreSingularAlong (generatorLog g) (generatorLog h) l := by
  obtain ⟨B, hB, hBy⟩ := exists_generatorNormSq_le_of_forall_dominatedAlong hg
  exact ⟨Real.log B, hBy.mono fun y hy => generatorLog_le_add_of_generatorNormSq_le hB hy⟩

omit [TopologicalSpace X] in
/-- **Transfer along `l`.**  A comparison of generator weights becomes a comparison
of the functions they present, absorbing both bounded remainders into the constant.
This is `IdealWeightComparison.moreSingularAt_of_moreSingularAt_generatorLog` with
`𝓝 x` replaced by an arbitrary filter. -/
theorem moreSingularAlong_of_moreSingularAlong_generatorLog {u u' : X → EReal} {c : ℝ}
    (hc : 0 < c) {N P : ℕ} {l : Filter X} {g : Fin N → X → ℂ} {h : Fin P → X → ℂ}
    {R R' : X → ℝ} {C₀ C₀' : ℝ}
    (hueq : ∀ᶠ y in l, u y = (c : EReal) * generatorLog g y + (R y : EReal))
    (hu'eq : ∀ᶠ y in l, u' y = (c : EReal) * generatorLog h y + (R' y : EReal))
    (hRb : ∀ᶠ y in l, R y ≤ C₀) (hR'b : ∀ᶠ y in l, -C₀' ≤ R' y)
    (hlog : MoreSingularAlong (generatorLog g) (generatorLog h) l) :
    MoreSingularAlong u u' l := by
  obtain ⟨D, hD⟩ := hlog
  refine ⟨c * D + C₀ + C₀', ?_⟩
  filter_upwards [hueq, hu'eq, hRb, hR'b, hD] with y hy hy' hyR hyR' hyD
  rw [hy, hy']
  have hscale : (c : EReal) * generatorLog g y
      ≤ (c : EReal) * generatorLog h y + ((c * D : ℝ) : EReal) := by
    calc (c : EReal) * generatorLog g y
        ≤ (c : EReal) * (generatorLog h y + (D : EReal)) :=
          monotone_eReal_const_mul hc.le hyD
      _ = (c : EReal) * generatorLog h y + (c : EReal) * ((D : ℝ) : EReal) :=
          EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc.le)
            (EReal.coe_ne_top _) _ _
      _ = (c : EReal) * generatorLog h y + ((c * D : ℝ) : EReal) := by
          rw [← EReal.coe_mul]
  calc (c : EReal) * generatorLog g y + (R y : EReal)
      ≤ ((c : EReal) * generatorLog h y + ((c * D : ℝ) : EReal)) + (R y : EReal) :=
        add_le_add hscale le_rfl
    _ = (c : EReal) * generatorLog h y + ((c * D + R y : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add]
    _ ≤ (c : EReal) * generatorLog h y
          + ((R' y + (c * D + C₀ + C₀') : ℝ) : EReal) := by
        refine add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)
        linarith
    _ = ((c : EReal) * generatorLog h y + (R' y : EReal))
          + ((c * D + C₀ + C₀' : ℝ) : EReal) := by
        rw [EReal.coe_add, ← add_assoc]

end Along

/-! ### Globalisation over a compact subset -/

section Compact

variable {X : Type*} [TopologicalSpace X]

/-- A germwise comparison **along `W`** with a locally varying constant has, on a
compact `W`, one global constant.  This is the `O(1)` of `eq:Pmov-restriction`:
`W` is compact in every application, while the ambient manifold need not be. -/
theorem moreSingularOn_of_forall_moreSingularAlong_nhdsWithin {u v : X → EReal}
    {W : Set X} (hW : IsCompact W)
    (h : ∀ x ∈ W, MoreSingularAlong u v (𝓝[W] x)) : MoreSingularOn u v W := by
  choose! C hC using h
  have hmem : ∀ x ∈ W, {y | y ∈ W → u y ≤ v y + (C x : EReal)} ∈ 𝓝 x := by
    intro x hx
    exact eventually_nhdsWithin_iff.mp (hC x hx)
  obtain ⟨t, htW, hcov⟩ := hW.elim_nhds_subcover _ hmem
  refine ⟨∑ z ∈ t, |C z|, fun y hy => ?_⟩
  obtain ⟨z, hzt, hzy⟩ := mem_iUnion₂.mp (hcov hy)
  refine (hzy hy).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_))
  exact (le_abs_self (C z)).trans
    (Finset.single_le_sum (f := fun z => |C z|) (fun _ _ => abs_nonneg _) hzt)

end Compact

/-! ### From a restricted inclusion of ideals to a comparison of weights on `W` -/

section Ideal

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- A germ whose restriction to `W` lies in the span of `h` is dominated by `h`
along `W`.  This is the restricted counterpart of
`IdealWeightComparison.dominatedAt_of_isInSpanAt`, and it is the only place where
`IsInSpanOnAt` is unpacked: the coefficients it produces are holomorphic on a full
neighbourhood — which is what `DominatedAlong.sum` needs — while the identity itself
holds only on `W`. -/
theorem dominatedAlong_nhdsWithin_of_isInSpanOnAt {P : ℕ} {h : Fin P → M → ℂ}
    {v : M → ℂ} {x : M} {W : Set M}
    (hv : IsInSpanOnAt (n := n) W (· ∈ range h) x v) :
    DominatedAlong (𝓝[W] x) h v := by
  obtain ⟨K, s, a, hs, ha, hsum⟩ := hv
  refine DominatedAlong.sum (x := x) nhdsWithin_le_nhds
    (fun k => (ha k).continuousAt)
    (fun k => dominatedAlong_of_eq ((hs k).imp fun _ hj => hj.symm)) ?_
  exact eventually_nhdsWithin_iff.mpr hsum

variable {W : Set M} {𝔞 𝔟 : GermIdeal n M}

/-- **`Res_W 𝔞 ⊆ Res_W 𝔟`.**  At every point of `W`, every germ of `𝔞` agrees on `W`,
near that point, with a holomorphic combination of germs of `𝔟`.  This is the
hypothesis that `lem:relative-principalization`\ref{it:rp-restriction} delivers, and
the only one available for `eq:Pmov-restriction`: no inclusion of the ambient ideals
holds. -/
def RestrictLe (W : Set M) (𝔞 𝔟 : GermIdeal n M) : Prop :=
  ∀ x ∈ W, ∀ g, 𝔞.mem x g → IsInSpanOnAt (n := n) W (𝔟.mem x) x g

/-- **The restricted comparison of ideal weights, at a point of `W`.**  If
`Res_W 𝔞 ⊆ Res_W 𝔟` then a function presenting `𝔞` is more singular than one
presenting `𝔟`, with the same coefficient, *along `W`* near every point of `W`. -/
theorem moreSingularAlong_nhdsWithin_of_restrictLe {φ φ' : M → EReal} {c : ℚ}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hφ' : HasAnalyticSingularitiesOfType (n := n) φ' c 𝔟)
    (hle : RestrictLe W 𝔞 𝔟) {x : M} (hx : x ∈ W) :
    MoreSingularAlong φ φ' (𝓝[W] x) := by
  obtain ⟨hc, -, hpres⟩ := hφ
  obtain ⟨-, -, hpres'⟩ := hφ'
  obtain ⟨U, hU, hxU, N, g, hgdiff, hgiff, R, C₀, hRb, hφeq⟩ := hpres x
  obtain ⟨U', hU', hxU', P, h, hhdiff, hhiff, R', C₀', hR'b, hφ'eq⟩ := hpres' x
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hspan : ∀ i, IsInSpanOnAt (n := n) W (· ∈ range h) x (g i) := by
    intro i
    refine IsInSpanOnAt.trans (S := 𝔟.mem x) ?_
      (hle x hx (g i) (mem_of_isPresentation hU hxU hgdiff hgiff i))
    intro s hs
    exact IsInSpanAt.restrict ((hhiff x hxU' s).mp hs)
  refine moreSingularAlong_of_moreSingularAlong_generatorLog hcR
    ((eventually_of_mem (hU.mem_nhds hxU) fun y hy => hφeq y hy).filter_mono
      nhdsWithin_le_nhds)
    ((eventually_of_mem (hU'.mem_nhds hxU') fun y hy => hφ'eq y hy).filter_mono
      nhdsWithin_le_nhds)
    ((eventually_of_mem (hU.mem_nhds hxU) fun y hy => (abs_le.mp (hRb y hy)).2).filter_mono
      nhdsWithin_le_nhds)
    ((eventually_of_mem (hU'.mem_nhds hxU') fun y hy =>
      (abs_le.mp (hR'b y hy)).1).filter_mono nhdsWithin_le_nhds)
    (moreSingularAlong_generatorLog_of_forall_dominatedAlong
      fun i => dominatedAlong_nhdsWithin_of_isInSpanOnAt (hspan i))

/-- **The restricted comparison of ideal weights, with one constant on `W`.**  This
is the form Copy-4 uses: `ψ_𝔞 ≤ ψ_𝔟 + O(1)` on the strict transform. -/
theorem moreSingularOn_of_restrictLe {φ φ' : M → EReal} {c : ℚ}
    (hW : IsCompact W)
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hφ' : HasAnalyticSingularitiesOfType (n := n) φ' c 𝔟)
    (hle : RestrictLe W 𝔞 𝔟) : MoreSingularOn φ φ' W :=
  moreSingularOn_of_forall_moreSingularAlong_nhdsWithin hW
    fun _ hx => moreSingularAlong_nhdsWithin_of_restrictLe hφ hφ' hle hx

/-- **Two ideals with the same restriction to a compact `W` have weights that agree up
to one constant on `W`.**  This is the comparison behind `eq:Pmov-restriction` and
`eq:PF-restriction`, which the manuscript writes as equalities of divisors
(`P^{mov}|_{W_1}=G_M-\frac MmG_m`, `P^F|_W=F_B`) and then uses only through the weights.
It is NOT either of those equations: neither `G_M`, `G_m` nor `F_B` occurs here. -/
theorem sameSingularityTypeOn_of_restrictLe {φ φ' : M → EReal} {c : ℚ}
    (hW : IsCompact W)
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hφ' : HasAnalyticSingularitiesOfType (n := n) φ' c 𝔟)
    (hle : RestrictLe W 𝔞 𝔟) (hge : RestrictLe W 𝔟 𝔞) :
    SameSingularityTypeOn φ φ' W :=
  ⟨moreSingularOn_of_restrictLe hW hφ hφ' hle,
   moreSingularOn_of_restrictLe hW hφ' hφ hge⟩

end Ideal

end

end Hironaka.RestrictedIdealWeight
