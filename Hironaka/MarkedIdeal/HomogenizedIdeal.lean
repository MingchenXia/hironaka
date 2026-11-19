import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Analytic.HolomorphicTaylorTail

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Homogenized ideals and the analytic glueing inclusion

Hironaka phase H3 (TN23-ENVELOPES, agreed with TN-CLASSICAL on I-0981); blueprint
`mc:homogenized-ideal`, `mc:homogenized-basic`, `mc:coordinate-iterated`, `mc:glueing-inclusion`,
`mc:homogenized-product`, `mc:coordinate-change`, `mc:homogenized-invariance`
(`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005, §2.10 (homogenized ideals,
Lemma `le:hom`, Lemma `le:homo0`), in the analytic adaptation of design note D7 (convergent
coordinate changes and the convergent Taylor tail instead of formal automorphisms).

For a marked ideal `(𝔞, μ)` (with `N = M`), `T(𝔞) = 𝓓^{μ-1}(𝔞)` (`tangentIdeal`) and the
**homogenized ideal** is `𝓗(𝔞) = ∑_{i<μ} 𝓓^i(𝔞) · T(𝔞)^i` (`homogenizedIdeal`, generated stalkwise by
the products of the summands).

* `le_homogenizedIdeal`: `𝔞 ⊆ 𝓗(𝔞)` (`μ ≥ 1`); `homogenizedIdeal_one`: `𝓗(𝔞) = 𝔞` for `μ = 1`
  (`le:hom` (1)).
* `comp_mem_homogenizedIdeal` (**glueing inclusion**, the analytic core of `le:homo0` (1)): let
  `W` be local holomorphic coordinates at `x`, `Ψ` a local inverse of `W ∘ e⁻¹`, `h ∈ T(𝔞)_x` with
  `h(x) = 0`, and `φ(p) = e⁻¹ Ψ(W(p) + h(p) eᵢ)` (the coordinate change replacing the `i`-th
  coordinate `wᵢ` by `wᵢ + h`, e.g. a tangent direction `u` by another one `v = u + h`).  Then
  `f ∘ φ ∈ 𝓗(𝔞)_x` for every `f ∈ 𝔞_x`.  Proof: the convergent Taylor tail
  (`HolomorphicTaylorTail.exists_taylor_tail`) of `F = f ∘ e⁻¹ ∘ Ψ` in the direction `eᵢ` gives
  `f ∘ φ = ∑_{j<μ} (j!)⁻¹ (∂ᵢʲ F)(W) hʲ + h^μ G(W, h)`, with `(∂ᵢʲ F) ∘ W ∈ 𝓓^j(𝔞)`
  (`iterDeriv_comp_mem_iterDerivIdeal`, from `BlowupDerivativeIdeal.exists_coordDeriv_coeff`),
  `hʲ ∈ T(𝔞)^j` and `h^μ = h · h^{μ-1} ∈ 𝓓^{μ-1}(𝔞) · T(𝔞)^{μ-1}`.
* `mul_mem_homogenizedIdeal`: `𝓗(𝓓^i 𝔞, μ - i) · T(𝔞)^i ⊆ 𝓗(𝔞, μ)` for `i < μ`.
* `CoordinateChange` (the data `W, Ψ, h, i` of the coordinate change, `coordMap = φ`) and
  `CoordinateChange.comp_mem_homogenizedIdeal_of_mem` (**`φ^* 𝓗(𝔞) ⊆ 𝓗(𝔞)` at `x`**, Włodarczyk's
  `le:homo0` (1)): from the glueing inclusion for `(𝓓^i 𝔞, μ - i)` (whose tangent ideal is again
  `T(𝔞)`), `φ^* T(𝔞)^j ⊆ T(𝔞)^j` (`comp_mem_idealPow_tangentIdeal`, via `𝓗(T(𝔞), 1) = T(𝔞)`) and
  `mul_mem_homogenizedIdeal`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold Nat

namespace Hironaka.HomogenizedIdeal

open Hironaka.HolomorphicIdealSheaves GermIdealOrder DerivativeIdeal IdealWeightPowers
  BlowupDerivativeIdeal HolomorphicTaylorTail

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Ideal-theoretic helpers -/

section Helpers

variable {x : M}

/-- A coherent ideal is closed under holomorphic combinations of its germs. -/
theorem mem_of_isInSpanAt {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {g : M → ℂ}
    (hg : IsInSpanAt (n := n) (𝔞.mem x) x g) : 𝔞.mem x g := by
  obtain ⟨U, -, hxU, N, s, -, hgen⟩ := h𝔞 x
  exact (hgen x hxU g).mpr
    (RelativePrincipalizationSpan.IsInSpanAt.trans (fun t ht => (hgen x hxU t).mp ht) hg)

/-- Membership in a coherent ideal only depends on the germ. -/
theorem mem_congr {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {g g' : M → ℂ} (hg : 𝔞.mem x g)
    (h : g =ᶠ[𝓝 x] g') : 𝔞.mem x g' :=
  mem_of_isInSpanAt h𝔞 (isInSpanAt_of_eq_mul hg
    ((RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg).congr h)
    (holomorphicAt_const 1) (h.symm.mono fun p hp => by simp [hp]))

/-- A product of germs of `𝔞` and `𝔟` is a germ of `𝔞𝔟`. -/
theorem mul_mem_mul {𝔞 𝔟 : GermIdeal n M} {a b : M → ℂ} (ha : 𝔞.mem x a) (hb : 𝔟.mem x b)
    (hab : HolomorphicAt n (fun p => a p * b p) x) : (𝔞.mul 𝔟).mem x (fun p => a p * b p) := by
  show IsInSpanAt (n := n) (fun s => ∃ a b, 𝔞.mem x a ∧ 𝔟.mem x b ∧ s = a * b) x _
  exact isInSpanAt_of_eq_mul ⟨a, b, ha, hb, rfl⟩ hab (holomorphicAt_const 1)
    (Eventually.of_forall fun p => by simp)

/-- Powers of a germ of `𝔟` are germs of the powers of `𝔟`. -/
theorem pow_mem_idealPow {𝔟 : GermIdeal n M} {b : M → ℂ} (hb : 𝔟.mem x b)
    (hbh : HolomorphicAt n b x) : ∀ j : ℕ, (idealPow 𝔟 j).mem x (fun p => b p ^ j)
  | 0 => by
    show HolomorphicAt n _ x
    simpa using holomorphicAt_const (n := n) (x := x) (1 : ℂ)
  | j + 1 => by
    have := mul_mem_mul (pow_mem_idealPow hb hbh j) hb
      (by simpa only [pow_succ] using (holomorphicAt_pow hbh (j + 1)))
    rw [idealPow_succ]
    simpa only [pow_succ] using this

/-- Membership in `𝓓^j(𝔞)`, `j ≥ 1`, only depends on the germ. -/
theorem iterDerivIdeal_succ_mem_congr {𝔞 : GermIdeal n M} {j : ℕ} {g g' : M → ℂ}
    (hg : (iterDerivIdeal 𝔞 (j + 1)).mem x g) (h : g =ᶠ[𝓝 x] g') :
    (iterDerivIdeal 𝔞 (j + 1)).mem x g' :=
  DerivativeIdeal.isInSpanAt_congr hg h

end Helpers

/-! ### The homogenized ideal -/

/-- `T(𝔞) = 𝓓^{μ-1}(𝔞)` for the marked ideal `(𝔞, μ)`. -/
def tangentIdeal (𝔞 : GermIdeal n M) (μ : ℕ) : GermIdeal n M :=
  iterDerivIdeal 𝔞 (μ - 1)

/-- The generators of `𝓗(𝔞)` at `x`: germs of `𝓓^i(𝔞) · T(𝔞)^i` for `i < μ`. -/
def HomGen (𝔞 : GermIdeal n M) (μ : ℕ) (x : M) (s : M → ℂ) : Prop :=
  ∃ i, i < μ ∧ ((iterDerivIdeal 𝔞 i).mul (idealPow (tangentIdeal 𝔞 μ) i)).mem x s

/-- **The homogenized ideal** `𝓗(𝔞) = ∑_{i<μ} 𝓓^i(𝔞) · T(𝔞)^i` of the marked ideal `(𝔞, μ)`
(Włodarczyk 2005, §2.10). -/
def homogenizedIdeal (𝔞 : GermIdeal n M) (μ : ℕ) : GermIdeal n M where
  mem x := IsInSpanAt (n := n) (HomGen 𝔞 μ x) x

variable {𝔞 : GermIdeal n M}

/-- **`𝔞 ⊆ 𝓗(𝔞)`** for `μ ≥ 1`. -/
theorem le_homogenizedIdeal (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {μ : ℕ}
    (hμ : 1 ≤ μ) : 𝔞.Le (homogenizedIdeal 𝔞 μ) := by
  intro x g hg
  have hgh := h𝔞 x g hg
  refine isInSpanAt_of_eq_mul (s := fun p => g p * 1) ⟨0, hμ, ?_⟩ (h𝔞 x g hg)
    (holomorphicAt_const 1) (Eventually.of_forall fun p => by simp)
  exact mul_mem_mul (b := fun _ => 1) hg (holomorphicAt_const (n := n) (x := x) 1)
    (by simpa using hgh)

/-- **`le:hom` (1)**: for `μ = 1`, `𝓗(𝔞) = 𝔞` (coherent `𝔞`). -/
theorem homogenizedIdeal_one (h𝔞 : 𝔞.IsCoherent) : homogenizedIdeal 𝔞 1 = 𝔞 := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun hg => ?_,
    fun hg => le_homogenizedIdeal hhol le_rfl x g hg⟩)
  refine mem_of_isInSpanAt h𝔞 (hg.mono ?_)
  rintro s ⟨i, hi, hs⟩
  obtain rfl : i = 0 := by omega
  refine mem_of_isInSpanAt h𝔞 ((show IsInSpanAt (n := n) (fun s => ∃ a b,
    (iterDerivIdeal 𝔞 0).mem x a ∧ (idealPow (tangentIdeal 𝔞 1) 0).mem x b ∧ s = a * b) x s
    from hs).mono ?_)
  rintro t ⟨a, b, ha, hb, rfl⟩
  -- `a ∈ 𝔞`, `b` holomorphic: `a * b ∈ 𝔞`
  have hb' : HolomorphicAt n b x := hb
  exact mem_of_isInSpanAt h𝔞 (isInSpanAt_of_eq_mul (s := a) ha ((hhol x a ha).mul hb') hb'
    (Eventually.of_forall fun p => by simp [mul_comm]))

/-! ### Coordinate derivatives of a germ of `𝔞` lie in `𝓓^j(𝔞)` -/

/-- **Iterated coordinate derivatives.**  Let `W` be local holomorphic coordinates at `x` and `F`
holomorphic near `W x` with `F ∘ W ∈ 𝔞_x`.  Then `(∂_v^j F) ∘ W ∈ 𝓓^j(𝔞)_x` for every `j` (for the
basis direction `v = eₗ`). -/
theorem iterDeriv_comp_mem_iterDerivIdeal (h𝔞 : 𝔞.IsCoherent) {x : M} {W : M → ComplexModel n}
    {N : Set (ComplexModel n)} (hN : IsOpen N) (hxN : (complexChartAt (n := n) x).val x ∈ N)
    (hFd : DifferentiableOn ℂ (W ∘ (complexChartAt (n := n) x).val.symm) N)
    (hinj : Function.Injective
      (fderiv ℂ (W ∘ (complexChartAt (n := n) x).val.symm) ((complexChartAt (n := n) x).val x)))
    {F : ComplexModel n → ℂ} (hF : ∀ᶠ w in 𝓝 (W x), DifferentiableAt ℂ F w)
    (hFW : 𝔞.mem x (F ∘ W)) (l : Fin n) :
    ∀ j : ℕ, (iterDerivIdeal 𝔞 j).mem x
      (iterDeriv (List.replicate j (EuclideanSpace.single l (1 : ℂ))) F ∘ W)
  | 0 => hFW
  | j + 1 => by
    obtain ⟨c, hc, hceq⟩ := exists_coordDeriv_coeff hN hxN hFd hinj
    have hhol : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y := fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
    -- `∂^j F` is differentiable near `W x`
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hF
    have hFU : DifferentiableOn ℂ F (Metric.ball (W x) r) := fun z hz =>
      (hball z hz).differentiableWithinAt
    have hdj := differentiableOn_iterDeriv hFU Metric.isOpen_ball
      (List.replicate j (EuclideanSpace.single l (1 : ℂ)))
    have hGev : ∀ᶠ w in 𝓝 (W x), DifferentiableAt ℂ
        (iterDeriv (List.replicate j (EuclideanSpace.single l (1 : ℂ))) F) w := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with w hw
      exact (hdj w hw).differentiableAt (Metric.isOpen_ball.mem_nhds hw)
    have hprev := iterDeriv_comp_mem_iterDerivIdeal h𝔞 hN hxN hFd hinj hF hFW l j
    have hxs : x ∈ (complexChartAt (n := n) x).val.source := mem_complexChartAt_source x
    -- `(∂^{j+1} F) ∘ W = ∑ₘ c l m · ∂^e_m ((∂^j F) ∘ W)` near `x`
    have heq := hceq _ hGev l
    have hmem : (iterDerivIdeal 𝔞 (j + 1)).mem x (fun p => ∑ m, c l m p *
        chartDeriv (complexChartAt (n := n) x) (EuclideanSpace.single m 1)
          (iterDeriv (List.replicate j (EuclideanSpace.single l (1 : ℂ))) F ∘ W) p) := by
      refine RelativePrincipalizationSpan.IsInSpanAt.sum _ fun m _ => ?_
      exact RelativePrincipalizationSpan.IsInSpanAt.mul_left (hc l m)
        (chartDeriv_mem_derivIdeal (holomorphicAt_of_mem_iterDerivIdeal hhol j) hxs hprev)
    refine iterDerivIdeal_succ_mem_congr hmem ?_
    filter_upwards [heq] with p hp
    simp only [Function.comp_apply, List.replicate_succ, iterDeriv, dirDeriv]
    exact hp.symm

/-! ### The glueing inclusion -/

/-- **The glueing inclusion** (the analytic core of Włodarczyk's Lemma `le:homo0` (1); design
note D7).  Let `W` be local holomorphic coordinates at `x` (its reading `W ∘ e⁻¹` in the preferred
chart `e` is holomorphic on an open `N ∋ e x` with injective derivative at `e x`), `Ψ` a holomorphic
local inverse (`Ψ ∘ W = e` near `x`), `h` a germ of `T(𝔞) = 𝓓^{μ-1}(𝔞)` with `h(x) = 0`, and let
`φ(p) = e⁻¹(Ψ(W(p) + h(p) eᵢ))` be the coordinate change that replaces the coordinate `wᵢ` by
`wᵢ + h`.  Then `f ∘ φ ∈ 𝓗(𝔞)_x` for every `f ∈ 𝔞_x`. -/
theorem comp_mem_homogenizedIdeal (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hμ : 1 ≤ μ) {x : M}
    {W : M → ComplexModel n} {N : Set (ComplexModel n)} (hN : IsOpen N)
    (hxN : (complexChartAt (n := n) x).val x ∈ N)
    (hFd : DifferentiableOn ℂ (W ∘ (complexChartAt (n := n) x).val.symm) N)
    (hinj : Function.Injective
      (fderiv ℂ (W ∘ (complexChartAt (n := n) x).val.symm) ((complexChartAt (n := n) x).val x)))
    {Ψ : ComplexModel n → ComplexModel n} (hΨ : ∀ᶠ w in 𝓝 (W x), DifferentiableAt ℂ Ψ w)
    (hΨW : ∀ᶠ p in 𝓝 x, Ψ (W p) = (complexChartAt (n := n) x).val p)
    {h : M → ℂ} (hh : (tangentIdeal 𝔞 μ).mem x h) (hh0 : h x = 0) (i : Fin n)
    {f : M → ℂ} (hf : 𝔞.mem x f) :
    (homogenizedIdeal 𝔞 μ).mem x (fun p =>
      f ((complexChartAt (n := n) x).val.symm (Ψ (W p + h p • EuclideanSpace.single i 1)))) := by
  classical
  set e := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hhol : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hfh : HolomorphicAt n f x := hhol x f hf
  have hhh : HolomorphicAt n h x := holomorphicAt_of_mem_iterDerivIdeal hhol (μ - 1) x h hh
  set v : ComplexModel n := EuclideanSpace.single i 1 with hv
  set F : ComplexModel n → ℂ := fun w => f (e.val.symm (Ψ w)) with hFdef
  -- `W` is continuous at `x`
  have hWc : ContinuousAt W x := by
    have hcomp : ContinuousAt (fun p => (W ∘ e.val.symm) (e.val p)) x :=
      ((hFd _ hxN).differentiableAt (hN.mem_nhds hxN)).continuousAt.comp (e.val.continuousAt hxs)
    refine hcomp.congr ?_
    filter_upwards [e.val.open_source.mem_nhds hxs] with p hp
    simp only [Function.comp_apply, e.val.left_inv hp]
  have hΨx : Ψ (W x) = e.val x := hΨW.self_of_nhds
  -- `F` is holomorphic near `W x`
  have hF : ∀ᶠ w in 𝓝 (W x), DifferentiableAt ℂ F w := by
    have hΨc : ContinuousAt Ψ (W x) := hΨ.self_of_nhds.continuousAt
    rw [ContinuousAt, hΨx] at hΨc
    filter_upwards [hΨ, hΨc.eventually (eventually_differentiableAt_comp_symm e hxs hfh)]
      with w hw1 hw2
    exact hw2.comp w hw1
  -- `F ∘ W = f` near `x`
  have hFW : 𝔞.mem x (F ∘ W) := by
    refine mem_congr h𝔞 hf ?_
    filter_upwards [hΨW, e.val.open_source.mem_nhds hxs] with p hp1 hp2
    simp only [hFdef, Function.comp_apply, hp1, e.val.left_inv hp2]
  -- the convergent Taylor tail of `F` in the direction `v`
  obtain ⟨G, hG, hGeq⟩ := exists_taylor_tail hF v μ
  have hγ : Tendsto (fun p => (W p, h p)) (𝓝 x) (𝓝 (W x, (0 : ℂ))) := by
    rw [← hh0]
    exact hWc.prodMk_nhds hhh.continuousAt
  have hexp := hγ.eventually hGeq
  -- `G (W, h)` is holomorphic at `x`
  have hGγ : HolomorphicAt n (fun p => G (W p, h p)) x := by
    have hhe := eventually_differentiableAt_comp_symm e hxs hhh
    set inner : ComplexModel n → ComplexModel n × ℂ :=
      fun ζ => ((W ∘ e.val.symm) ζ, (h ∘ e.val.symm) ζ) with hinner
    have hinnerd : ∀ᶠ ζ in 𝓝 (e.val x), DifferentiableAt ℂ inner ζ := by
      filter_upwards [hN.mem_nhds hxN, hhe] with ζ hζ1 hζ2
      exact ((hFd ζ hζ1).differentiableAt (hN.mem_nhds hζ1)).prodMk hζ2
    have hinnerx : inner (e.val x) = (W x, 0) := by
      simp only [hinner, Function.comp_apply, e.val.left_inv hxs, hh0]
    have hinnerc : Tendsto inner (𝓝 (e.val x)) (𝓝 (W x, (0 : ℂ))) := by
      rw [← hinnerx]; exact hinnerd.self_of_nhds.continuousAt
    refine (holomorphicAt_comp_chart e (W := G ∘ inner) hxs ?_).congr ?_
    · filter_upwards [hinnerd, hinnerc.eventually hG] with ζ h1 h2
      exact h2.comp ζ h1
    · filter_upwards [e.val.open_source.mem_nhds hxs] with p hp
      simp only [hinner, Function.comp_apply, e.val.left_inv hp]
  -- the generators
  have hA : ∀ j, (iterDerivIdeal 𝔞 j).mem x (iterDeriv (List.replicate j v) F ∘ W) :=
    iterDeriv_comp_mem_iterDerivIdeal h𝔞 hN hxN hFd hinj hF hFW i
  have hAh : ∀ j, HolomorphicAt n (iterDeriv (List.replicate j v) F ∘ W) x := fun j =>
    holomorphicAt_of_mem_iterDerivIdeal hhol j x _ (hA j)
  have hgen_j : ∀ j ∈ Finset.range μ, HomGen 𝔞 μ x
      (fun p => (iterDeriv (List.replicate j v) F ∘ W) p * h p ^ j) := fun j hj =>
    ⟨j, Finset.mem_range.mp hj, mul_mem_mul (hA j) (pow_mem_idealPow hh hhh j)
      ((hAh j).mul (holomorphicAt_pow hhh j))⟩
  have hgen_tail : HomGen 𝔞 μ x (fun p => h p * h p ^ (μ - 1)) :=
    ⟨μ - 1, by omega, mul_mem_mul hh (pow_mem_idealPow hh hhh (μ - 1))
      (hhh.mul (holomorphicAt_pow hhh (μ - 1)))⟩
  have hspan : IsInSpanAt (n := n) (HomGen 𝔞 μ x) x (fun p =>
      ∑ j ∈ Finset.range μ, (j ! : ℂ)⁻¹ * ((iterDeriv (List.replicate j v) F ∘ W) p * h p ^ j) +
        G (W p, h p) * (h p * h p ^ (μ - 1))) := by
    refine RelativePrincipalizationSpan.IsInSpanAt.add
      (RelativePrincipalizationSpan.IsInSpanAt.sum _ fun j hj => ?_) ?_
    · exact isInSpanAt_of_eq_mul (hgen_j j hj)
        ((holomorphicAt_const _).mul ((hAh j).mul (holomorphicAt_pow hhh j)))
        (holomorphicAt_const _) (Eventually.of_forall fun p => rfl)
    · exact isInSpanAt_of_eq_mul hgen_tail
        (hGγ.mul (hhh.mul (holomorphicAt_pow hhh (μ - 1)))) hGγ
        (Eventually.of_forall fun p => rfl)
  refine DerivativeIdeal.isInSpanAt_congr hspan ?_
  filter_upwards [hexp] with p hp
  have hp' : f (e.val.symm (Ψ (W p + h p • v))) =
      ∑ j ∈ Finset.range μ, (j ! : ℂ)⁻¹ * iterDeriv (List.replicate j v) F (W p) * h p ^ j +
        h p ^ μ * G (W p, h p) := hp
  have hpow : h p ^ μ = h p * h p ^ (μ - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hp', hpow]
  simp only [Function.comp_apply]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by ring
  · ring

/-! ### Products with powers of the tangent ideal -/

/-- `𝓗(𝓓^i 𝔞, μ - i) · T(𝔞)^i ⊆ 𝓗(𝔞, μ)` (germs at `x`), for `i < μ`. -/
theorem mul_mem_homogenizedIdeal {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {x : M} {μ i : ℕ}
    (hi : i < μ)
    {a b : M → ℂ} (ha : (homogenizedIdeal (iterDerivIdeal 𝔞 i) (μ - i)).mem x a)
    (hb : (idealPow (tangentIdeal 𝔞 μ) i).mem x b) :
    (homogenizedIdeal 𝔞 μ).mem x (fun p => a p * b p) := by
  have hhol : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hThol : ∀ y g, (tangentIdeal 𝔞 μ).mem y g → HolomorphicAt n g y :=
    holomorphicAt_of_mem_iterDerivIdeal hhol (μ - 1)
  have hbh : HolomorphicAt n b x := holomorphicAt_of_mem_idealPow hb
  have hTT : tangentIdeal (iterDerivIdeal 𝔞 i) (μ - i) = tangentIdeal 𝔞 μ := by
    simp only [tangentIdeal]
    rw [MaximalContact.iterDerivIdeal_iterDerivIdeal]
    congr 1; omega
  obtain ⟨hah, N, s, c, hs, hc, hsum⟩ := ha
  -- each generator `s k ∈ 𝓓^j(𝓓^i 𝔞) · T^j` times `b ∈ T^i` lies in `𝓗(𝔞)`
  have hstep : ∀ k, IsInSpanAt (n := n) (HomGen 𝔞 μ x) x (fun p => s k p * b p) := by
    intro k
    obtain ⟨j, hj, hsk⟩ := hs k
    rw [hTT] at hsk
    obtain ⟨hskh, K, t, d', ht, hd', htsum⟩ := (show IsInSpanAt (n := n) (fun t => ∃ a' b',
      (iterDerivIdeal (iterDerivIdeal 𝔞 i) j).mem x a' ∧
      (idealPow (tangentIdeal 𝔞 μ) j).mem x b' ∧ t = a' * b') x (s k) from hsk)
    have hgen : ∀ l, IsInSpanAt (n := n) (HomGen 𝔞 μ x) x (fun p => d' l p * (t l p * b p)) := by
      intro l
      obtain ⟨a', b', ha', hb', hteq⟩ := ht l
      rw [MaximalContact.iterDerivIdeal_iterDerivIdeal] at ha'
      have ha'h : HolomorphicAt n a' x := holomorphicAt_of_mem_iterDerivIdeal hhol (i + j) x a' ha'
      have hb'h : HolomorphicAt n b' x := holomorphicAt_of_mem_idealPow hb'
      have hbb : (idealPow (tangentIdeal 𝔞 μ) (i + j)).mem x (fun p => b' p * b p) := by
        have := mul_mem_idealPow_add hThol hb' hb
        rwa [Nat.add_comm j i] at this
      have hg : HomGen 𝔞 μ x (fun p => a' p * (b' p * b p)) :=
        ⟨i + j, by omega, mul_mem_mul ha' hbb (ha'h.mul (hb'h.mul hbh))⟩
      refine isInSpanAt_of_eq_mul hg ((hd' l).mul ((ha'h.mul hb'h).mul hbh |>.congr
        (Eventually.of_forall fun p => by simp only [hteq, Pi.mul_apply]))) (hd' l)
        (Eventually.of_forall fun p => ?_)
      simp only [hteq, Pi.mul_apply]; ring
    refine DerivativeIdeal.isInSpanAt_congr
      (RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun l _ => hgen l) ?_
    filter_upwards [htsum] with p hp
    simp only [hp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  refine DerivativeIdeal.isInSpanAt_congr (RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ
    fun k _ => RelativePrincipalizationSpan.IsInSpanAt.mul_left (hc k) (hstep k)) ?_
  filter_upwards [hsum] with p hp
  simp only [hp, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### The coordinate change preserves the homogenized ideal -/

/-- **Data of a coordinate change** at `x` (Włodarczyk's `φ_{uv}`, analytic form): local holomorphic
coordinates `W` at `x` with a holomorphic local inverse `Ψ`, a holomorphic `h` with `h(x) = 0`, and
an index `i`; `coordMap(p) = e⁻¹ Ψ(W(p) + h(p) eᵢ)` replaces the coordinate `Wᵢ` by `Wᵢ + h`. -/
structure CoordinateChange (x : M) where
  W : M → ComplexModel n
  N : Set (ComplexModel n)
  isOpen : IsOpen N
  mem : (complexChartAt (n := n) x).val x ∈ N
  differentiableOn : DifferentiableOn ℂ (W ∘ (complexChartAt (n := n) x).val.symm) N
  injective : Function.Injective
    (fderiv ℂ (W ∘ (complexChartAt (n := n) x).val.symm) ((complexChartAt (n := n) x).val x))
  Ψ : ComplexModel n → ComplexModel n
  differentiableAt : ∀ᶠ w in 𝓝 (W x), DifferentiableAt ℂ Ψ w
  left_inv : ∀ᶠ p in 𝓝 x, Ψ (W p) = (complexChartAt (n := n) x).val p
  h : M → ℂ
  holomorphicAt : HolomorphicAt n h x
  h_zero : h x = 0
  i : Fin n

namespace CoordinateChange

variable {x : M} (d : CoordinateChange (n := n) x)

/-- The coordinate change `φ(p) = e⁻¹ Ψ(W(p) + h(p) eᵢ)`. -/
def coordMap : M → M := fun p =>
  (complexChartAt (n := n) x).val.symm (d.Ψ (d.W p + d.h p • EuclideanSpace.single d.i 1))

theorem continuousAt_W : ContinuousAt d.W x := by
  have hxs : x ∈ (complexChartAt (n := n) x).val.source := mem_complexChartAt_source x
  have hcomp : ContinuousAt (fun p => (d.W ∘ (complexChartAt (n := n) x).val.symm)
      ((complexChartAt (n := n) x).val p)) x :=
    ((d.differentiableOn _ d.mem).differentiableAt (d.isOpen.mem_nhds d.mem)).continuousAt.comp
      ((complexChartAt (n := n) x).val.continuousAt hxs)
  refine hcomp.congr ?_
  filter_upwards [(complexChartAt (n := n) x).val.open_source.mem_nhds hxs] with p hp
  simp only [Function.comp_apply, (complexChartAt (n := n) x).val.left_inv hp]

theorem coordMap_self : d.coordMap x = x := by
  simp only [coordMap, d.h_zero, zero_smul, add_zero, d.left_inv.self_of_nhds]
  exact (complexChartAt (n := n) x).val.left_inv (mem_complexChartAt_source x)

/-- In the chart at `x`, `φ` is `e⁻¹ ∘ H` for a map `H` holomorphic near `e x` with `H (e x) = e x`. -/
theorem exists_chart_form : ∃ H : ComplexModel n → ComplexModel n,
    (∀ᶠ ζ in 𝓝 ((complexChartAt (n := n) x).val x), DifferentiableAt ℂ H ζ) ∧
    H ((complexChartAt (n := n) x).val x) = (complexChartAt (n := n) x).val x ∧
    ∀ᶠ p in 𝓝 x, d.coordMap p = (complexChartAt (n := n) x).val.symm
      (H ((complexChartAt (n := n) x).val p)) := by
  set e := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  set v : ComplexModel n := EuclideanSpace.single d.i 1
  set inner : ComplexModel n → ComplexModel n :=
    fun ζ => (d.W ∘ e.val.symm) ζ + (d.h ∘ e.val.symm) ζ • v with hinner
  have hhe := eventually_differentiableAt_comp_symm e hxs d.holomorphicAt
  have hinnerd : ∀ᶠ ζ in 𝓝 (e.val x), DifferentiableAt ℂ inner ζ := by
    filter_upwards [d.isOpen.mem_nhds d.mem, hhe] with ζ h1 h2
    exact ((d.differentiableOn ζ h1).differentiableAt (d.isOpen.mem_nhds h1)).add (h2.smul_const v)
  have hinnerx : inner (e.val x) = d.W x := by
    simp only [hinner, Function.comp_apply, e.val.left_inv hxs, d.h_zero, zero_smul, add_zero]
  have hinnerc : Tendsto inner (𝓝 (e.val x)) (𝓝 (d.W x)) := by
    rw [← hinnerx]; exact hinnerd.self_of_nhds.continuousAt
  refine ⟨d.Ψ ∘ inner, ?_, ?_, ?_⟩
  · filter_upwards [hinnerd, hinnerc.eventually d.differentiableAt] with ζ h1 h2
    exact h2.comp ζ h1
  · simp only [Function.comp_apply, hinnerx, d.left_inv.self_of_nhds]
    try rfl
  · filter_upwards [e.val.open_source.mem_nhds hxs] with p hp
    simp only [coordMap, hinner, Function.comp_apply, e.val.left_inv hp]
    try rfl

theorem continuousAt_coordMap : ContinuousAt d.coordMap x := by
  obtain ⟨H, hH, hHx, hφ⟩ := d.exists_chart_form
  have hxs : x ∈ (complexChartAt (n := n) x).val.source := mem_complexChartAt_source x
  have h1 : ContinuousAt (fun p => (complexChartAt (n := n) x).val.symm
      (H ((complexChartAt (n := n) x).val p))) x := by
    refine ContinuousAt.comp ?_ (hH.self_of_nhds.continuousAt.comp
      ((complexChartAt (n := n) x).val.continuousAt hxs))
    rw [hHx]
    exact (complexChartAt (n := n) x).val.continuousAt_symm
      ((complexChartAt (n := n) x).val.map_source hxs)
  exact h1.congr (hφ.mono fun p hp => hp.symm)

/-- Pullback along `φ` preserves holomorphy at `x`. -/
theorem holomorphicAt_comp {c : M → ℂ} (hc : HolomorphicAt n c x) :
    HolomorphicAt n (fun p => c (d.coordMap p)) x := by
  obtain ⟨H, hH, hHx, hφ⟩ := d.exists_chart_form
  set e := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hce := eventually_differentiableAt_comp_symm e hxs hc
  have hHc : Tendsto H (𝓝 (e.val x)) (𝓝 (e.val x)) := by
    have := hH.self_of_nhds.continuousAt
    rwa [ContinuousAt, hHx] at this
  refine (holomorphicAt_comp_chart e (W := (c ∘ e.val.symm) ∘ H) hxs ?_).congr ?_
  · filter_upwards [hH, hHc.eventually hce] with ζ h1 h2
    exact h2.comp ζ h1
  · filter_upwards [hφ] with p hp
    simp only [Function.comp_apply, hp]

/-- Pullback along `φ` respects germs at `x`. -/
theorem comp_eventuallyEq {g g' : M → ℂ} (hg : g =ᶠ[𝓝 x] g') :
    (fun p => g (d.coordMap p)) =ᶠ[𝓝 x] fun p => g' (d.coordMap p) := by
  have := d.continuousAt_coordMap
  rw [ContinuousAt, d.coordMap_self] at this
  exact this.eventually hg

/-- Pullback along `φ` of a holomorphic combination. -/
theorem comp_isInSpanAt {S T : (M → ℂ) → Prop} {g : M → ℂ} (hg : IsInSpanAt (n := n) S x g)
    (hST : ∀ s, S s → IsInSpanAt (n := n) T x (fun p => s (d.coordMap p))) :
    IsInSpanAt (n := n) T x (fun p => g (d.coordMap p)) := by
  obtain ⟨hgh, N, s, a, hs, ha, hsum⟩ := hg
  have hsum' := d.comp_eventuallyEq hsum
  refine DerivativeIdeal.isInSpanAt_congr ?_ hsum'.symm
  refine RelativePrincipalizationSpan.IsInSpanAt.sum _ fun k _ => ?_
  exact RelativePrincipalizationSpan.IsInSpanAt.mul_left (d.holomorphicAt_comp (ha k)) (hST _ (hs k))

/-- The glueing inclusion for the data `d`: `φ^* 𝔞 ⊆ 𝓗(𝔞)` at `x`. -/
theorem comp_mem_homogenizedIdeal' {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hμ : 1 ≤ μ)
    (hh : (tangentIdeal 𝔞 μ).mem x d.h) {f : M → ℂ} (hf : 𝔞.mem x f) :
    (homogenizedIdeal 𝔞 μ).mem x (fun p => f (d.coordMap p)) :=
  comp_mem_homogenizedIdeal h𝔞 hμ d.isOpen d.mem d.differentiableOn d.injective d.differentiableAt
    d.left_inv hh d.h_zero d.i hf

/-- **`T(𝔞)^j` is preserved by `φ`** (Włodarczyk: `φ^*(T(𝔞), 1) ⊆ 𝓗(T(𝔞), 1) = (T(𝔞), 1)`). -/
theorem comp_mem_idealPow_tangentIdeal {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ}
    (hh : (tangentIdeal 𝔞 μ).mem x d.h) :
    ∀ j {b : M → ℂ}, (idealPow (tangentIdeal 𝔞 μ) j).mem x b →
      (idealPow (tangentIdeal 𝔞 μ) j).mem x (fun p => b (d.coordMap p))
  | 0, b, hb => d.holomorphicAt_comp hb
  | j + 1, b, hb => by
    have hT : (tangentIdeal 𝔞 μ).IsCoherent := isCoherent_iterDerivIdeal h𝔞 (μ - 1)
    have hThol : ∀ y g, (tangentIdeal 𝔞 μ).mem y g → HolomorphicAt n g y := fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hT hg
    have hT1 : (tangentIdeal (tangentIdeal 𝔞 μ) 1).mem x d.h := hh
    rw [idealPow_succ] at hb ⊢
    show IsInSpanAt (n := n) (fun s => ∃ a b, (idealPow (tangentIdeal 𝔞 μ) j).mem x a ∧
      (tangentIdeal 𝔞 μ).mem x b ∧ s = a * b) x _
    refine d.comp_isInSpanAt (S := fun s => ∃ a b, (idealPow (tangentIdeal 𝔞 μ) j).mem x a ∧
      (tangentIdeal 𝔞 μ).mem x b ∧ s = a * b) hb ?_
    rintro s ⟨a, t, ha, ht, rfl⟩
    have ha' := comp_mem_idealPow_tangentIdeal h𝔞 hh j ha
    have ht' : (tangentIdeal 𝔞 μ).mem x (fun p => t (d.coordMap p)) := by
      have := d.comp_mem_homogenizedIdeal' hT le_rfl hT1 ht
      rwa [homogenizedIdeal_one hT] at this
    exact mul_mem_mul ha' ht' ((holomorphicAt_of_mem_idealPow ha').mul (hThol x _ ht'))

/-- **The coordinate change preserves the homogenized ideal** (Włodarczyk, Lemma `le:homo0` (1),
inclusion `φ^* 𝓗(𝔞) ⊆ 𝓗(𝔞)`, analytic form): if `h ∈ T(𝔞)_x`, then `f ∘ φ ∈ 𝓗(𝔞)_x` for every
`f ∈ 𝓗(𝔞)_x`. -/
theorem comp_mem_homogenizedIdeal_of_mem {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ}
    (hμ : 1 ≤ μ) (hh : (tangentIdeal 𝔞 μ).mem x d.h) {f : M → ℂ}
    (hf : (homogenizedIdeal 𝔞 μ).mem x f) :
    (homogenizedIdeal 𝔞 μ).mem x (fun p => f (d.coordMap p)) := by
  have hhol : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  refine d.comp_isInSpanAt (S := HomGen 𝔞 μ x) hf ?_
  rintro s ⟨i, hi, hs⟩
  refine d.comp_isInSpanAt (S := fun t => ∃ a b, (iterDerivIdeal 𝔞 i).mem x a ∧
    (idealPow (tangentIdeal 𝔞 μ) i).mem x b ∧ t = a * b) hs ?_
  rintro t ⟨a, b, ha, hb, rfl⟩
  have hTT : tangentIdeal (iterDerivIdeal 𝔞 i) (μ - i) = tangentIdeal 𝔞 μ := by
    simp only [tangentIdeal]
    rw [MaximalContact.iterDerivIdeal_iterDerivIdeal]
    congr 1; omega
  have hh' : (tangentIdeal (iterDerivIdeal 𝔞 i) (μ - i)).mem x d.h := by rw [hTT]; exact hh
  have ha' := d.comp_mem_homogenizedIdeal' (isCoherent_iterDerivIdeal h𝔞 i) (by omega) hh' ha
  have hb' := d.comp_mem_idealPow_tangentIdeal h𝔞 hh i hb
  exact mul_mem_homogenizedIdeal h𝔞 hi ha' hb'

end CoordinateChange

end

end Hironaka.HomogenizedIdeal
