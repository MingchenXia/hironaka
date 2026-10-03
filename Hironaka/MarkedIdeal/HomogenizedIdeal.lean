/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Analytic.HolomorphicTaylorTail
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Homogenized ideals and the analytic glueing inclusion

Source: Włodarczyk 2005, §2.10 (homogenized ideals, Lemma `le:hom`, Lemma `le:homo0`).

For a marked ideal `(𝔞, μ)` (with `N = M`), `T(𝔞) = 𝓓^{μ-1}(𝔞)` (`tangentIdeal`) and the
**homogenized ideal** is `𝓗(𝔞) = ∑_{i<μ} 𝓓^i(𝔞) · T(𝔞)^i` (`homogenizedIdeal`, generated stalkwise by
the products of the summands).

* `le_homogenizedIdeal`: `𝔞 ⊆ 𝓗(𝔞)` (`μ ≥ 1`); `homogenizedIdeal_one`: `𝓗(𝔞) = 𝔞` for `μ = 1`
  (`le:hom` (1)).
* Proof: the convergent Taylor tail (`HolomorphicTaylorTail.exists_taylor_tail`) of `F = f ∘ e⁻¹ ∘ Ψ` in the
  direction `eᵢ` gives `f ∘ φ = ∑_{j<μ} (j!)⁻¹ (∂ᵢʲ F)(W) hʲ + h^μ G(W, h)`, with `(∂ᵢʲ F) ∘ W ∈ 𝓓^j(𝔞)` (from
  `BlowupDerivativeIdeal.exists_coordDeriv_coeff`), `hʲ ∈ T(𝔞)^j` and `h^μ = h · h^{μ-1} ∈ 𝓓^{μ-1}(𝔞) · T(𝔞)^{μ-1}`.
-/

open Set Filter
open scoped Topology Manifold Nat

namespace Hironaka.HomogenizedIdeal

open Hironaka.HolomorphicIdealSheaves GermIdealOrder DerivativeIdeal IdealWeightPowers BlowupDerivativeIdeal HolomorphicTaylorTail

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

end CoordinateChange

end

end Hironaka.HomogenizedIdeal
