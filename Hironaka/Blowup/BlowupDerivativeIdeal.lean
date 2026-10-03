/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Blowup.BlowupFibreDirection
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Manifold.LocalHolomorphicInverse
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Manifold.HolomorphicContDiff
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Derivative ideals under a blowup (Giraud, Villamayor)

Source: Włodarczyk 2005, §2.6, Lemma `le:inclusions` and the lemma after the definition of maximal order
(Villamayor); Bierstone--Milman 2008, Lemmas 3.1--3.3.

Let `π : Y → X` be a blowup along `C` with exceptional divisor `D` (ideal `𝒪_Y(-D) = π^*𝓘_C`),
`𝔞` a coherent ideal, and `σ^c(𝔞, μ) = (π^*𝔞 : 𝒪_Y(-μD))` the controlled transform
(`BlowupControlledTransform.controlledTransform`).  Everything is for marked ideals with `N = M`.

## Main results

## Method (analytic form of the source's `y σ^*(Der)`)

At a point `z` of `Y` over `x = π z`:

* if `x ∈ C`, take flattening coordinates `Φ ∘ e_x` of `C` at `x`, a monomial chart `j` and its local inverse `W`
  (`BlowupLocalSurjectivity.exists_monomialLocalInverse`), so that `σⱼ ∘ W = Φ ∘ e_x ∘ π` near `z`; then `y = Wⱼ`
  generates `π^*𝓘_C` near `z`;
* if `x ∉ C`, take `W = e_x ∘ π` (a local biholomorphism) and `y = 1`.

In both cases `W` is a local holomorphic coordinate system at `z`, so the coordinate derivatives `(∂ₗ G) ∘ W` are
holomorphic combinations of chart derivatives (`exists_coordDeriv_coeff`), and `y · (∂ f) ∘ π = D'(f ∘ π)` for a
derivation `D'` with `D'(y) ∈ (y)` (`mul_fderiv_monomial`). The algebra of the source, `D'(y^{μ+1} h) ∈ y^{μ+1}
𝓓(h)` and cancellation of `y^{μ+1}`, then gives the inclusion.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupDerivativeIdeal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences Hironaka.HolomorphicMaps GermIdealOrder DerivativeIdeal IdealWeightPowers InvertibleIdealQuotient BlowupExceptionalDivisor BlowupControlledTransform

noncomputable section

/-! ### Derivatives lower powers of an ideal by one -/

section Powers

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

variable {𝔟 : GermIdeal n M} {x : M} {e : ComplexChart n M} {v : ComplexModel n}

theorem memPow_of_eq' {k : ℕ} {t t' : M → ℂ} (h : (idealPow 𝔟 k).mem x t)
    (heq : t = t') : (idealPow 𝔟 k).mem x t' :=
  heq ▸ h

theorem memPow_add' {k : ℕ} {t t' : M → ℂ} (h : (idealPow 𝔟 (k + 1)).mem x t)
    (h' : (idealPow 𝔟 (k + 1)).mem x t') :
    (idealPow 𝔟 (k + 1)).mem x (fun p => t p + t' p) :=
  mem_idealPow_succ_iff.mpr (RelativePrincipalizationSpan.IsInSpanAt.add
    (mem_idealPow_succ_iff.mp h) (mem_idealPow_succ_iff.mp h'))

theorem memPow_sum' {k K : ℕ} {t : Fin K → M → ℂ}
    (h : ∀ i, (idealPow 𝔟 (k + 1)).mem x (t i)) :
    (idealPow 𝔟 (k + 1)).mem x (fun p => ∑ i, t i p) :=
  mem_idealPow_succ_iff.mpr (RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ
    fun i _ => mem_idealPow_succ_iff.mp (h i))

theorem memPow_congr' {k : ℕ} {t t' : M → ℂ} (h : (idealPow 𝔟 (k + 1)).mem x t)
    (heq : t =ᶠ[𝓝 x] t') : (idealPow 𝔟 (k + 1)).mem x t' :=
  mem_idealPow_succ_iff.mpr (isInSpanAt_congr (mem_idealPow_succ_iff.mp h) heq)

theorem mem_idealPow_one_of_mem {b : M → ℂ} (h𝔟 : ∀ y g, 𝔟.mem y g → HolomorphicAt n g y)
    (hb : 𝔟.mem x b) : (idealPow 𝔟 1).mem x b :=
  mem_idealPow_succ_iff.mpr (isInSpanAt_of_eq_mul (s := (fun _ => (1 : ℂ)) * b)
    (a := fun _ => (1 : ℂ)) ⟨fun _ => (1 : ℂ), b, holomorphicAt_const 1, hb, rfl⟩ (h𝔟 x b hb)
    (holomorphicAt_const 1) (Eventually.of_forall fun z => by simp))

/-- **Derivatives lower the power of an ideal by at most one**: a partial derivative (in any
chart) of a germ of `𝔟^{q+1}` is a germ of `𝔟^q`, for any ideal `𝔟` of holomorphic germs.  (The
generic form of `DerivativeIdeal.chartDeriv_mem_idealPow`, whose proof it follows.) -/
theorem chartDeriv_mem_idealPow' (h𝔟 : ∀ y g, 𝔟.mem y g → HolomorphicAt n g y)
    (hx : x ∈ e.val.source) :
    ∀ (q : ℕ) (g : M → ℂ), (idealPow 𝔟 (q + 1)).mem x g →
      (idealPow 𝔟 q).mem x (chartDeriv e v g)
  | 0, g, hg => holomorphicAt_chartDeriv hx (holomorphicAt_of_mem_idealPow hg)
  | q + 1, g, hg => by
    obtain ⟨-, K, r, c, hr, hc, hsum⟩ := mem_idealPow_succ_iff.mp hg
    choose a b ha hb hab using hr
    have hahol : ∀ k, HolomorphicAt n (a k) x := fun k => holomorphicAt_of_mem_idealPow (ha k)
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
    have hexp : (fun p => ∑ k, (chartDeriv e v (c k) p * r k p +
        (c k p * (chartDeriv e v (a k) p * b k p) + c k p * (a k p * chartDeriv e v (b k) p))))
        =ᶠ[𝓝 x] chartDeriv e v g := by
      filter_upwards [hprod, eventually_all.2 hab'] with p hp hp'
      rw [hp]
      exact Finset.sum_congr rfl fun k _ => by rw [hp' k]; ring
    refine memPow_congr' (memPow_sum' fun k => memPow_add' ?_ (memPow_add' ?_ ?_)) hexp
    · exact memPow_of_eq' (mul_mem_idealPow ((holomorphicAt_chartDeriv hx (hc k)).mul (hbhol k))
        (ha k)) (by funext p; rw [hab k]; simp only [Pi.mul_apply]; ring)
    · have h2 := mul_mem_idealPow_add (q := 1) h𝔟 (chartDeriv_mem_idealPow' h𝔟 hx q (a k) (ha k))
        (mem_idealPow_one_of_mem h𝔟 (hb k))
      exact memPow_of_eq' (mul_mem_idealPow (hc k) h2) (by funext p; ring)
    · exact memPow_of_eq' (mul_mem_idealPow ((hc k).mul (holomorphicAt_chartDeriv hx (hbhol k)))
        (ha k)) (by funext p; ring)

end Powers

/-! ### Powers of a locally principal ideal -/

section Principal

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Powers of holomorphic germs are holomorphic. -/
theorem holomorphicAt_pow {f : M → ℂ} {x : M} (hf : HolomorphicAt n f x) :
    ∀ q : ℕ, HolomorphicAt n (fun p => f p ^ q) x
  | 0 => by simpa using holomorphicAt_const (n := n) (x := x) (1 : ℂ)
  | q + 1 => by
    simpa only [pow_succ] using (holomorphicAt_pow hf q).mul hf

/-- If `𝔩` is generated by `y` at every point of the open set `U`, then `𝔩^q` is generated by
`y^q` there. -/
theorem idealPow_mem_iff_of_generator {𝔩 : GermIdeal n M} {U : Set M} {y : M → ℂ}
    (hy : ∀ z ∈ U, HolomorphicAt n y z)
    (hgen : ∀ z ∈ U, ∀ g, 𝔩.mem z g ↔ IsInSpanAt (n := n) (· = y) z g) :
    ∀ (q : ℕ), ∀ z ∈ U, ∀ g, (idealPow 𝔩 q).mem z g ↔
      IsInSpanAt (n := n) (· = fun p => y p ^ q) z g
  | 0, z, hz, g => by
    simp only [idealPow_zero, pow_zero]
    constructor
    · intro hg
      exact isInSpanAt_of_eq_mul rfl hg hg (Eventually.of_forall fun p => by simp)
    · exact fun hg => hg.holomorphicAt
  | q + 1, z, hz, g => by
    rw [mem_idealPow_succ_iff]
    constructor
    · intro hg
      refine IsInSpanAt.of_forall_eq_mul ?_ hg
      rintro s ⟨a, b, ha, hb, rfl⟩
      obtain ⟨-, c, hc, hac⟩ := isInSpanAt_eq_iff.mp
        ((idealPow_mem_iff_of_generator hy hgen q z hz a).mp ha)
      obtain ⟨-, d, hd, hbd⟩ := isInSpanAt_eq_iff.mp ((hgen z hz b).mp hb)
      refine ⟨fun p => c p * d p, hc.mul hd, ?_⟩
      filter_upwards [hac, hbd] with p hp1 hp2
      simp only [Pi.mul_apply, hp1, hp2, pow_succ]
      ring
    · intro hg
      obtain ⟨hgh, c, hc, hgc⟩ := isInSpanAt_eq_iff.mp hg
      have hyq : (idealPow 𝔩 q).mem z (fun p => y p ^ q) :=
        (idealPow_mem_iff_of_generator hy hgen q z hz _).mpr
          (isInSpanAt_of_eq_mul rfl (holomorphicAt_pow (hy z hz) q) (holomorphicAt_const 1)
            (Eventually.of_forall fun p => by simp))
      have hy1 : 𝔩.mem z y := (hgen z hz y).mpr
        (isInSpanAt_of_eq_mul rfl (hy z hz) (holomorphicAt_const 1)
          (Eventually.of_forall fun p => by simp))
      refine isInSpanAt_of_eq_mul ⟨fun p => y p ^ q, y, hyq, hy1, rfl⟩ hgh hc ?_
      filter_upwards [hgc] with p hp
      simp only [hp, Pi.mul_apply, pow_succ]

end Principal

/-! ### Derivatives in a local holomorphic coordinate system -/

section Coordinates

variable {n : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **Coordinate derivatives are holomorphic combinations of chart derivatives.**  Let `W` be a
local holomorphic coordinate system at `z` (its reading `W ∘ e⁻¹` in the preferred chart `e` at `z`
is holomorphic near `e z` with injective derivative there).  There are functions `c l m`,
holomorphic at `z`, such that for every `G` holomorphic near `W z`, near `z`
`(∂ₗ G) ∘ W = ∑ₘ c l m · ∂^e_{eₘ} (G ∘ W)`. -/
theorem exists_coordDeriv_coeff {z : Z} {W : Z → ComplexModel n} {N : Set (ComplexModel n)}
    (hN : IsOpen N) (hzN : (complexChartAt (n := n) z).val z ∈ N)
    (hFd : DifferentiableOn ℂ (W ∘ (complexChartAt (n := n) z).val.symm) N)
    (hinj : Function.Injective
      (fderiv ℂ (W ∘ (complexChartAt (n := n) z).val.symm) ((complexChartAt (n := n) z).val z))) :
    ∃ c : Fin n → Fin n → Z → ℂ, (∀ l m, HolomorphicAt n (c l m) z) ∧
      ∀ G : ComplexModel n → ℂ, (∀ᶠ w in 𝓝 (W z), DifferentiableAt ℂ G w) → ∀ l : Fin n,
        (fun p => fderiv ℂ G (W p) (EuclideanSpace.single l 1)) =ᶠ[𝓝 z] fun p =>
          ∑ m, c l m p * chartDeriv (complexChartAt (n := n) z)
            (EuclideanSpace.single m 1) (G ∘ W) p := by
  classical
  set e := complexChartAt (n := n) z with he
  obtain ⟨Θ, hΘN, hΘF, -⟩ := exists_localHolomorphicEquivAt hN hzN hFd hinj
  -- `W = Θ ∘ e` near `z`
  have hzs : z ∈ e.val.source := mem_complexChartAt_source z
  have hΘsrc : ∀ᶠ p in 𝓝 z, p ∈ e.val.source ∧ e.val p ∈ Θ.source :=
    Filter.Eventually.and (e.val.open_source.mem_nhds hzs)
      ((e.val.continuousAt hzs).preimage_mem_nhds (Θ.isOpen_source.mem_nhds Θ.center_mem_source))
  have hWΘ : ∀ p, p ∈ e.val.source → W p = Θ.toFun (e.val p) := fun p hp => by
    rw [hΘF]; simp only [Function.comp_apply, e.val.left_inv hp]
  refine ⟨fun l m p => fderiv ℂ Θ.invFun (W p) (EuclideanSpace.single l 1) m, fun l m => ?_, ?_⟩
  · -- holomorphy of the coefficients
    set H : ComplexModel n → ℂ := fun ζ =>
      fderiv ℂ Θ.invFun (Θ.toFun ζ) (EuclideanSpace.single l 1) m with hH
    have hdi := Hironaka.differentiableOn_fderiv_apply_of_isOpen Θ.invFun_holomorphic
      Θ.isOpen_target (EuclideanSpace.single l (1 : ℂ))
    have hHd : ∀ᶠ ζ in 𝓝 (e.val z), DifferentiableAt ℂ H ζ := by
      filter_upwards [Θ.isOpen_source.mem_nhds Θ.center_mem_source] with ζ hζ
      have h1 : DifferentiableAt ℂ Θ.toFun ζ :=
        (Θ.toFun_holomorphic ζ hζ).differentiableAt (Θ.isOpen_source.mem_nhds hζ)
      have h2 : DifferentiableAt ℂ (fun w => fderiv ℂ Θ.invFun w (EuclideanSpace.single l 1))
          (Θ.toFun ζ) :=
        (hdi _ (Θ.mapsTo_toFun hζ)).differentiableAt
          (Θ.isOpen_target.mem_nhds (Θ.mapsTo_toFun hζ))
      have h3 : DifferentiableAt ℂ (fun w : ComplexModel n => w m)
          (fderiv ℂ Θ.invFun (Θ.toFun ζ) (EuclideanSpace.single l 1)) :=
        (EuclideanSpace.proj (𝕜 := ℂ) m).differentiableAt
      exact h3.comp ζ (h2.comp ζ h1)
    refine (holomorphicAt_comp_chart e hzs hHd).congr ?_
    filter_upwards [hΘsrc] with p hp
    simp only [hH, hWΘ p hp.1]
  · intro G hG l
    have hWc : ∀ᶠ p in 𝓝 z, DifferentiableAt ℂ G (W p) := by
      have hcont : ContinuousAt W z := by
        have h1 : ContinuousAt (fun p => Θ.toFun (e.val p)) z :=
          ((Θ.toFun_holomorphic _ Θ.center_mem_source).continuousWithinAt.continuousAt
            (Θ.isOpen_source.mem_nhds Θ.center_mem_source)).comp (e.val.continuousAt hzs)
        refine h1.congr ?_
        filter_upwards [hΘsrc] with p hp
        exact (hWΘ p hp.1).symm
      exact hcont.eventually hG
    filter_upwards [hΘsrc, hWc] with p hp hGp
    obtain ⟨hpe, hpΘ⟩ := hp
    set ζ := e.val p with hζ
    have hWp : W p = Θ.toFun ζ := hWΘ p hpe
    have hΘd : DifferentiableAt ℂ Θ.toFun ζ :=
      (Θ.toFun_holomorphic ζ hpΘ).differentiableAt (Θ.isOpen_source.mem_nhds hpΘ)
    have hT : Θ.toFun ζ ∈ Θ.target := Θ.mapsTo_toFun hpΘ
    have hΘid : Θ.invFun (Θ.toFun ζ) = ζ := Θ.left_inv ζ hpΘ
    have hId : DifferentiableAt ℂ Θ.invFun (Θ.toFun ζ) :=
      (Θ.invFun_holomorphic _ hT).differentiableAt (Θ.isOpen_target.mem_nhds hT)
    -- `Θ ∘ Θ⁻¹ = id` near `Θ ζ`
    have hcomp : fderiv ℂ (Θ.toFun ∘ Θ.invFun) (Θ.toFun ζ) = ContinuousLinearMap.id ℂ _ := by
      have heq : Θ.toFun ∘ Θ.invFun =ᶠ[𝓝 (Θ.toFun ζ)] id := by
        filter_upwards [Θ.isOpen_target.mem_nhds hT] with w hw
        exact Θ.right_inv w hw
      rw [heq.fderiv_eq, fderiv_id]
    have hchain : fderiv ℂ Θ.toFun ζ (fderiv ℂ Θ.invFun (Θ.toFun ζ)
        (EuclideanSpace.single l 1)) = EuclideanSpace.single l 1 := by
      have h := fderiv_comp (Θ.toFun ζ) (hΘid ▸ hΘd) hId
      rw [hcomp, hΘid] at h
      have := congrArg (fun L : ComplexModel n →L[ℂ] ComplexModel n => L (EuclideanSpace.single l 1)) h
      simpa using this.symm
    -- the chart derivative of `G ∘ W` is that of `G ∘ Θ`
    have hloc : (G ∘ W) ∘ e.val.symm =ᶠ[𝓝 ζ] G ∘ Θ.toFun := by
      have hTc : Tendsto e.val.symm (𝓝 ζ) (𝓝 p) := by
        have := e.val.continuousAt_symm (e.val.map_source hpe)
        rwa [ContinuousAt, e.val.left_inv hpe] at this
      filter_upwards [hTc.eventually (e.val.open_source.mem_nhds hpe),
        e.val.open_target.mem_nhds (e.val.map_source hpe)] with ζ' hζ' hζt
      simp only [Function.comp_apply]
      rw [hWΘ _ hζ', e.val.right_inv hζt]
    have hGd : DifferentiableAt ℂ G (Θ.toFun ζ) := hWp ▸ hGp
    have hsum : ∀ m, chartDeriv e (EuclideanSpace.single m 1) (G ∘ W) p =
        fderiv ℂ (G ∘ Θ.toFun) ζ (EuclideanSpace.single m 1) := fun m => by
      simp only [chartDeriv, ← hζ, hloc.fderiv_eq]
    simp only [hsum]
    have hlin : ∑ m, fderiv ℂ Θ.invFun (W p) (EuclideanSpace.single l 1) m *
        fderiv ℂ (G ∘ Θ.toFun) ζ (EuclideanSpace.single m 1) =
        fderiv ℂ (G ∘ Θ.toFun) ζ (fderiv ℂ Θ.invFun (W p) (EuclideanSpace.single l 1)) := by
      conv_rhs => rw [← sum_smul_single (fderiv ℂ Θ.invFun (W p) (EuclideanSpace.single l 1))]
      rw [map_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [map_smul, smul_eq_mul]
    rw [hlin, fderiv_comp ζ hGd hΘd, ContinuousLinearMap.comp_apply, hWp, hchain]

end Coordinates

/-! ### The derivation `y σ^*(∂)` in a monomial chart -/

section Monomial

open BlowupMonomialCharts

variable {n : ℕ}

/-- The direction in which the monomial map `σⱼ` moves a point when the `l`-th coordinate moves:
`σⱼ (w + t eₗ) = σⱼ w + t · lineDir k j l w` (`monomial_add_smul_single`). -/
def lineDir (k : ℕ) (j l : Fin n) (w : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 fun i =>
    if l = j then (if i = j then 1 else if k ≤ i.1 then w i else 0)
    else if k ≤ l.1 then (if i = l then w j else 0)
    else (if i = l then 1 else 0)

@[simp] theorem lineDir_apply (k : ℕ) (j l i : Fin n) (w : ComplexModel n) :
    lineDir k j l w i =
      if l = j then (if i = j then 1 else if k ≤ i.1 then w i else 0)
      else if k ≤ l.1 then (if i = l then w j else 0)
      else (if i = l then 1 else 0) := rfl

/-- **The monomial map is affine on coordinate lines.** -/
theorem monomial_add_smul_single {k : ℕ} {j : Fin n} (hj : k ≤ j.1) (w : ComplexModel n)
    (l : Fin n) (t : ℂ) :
    monomial k j (w + t • EuclideanSpace.single l 1) = monomial k j w + t • lineDir k j l w := by
  ext i
  simp only [monomial_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.single_apply, lineDir_apply]
  by_cases hlj : l = j
  · subst hlj
    by_cases hil : i = l
    · subst hil; simp
    · by_cases hki : k ≤ i.1
      · simp [hil, hki]; ring
      · simp [hil, hki]
  · by_cases hil : i = l
    · subst hil
      by_cases hki : k ≤ i.1
      · simp [hlj, hki, Ne.symm hlj]; ring
      · simp [hlj, hki]
    · by_cases hij : i = j
      · subst hij; simp [hil]; intro h; exact absurd h hlj
      · by_cases hki : k ≤ i.1
        · by_cases hkl : k ≤ l.1
          · simp [hil, hij, hki, hkl, hlj]; exact Or.inl fun h => absurd h.symm hlj
          · simp [hil, hij, hki, hkl, hlj]; exact Or.inl fun h => absurd h.symm hlj
        · by_cases hkl : k ≤ l.1
          · simp [hil, hij, hki, hkl, hlj]
          · simp [hil, hij, hki, hkl, hlj]

/-- **Partial derivatives of `F ∘ σⱼ`**: `∂ₗ (F ∘ σⱼ)(w) = DF(σⱼ w) (lineDir k j l w)`. -/
theorem fderiv_comp_monomial {k : ℕ} {j : Fin n} (hj : k ≤ j.1) {F : ComplexModel n → ℂ}
    {w : ComplexModel n} (hF : DifferentiableAt ℂ F (monomial k j w)) (l : Fin n) :
    fderiv ℂ (F ∘ monomial k j) w (EuclideanSpace.single l 1) =
      fderiv ℂ F (monomial k j w) (lineDir k j l w) := by
  have hσ : DifferentiableAt ℂ (monomial k j) w :=
    ((contDiff_monomial k j).differentiable (by simp)) w
  have hFσ : DifferentiableAt ℂ (F ∘ monomial k j) w := hF.comp w hσ
  have hline : ∀ v : ComplexModel n, ∀ a : ComplexModel n,
      HasDerivAt (fun t : ℂ => a + t • v) v 0 := fun v a => by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add a
  have h1 : HasDerivAt ((F ∘ monomial k j) ∘ fun t : ℂ => w + t • EuclideanSpace.single l 1)
      (fderiv ℂ (F ∘ monomial k j) w (EuclideanSpace.single l 1)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hFσ.hasFDerivAt (hline _ w) (by simp)
  have h2 : HasDerivAt (F ∘ fun t : ℂ => monomial k j w + t • lineDir k j l w)
      (fderiv ℂ F (monomial k j w) (lineDir k j l w)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hF.hasFDerivAt (hline _ _) (by simp)
  have heq : ((F ∘ monomial k j) ∘ fun t : ℂ => w + t • EuclideanSpace.single l 1) =
      F ∘ fun t : ℂ => monomial k j w + t • lineDir k j l w := by
    funext t
    simp only [Function.comp_apply, monomial_add_smul_single hj]
  rw [heq] at h1
  exact h1.unique h2

/-- The coefficients of the derivation `wⱼ σⱼ^*(∂ᵢ)` in the coordinates `w`:
`wⱼ (∂ᵢ F)(σⱼ w) = ∑ₗ monomialCoeff k j i l w · ∂ₗ (F ∘ σⱼ)(w)` (`mul_fderiv_monomial`). -/
def monomialCoeff (k : ℕ) (j i l : Fin n) (w : ComplexModel n) : ℂ :=
  if i = j then (if l = j then w j else if k ≤ l.1 then -w l else 0)
  else if k ≤ i.1 then (if l = i then 1 else 0)
  else (if l = i then w j else 0)

theorem differentiable_monomialCoeff (k : ℕ) (j i l : Fin n) :
    Differentiable ℂ (monomialCoeff k j i l) := by
  have hp : ∀ m : Fin n, Differentiable ℂ fun w : ComplexModel n => w m := fun m =>
    (EuclideanSpace.proj (𝕜 := ℂ) m).differentiable
  unfold monomialCoeff
  split_ifs
  · exact hp j
  · exact (hp l).neg
  · exact differentiable_const 0
  · exact differentiable_const 1
  · exact differentiable_const 0
  · exact hp j
  · exact differentiable_const 0

/-- The coefficient of `∂ⱼ` vanishes unless `i = j`, where it is `wⱼ`. -/
theorem monomialCoeff_self (k : ℕ) (j i : Fin n) (w : ComplexModel n) :
    monomialCoeff k j i j w = if i = j then w j else 0 := by
  unfold monomialCoeff
  by_cases hij : i = j
  · simp [hij]
  · by_cases hki : k ≤ i.1
    · simp [hij, hki, Ne.symm hij]
    · simp [hij, hki, Ne.symm hij]

theorem sum_monomialCoeff_mul_lineDir {k : ℕ} {j : Fin n} (hj : k ≤ j.1) (i m : Fin n)
    (w : ComplexModel n) :
    ∑ l, monomialCoeff k j i l w * lineDir k j l w m = if m = i then w j else 0 := by
  classical
  by_cases hij : i = j
  · subst hij
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hrest : ∀ l ∈ Finset.univ.erase i, monomialCoeff k i i l w * lineDir k i l w m =
        if l = m then (if k ≤ l.1 then -(w l * w i) else 0) else 0 := by
      intro l hl
      have hli : l ≠ i := Finset.ne_of_mem_erase hl
      by_cases hkl : k ≤ l.1
      · by_cases hml : m = l
        · subst hml; simp [monomialCoeff, hli, hkl]
        · simp [monomialCoeff, hli, hkl, hml, Ne.symm hml]
      · simp [monomialCoeff, hli, hkl]
    rw [Finset.sum_congr rfl hrest, Finset.sum_ite_eq']
    by_cases hmi : m = i
    · subst hmi; simp [monomialCoeff]
    · by_cases hkm : k ≤ m.1
      · simp [monomialCoeff, hmi, hkm, Finset.mem_erase]; ring
      · simp [monomialCoeff, hmi, hkm, Finset.mem_erase]
  · rw [Finset.sum_eq_single i]
    · by_cases hki : k ≤ i.1
      · by_cases hmi : m = i
        · subst hmi; simp [monomialCoeff, hij, hki]
        · simp [monomialCoeff, hij, hki, hmi]
      · by_cases hmi : m = i
        · subst hmi; simp [monomialCoeff, hij, hki]
        · simp [monomialCoeff, hij, hki, hmi]
    · intro l _ hli
      by_cases hki : k ≤ i.1
      · simp [monomialCoeff, hij, hki, hli]
      · simp [monomialCoeff, hij, hki, hli]
    · simp

/-- **The derivation `wⱼ σⱼ^*(∂ᵢ)` has holomorphic coefficients** (Włodarczyk, proof of
`le:inclusions`): `wⱼ (∂ᵢ F)(σⱼ w) = ∑ₗ monomialCoeff k j i l w · ∂ₗ (F ∘ σⱼ)(w)`. -/
theorem mul_fderiv_monomial {k : ℕ} {j : Fin n} (hj : k ≤ j.1) {F : ComplexModel n → ℂ}
    {w : ComplexModel n} (hF : DifferentiableAt ℂ F (monomial k j w)) (i : Fin n) :
    w j * fderiv ℂ F (monomial k j w) (EuclideanSpace.single i 1) =
      ∑ l, monomialCoeff k j i l w * fderiv ℂ (F ∘ monomial k j) w (EuclideanSpace.single l 1) := by
  classical
  set A := fderiv ℂ F (monomial k j w)
  have hd : ∀ l, fderiv ℂ (F ∘ monomial k j) w (EuclideanSpace.single l 1) =
      ∑ m, lineDir k j l w m * A (EuclideanSpace.single m 1) := fun l => by
    rw [fderiv_comp_monomial hj hF l]
    conv_lhs => rw [← sum_smul_single (lineDir k j l w)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [map_smul, smul_eq_mul]
  simp only [hd, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ m, ∑ l, monomialCoeff k j i l w * (lineDir k j l w m * A (EuclideanSpace.single m 1)) =
      (if m = i then w j else 0) * A (EuclideanSpace.single m 1) := fun m => by
    rw [← sum_monomialCoeff_mul_lineDir hj i m w, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [hinner, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Monomial

/-! ### Chart derivatives in flattening coordinates, and the derivation data at a point -/

section Assembly

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Reindexing a triple sum. -/
theorem sum_triple {n : ℕ} (a : Fin n → ℂ) (P c : Fin n → Fin n → ℂ) (D : Fin n → ℂ) :
    ∑ i, a i * ∑ l, P i l * ∑ m, c l m * D m = ∑ m, (∑ i, a i * ∑ l, P i l * c l m) * D m := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring

end Assembly

/-! ### The data of `y σ^*(Der)` at a point of a blowup -/

section PointData

open BlowupFlatCoordinates BlowupMonomialCharts

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- The identity of an open set `S ∋ p`, as a local biholomorphism at `p`. -/
def idOn {p : ComplexModel n} (S : Set (ComplexModel n)) (hS : IsOpen S) (hp : p ∈ S) :
    LocalHolomorphicEquivAt (n := n) p where
  source := S
  target := S
  isOpen_source := hS
  isOpen_target := hS
  center_mem_source := hp
  toFun := id
  invFun := id
  toFun_holomorphic := differentiableOn_id
  invFun_holomorphic := differentiableOn_id
  mapsTo_toFun := mapsTo_id S
  mapsTo_invFun := mapsTo_id S
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl

end PointData

/-! ### Giraud--Villamayor: derivative ideals and controlled transforms -/

section Inclusions

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Power rule for chart derivatives: `∂(y^{q+1}) = (q+1) y^q ∂y`. -/
theorem chartDeriv_pow {e : ComplexChart n M} {v : ComplexModel n} {y : M → ℂ} {p₀ : M}
    (hp₀ : p₀ ∈ e.val.source) (hy : HolomorphicAt n y p₀) :
    ∀ q : ℕ, chartDeriv e v (fun p => y p ^ (q + 1)) =ᶠ[𝓝 p₀]
      fun p => ((q : ℂ) + 1) * y p ^ q * chartDeriv e v y p
  | 0 => by
    filter_upwards with p
    simp
  | q + 1 => by
    have h1 := chartDeriv_eventuallyEq_sum_mul (e := e) (v := v) (N := 1)
      (f := fun p => y p ^ (q + 1 + 1)) (a := fun _ => fun p => y p ^ (q + 1)) (s := fun _ => y)
      hp₀ (fun _ => holomorphicAt_pow hy (q + 1)) (fun _ => hy)
      (Eventually.of_forall fun p => by simp [pow_succ])
    filter_upwards [h1, chartDeriv_pow hp₀ hy q] with p hp hp'
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at hp
    rw [hp, hp']
    push_cast
    ring

end Inclusions

section Blowup

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- Membership of a single pulled-back germ in a pullback ideal. -/
theorem comp_mem_pullback {𝔟 : GermIdeal n X} {z : Y} {s : X → ℂ} {c : Y → ℂ} {g : Y → ℂ}
    (hs : 𝔟.mem (π z) s) (hg : HolomorphicAt n g z) (hc : HolomorphicAt n c z)
    (heq : g =ᶠ[𝓝 z] fun p => c p * s (π p)) : (GermIdeal.pullback (m := n) π 𝔟).mem z g := by
  show IsInSpanAt (n := n) (fun t => ∃ a, 𝔟.mem (π z) a ∧ t = a ∘ π) z g
  exact isInSpanAt_of_eq_mul ⟨s, hs, rfl⟩ hg hc heq

end Blowup

end

end Hironaka.BlowupDerivativeIdeal
