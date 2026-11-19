import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Blowup.BlowupFibreDirection
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.MarkedIdeal.MaximalContact
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Manifold.LocalHolomorphicInverse

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Derivative ideals under a blowup (Giraud, Villamayor)

Hironaka phase H3 (TN23-ENVELOPES; taken over from H2 on I-0977 C-0012); blueprint
`mc:derivative-power`, `mc:principal-power`, `mc:coordinate-derivatives`,
`mc:monomial-derivation`, `mc:exceptional-derivation`, `mc:inclusions`,
`mc:maximal-order-transform` (`blueprint/src/maximal-contact.tex`).
Source: Włodarczyk 2005, §2.6, Lemma `le:inclusions` and the lemma after the definition of
maximal order (Villamayor); Bierstone--Milman 2008, Lemmas 3.1--3.3.

Let `π : Y → X` be a blowup along `C` with exceptional divisor `D` (ideal `𝒪_Y(-D) = π^*𝓘_C`),
`𝔞` a coherent ideal, and `σ^c(𝔞, μ) = (π^*𝔞 : 𝒪_Y(-μD))` the controlled transform
(`BlowupControlledTransform.controlledTransform`).  Everything is for marked ideals with `N = M`.

## Main results

* `derivIdeal_le_idealPow`: `𝔞 ⊆ 𝔟^{q+1} ⟹ 𝓓(𝔞) ⊆ 𝔟^q` (from `chartDeriv_mem_idealPow'`, the
  generic form of `DerivativeIdeal.chartDeriv_mem_idealPow`); `iterDerivIdeal_le_idealPow`.
* `controlledTransform_derivIdeal_le` (**Giraud--Villamayor, `le:inclusions` for `r = 1`**):
  `𝔞 ⊆ 𝓘_C^{μ+1} ⟹ σ^c(𝓓(𝔞), μ) ⊆ 𝓓(σ^c(𝔞, μ + 1))`;
  `controlledTransform_iterDerivIdeal_le`: `𝔞 ⊆ 𝓘_C^{μ+r} ⟹ σ^c(𝓓^r(𝔞), μ) ⊆ 𝓓^r(σ^c(𝔞, μ + r))`;
  `controlledTransform_iterDerivIdeal_le_of_subset_cosupport`: the same under the source's
  hypothesis `C ⊆ cosupp(𝔞, μ + r)` (TN-CLASSICAL's Hadamard bridge).
* `MaximalContact.IsMaximalOrder.controlledTransform` (**Villamayor**): the controlled transform of
  a marked ideal of maximal order along an admissible centre is of maximal order
  (`..._of_subset_cosupport`: with `C ⊆ cosupp(𝔞, μ)`).

## Method (analytic form of the source's `y σ^*(Der)`)

At a point `z` of `Y` over `x = π z` (`exists_isDerivationGenerator`):

* if `x ∈ C`, take flattening coordinates `Φ ∘ e_x` of `C` at `x`, a monomial chart `j` and its
  local inverse `W` (`BlowupLocalSurjectivity.exists_monomialLocalInverse`), so that
  `σⱼ ∘ W = Φ ∘ e_x ∘ π` near `z`; then `y = Wⱼ` generates `π^*𝓘_C` near `z`
  (`exists_isDerivationGenerator_of_mem`);
* if `x ∉ C`, take `W = e_x ∘ π` (a local biholomorphism) and `y = 1`
  (`isDerivationGenerator_of_notMem`).

In both cases `W` is a local holomorphic coordinate system at `z`, so the coordinate derivatives
`(∂ₗ G) ∘ W` are holomorphic combinations of chart derivatives (`exists_coordDeriv_coeff`), and
`y · (∂ f) ∘ π = D'(f ∘ π)` for a derivation `D'` with `D'(y) ∈ (y)`
(`derivationData_of_coordinates`, `mul_fderiv_monomial`).  The algebra of the source,
`D'(y^{μ+1} h) ∈ y^{μ+1} 𝓓(h)` and cancellation of `y^{μ+1}`, then gives the inclusion.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupDerivativeIdeal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences Hironaka.HolomorphicMaps GermIdealOrder
  DerivativeIdeal IdealWeightPowers InvertibleIdealQuotient BlowupExceptionalDivisor
  BlowupControlledTransform

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

/-- `𝔞 ⊆ 𝔟^{q+1} ⟹ 𝓓(𝔞) ⊆ 𝔟^q`. -/
theorem derivIdeal_le_idealPow {𝔞 : GermIdeal n M} (h𝔟 : ∀ y g, 𝔟.mem y g → HolomorphicAt n g y)
    {q : ℕ} (hle : 𝔞.Le (idealPow 𝔟 (q + 1))) : (derivIdeal 𝔞).Le (idealPow 𝔟 q) := by
  intro y g hg
  refine mem_idealPow_of_isInSpanAt (hg.mono ?_)
  rintro s (hs | ⟨e', v', f, hye, hf, rfl⟩)
  · exact idealPow_succ_le h𝔟 q y s (hle y s hs)
  · exact chartDeriv_mem_idealPow' h𝔟 hye q f (hle y f hf)

/-- `𝔞 ⊆ 𝔟^{q+i} ⟹ 𝓓^i(𝔞) ⊆ 𝔟^q`. -/
theorem iterDerivIdeal_le_idealPow {𝔞 : GermIdeal n M}
    (h𝔟 : ∀ y g, 𝔟.mem y g → HolomorphicAt n g y) {q : ℕ} :
    ∀ i, 𝔞.Le (idealPow 𝔟 (q + i)) → (iterDerivIdeal 𝔞 i).Le (idealPow 𝔟 q)
  | 0, hle => hle
  | i + 1, hle => by
    rw [iterDerivIdeal_succ]
    refine derivIdeal_le_idealPow h𝔟 (iterDerivIdeal_le_idealPow h𝔟 i ?_)
    rwa [show q + 1 + i = q + (i + 1) by omega]

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

/-- **Chart derivatives in flattening coordinates.**  If `Φ` is a local biholomorphism at `e x`
(`e` a chart at `x`), every chart derivative of `f` near `x` is a holomorphic
combination of the coordinate derivatives of `F = f ∘ e⁻¹ ∘ Φ⁻¹` at `Φ (e q)`. -/
theorem chartDeriv_eventuallyEq_sum_flat {x : X} (e : ComplexChart n X) (hxs : x ∈ e.val.source)
    (Φ : LocalHolomorphicEquivAt (n := n) (e.val x)) {f : X → ℂ}
    (hf : HolomorphicAt n f x) (e' : ComplexChart n X) (hx' : x ∈ e'.val.source)
    (v : ComplexModel n) :
    ∃ α : Fin n → X → ℂ, (∀ i, HolomorphicAt n (α i) x) ∧
      chartDeriv e' v f =ᶠ[𝓝 x] fun q => ∑ i, α i q *
        fderiv ℂ (f ∘ e.val.symm ∘ Φ.invFun) (Φ.toFun (e.val q)) (EuclideanSpace.single i 1) := by
  classical
  set F := f ∘ e.val.symm ∘ Φ.invFun with hF
  refine ⟨fun i q => ∑ l, transitionCoeff e e' v l q *
    fderiv ℂ Φ.toFun (e.val q) (EuclideanSpace.single l 1) i, fun i => ?_, ?_⟩
  · refine HolomorphicAt.sum _ fun l _ => (holomorphicAt_transitionCoeff e e' hxs hx' l).mul ?_
    have hdi := Hironaka.differentiableOn_fderiv_apply_of_isOpen Φ.toFun_holomorphic
      Φ.isOpen_source (EuclideanSpace.single l (1 : ℂ))
    refine holomorphicAt_comp_chart e
      (W := fun ζ => fderiv ℂ Φ.toFun ζ (EuclideanSpace.single l 1) i) hxs ?_
    filter_upwards [Φ.isOpen_source.mem_nhds Φ.center_mem_source] with ζ hζ
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt.comp ζ
      ((hdi ζ hζ).differentiableAt (Φ.isOpen_source.mem_nhds hζ))
  · have hsrc : ∀ᶠ q in 𝓝 x, q ∈ e.val.source ∧ e.val q ∈ Φ.source :=
      Filter.Eventually.and (e.val.open_source.mem_nhds hxs)
        ((e.val.continuousAt hxs).preimage_mem_nhds
          (Φ.isOpen_source.mem_nhds Φ.center_mem_source))
    filter_upwards [chartDeriv_eventuallyEq_sum (v := v) e e' hxs hx' hf, hsrc,
      hf.eventually_nhds] with q hq hqs hfq
    rw [hq]
    obtain ⟨hqe, hqΦ⟩ := hqs
    set ζ := e.val q with hζ
    have hT : Φ.toFun ζ ∈ Φ.target := Φ.mapsTo_toFun hqΦ
    have hΦd : DifferentiableAt ℂ Φ.toFun ζ :=
      (Φ.toFun_holomorphic ζ hqΦ).differentiableAt (Φ.isOpen_source.mem_nhds hqΦ)
    have hId : DifferentiableAt ℂ Φ.invFun (Φ.toFun ζ) :=
      (Φ.invFun_holomorphic _ hT).differentiableAt (Φ.isOpen_target.mem_nhds hT)
    have hfe : DifferentiableAt ℂ (f ∘ e.val.symm) (Φ.invFun (Φ.toFun ζ)) := by
      rw [Φ.left_inv ζ hqΦ]
      exact (eventually_differentiableAt_comp_symm e hqe hfq).self_of_nhds
    have hFd : DifferentiableAt ℂ F (Φ.toFun ζ) := hfe.comp _ hId
    have hloc : f ∘ e.val.symm =ᶠ[𝓝 ζ] F ∘ Φ.toFun := by
      filter_upwards [Φ.isOpen_source.mem_nhds hqΦ] with ζ' hζ'
      simp only [hF, Function.comp_apply, Φ.left_inv ζ' hζ']
    have hl : ∀ l, chartDeriv e (EuclideanSpace.single l 1) f q =
        ∑ i, fderiv ℂ Φ.toFun ζ (EuclideanSpace.single l 1) i *
          fderiv ℂ F (Φ.toFun ζ) (EuclideanSpace.single i 1) := fun l => by
      simp only [chartDeriv, ← hζ, hloc.fderiv_eq, fderiv_comp ζ hFd hΦd,
        ContinuousLinearMap.comp_apply]
      conv_lhs => rw [← sum_smul_single (fderiv ℂ Φ.toFun ζ (EuclideanSpace.single l 1))]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    simp only [hl, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **The derivation data at a point of a holomorphic map, from local coordinates.**  Let
`π : Y → X` be holomorphic, `z ∈ Y`, `x = π z`, `Φ` a local biholomorphism at `e_x x`, `W` a local
holomorphic coordinate system at `z` with `Φ ∘ e_x ∘ π = Ψ ∘ W` near `z`, and suppose that the
function `Q` (read through `W`) satisfies the two identities of the source's `y σ^*(Der)`:
`Q (∂ᵢ F) ∘ Ψ = ∑ₗ Pᵢₗ ∂ₗ (F ∘ Ψ)` and `∑ₗ Pᵢₗ ∂ₗ Q = Rᵢ Q`.  Then for every `f` holomorphic near `x`,
every chart `e'` at `x` and every `v`, `y · (∂^{e'}_v f) ∘ π` (`y = Q ∘ W`) is `D'(f ∘ π)` for a
derivation `D' = ∑ₘ bₘ ∂^{e_z}_{eₘ}` with holomorphic coefficients and `D'(y) ∈ (y)`. -/
theorem derivationData_of_coordinates {π : Y → X}
    (hπs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {z : Y}
    (ex : ComplexChart n X) (hxs : π z ∈ ex.val.source)
    (Φ : LocalHolomorphicEquivAt (n := n) (ex.val (π z)))
    {W : Y → ComplexModel n} {N : Set (ComplexModel n)}
    (hN : IsOpen N) (hzN : (complexChartAt (n := n) z).val z ∈ N)
    (hFd : DifferentiableOn ℂ (W ∘ (complexChartAt (n := n) z).val.symm) N)
    (hinj : Function.Injective
      (fderiv ℂ (W ∘ (complexChartAt (n := n) z).val.symm) ((complexChartAt (n := n) z).val z)))
    {Ψ : ComplexModel n → ComplexModel n} (hΨ : Differentiable ℂ Ψ)
    (hΦW : ∀ᶠ p in 𝓝 z, π p ∈ ex.val.source ∧ ex.val (π p) ∈ Φ.source ∧
      Φ.toFun (ex.val (π p)) = Ψ (W p))
    {Q : ComplexModel n → ℂ} (hQ : Differentiable ℂ Q)
    {P : Fin n → Fin n → ComplexModel n → ℂ} (hP : ∀ i l, Differentiable ℂ (P i l))
    (hPΨ : ∀ (F : ComplexModel n → ℂ) (w : ComplexModel n), DifferentiableAt ℂ F (Ψ w) →
      ∀ i, Q w * fderiv ℂ F (Ψ w) (EuclideanSpace.single i 1) =
        ∑ l, P i l w * fderiv ℂ (F ∘ Ψ) w (EuclideanSpace.single l 1))
    {R : Fin n → ComplexModel n → ℂ} (hR : ∀ i, Differentiable ℂ (R i))
    (hPQ : ∀ i w, ∑ l, P i l w * fderiv ℂ Q w (EuclideanSpace.single l 1) = R i w * Q w)
    {f : X → ℂ} (hf : HolomorphicAt n f (π z)) (e' : ComplexChart n X)
    (hx' : π z ∈ e'.val.source) (v : ComplexModel n) :
    ∃ b : Fin n → Y → ℂ, (∀ m, HolomorphicAt n (b m) z) ∧
      (fun p => Q (W p) * chartDeriv e' v f (π p)) =ᶠ[𝓝 z] (fun p =>
        ∑ m, b m p * chartDeriv (complexChartAt (n := n) z) (EuclideanSpace.single m 1) (f ∘ π) p) ∧
      ∃ ρ : Y → ℂ, HolomorphicAt n ρ z ∧
        (fun p => ∑ m, b m p *
          chartDeriv (complexChartAt (n := n) z) (EuclideanSpace.single m 1) (Q ∘ W) p)
          =ᶠ[𝓝 z] fun p => ρ p * Q (W p) := by
  classical
  set ez := complexChartAt (n := n) z with hez
  have hzs : z ∈ ez.val.source := mem_complexChartAt_source z
  set F := f ∘ ex.val.symm ∘ Φ.invFun with hF
  obtain ⟨α, hα, hαeq⟩ := chartDeriv_eventuallyEq_sum_flat ex hxs Φ hf e' hx' v
  obtain ⟨c, hc, hceq⟩ := exists_coordDeriv_coeff hN hzN hFd hinj
  -- `W` is continuous at `z`, and functions of `W` are holomorphic at `z`
  have hWhol : ∀ H : ComplexModel n → ℂ, Differentiable ℂ H → HolomorphicAt n (fun p => H (W p)) z := by
    intro H hH
    refine (holomorphicAt_comp_chart ez (W := H ∘ (W ∘ ez.val.symm)) hzs ?_).congr ?_
    · filter_upwards [hN.mem_nhds hzN] with ζ hζ
      exact (hH _).comp ζ ((hFd ζ hζ).differentiableAt (hN.mem_nhds hζ))
    · filter_upwards [ez.val.open_source.mem_nhds hzs] with p hp
      simp only [Function.comp_apply, ez.val.left_inv hp]
  have hWc : ContinuousAt W z := by
    have hcomp : ContinuousAt (fun p => (W ∘ ez.val.symm) (ez.val p)) z :=
      ((hFd _ hzN).differentiableAt (hN.mem_nhds hzN)).continuousAt.comp
        (ez.val.continuousAt hzs)
    refine hcomp.congr ?_
    filter_upwards [ez.val.open_source.mem_nhds hzs] with p hp
    simp only [Function.comp_apply, ez.val.left_inv hp]
  -- `F` is differentiable near `Φ (e_x (π z))`
  have hFev : ∀ᶠ w in 𝓝 (Φ.toFun (ex.val (π z))), DifferentiableAt ℂ F w := by
    have hT : Φ.toFun (ex.val (π z)) ∈ Φ.target := Φ.mapsTo_toFun Φ.center_mem_source
    have hIc : ContinuousAt Φ.invFun (Φ.toFun (ex.val (π z))) :=
      ((Φ.invFun_holomorphic _ hT).differentiableAt (Φ.isOpen_target.mem_nhds hT)).continuousAt
    have hId : Φ.invFun (Φ.toFun (ex.val (π z))) = ex.val (π z) :=
      Φ.left_inv _ Φ.center_mem_source
    have h1 := eventually_differentiableAt_comp_symm ex hxs hf
    rw [← hId] at h1
    filter_upwards [hIc.eventually h1, Φ.isOpen_target.mem_nhds hT] with w hw hwT
    exact hw.comp w ((Φ.invFun_holomorphic w hwT).differentiableAt (Φ.isOpen_target.mem_nhds hwT))
  -- along `π`, `Φ ∘ e_x ∘ π = Ψ ∘ W` tends to `Φ (e_x (π z))`
  have hΨWz : Ψ (W z) = Φ.toFun (ex.val (π z)) := hΦW.self_of_nhds.2.2.symm
  have hFΨ : ∀ᶠ w in 𝓝 (W z), DifferentiableAt ℂ (F ∘ Ψ) w := by
    have hΨc : ContinuousAt Ψ (W z) := (hΨ (W z)).continuousAt
    rw [ContinuousAt, hΨWz] at hΨc
    filter_upwards [hΨc.eventually hFev] with w hw
    exact hw.comp w (hΨ w)
  have hFp : ∀ᶠ p in 𝓝 z, DifferentiableAt ℂ F (Ψ (W p)) := by
    have hc' : ContinuousAt (fun p => Ψ (W p)) z := (hΨ (W z)).continuousAt.comp hWc
    rw [ContinuousAt, hΨWz] at hc'
    exact hc'.eventually hFev
  -- `(F ∘ Ψ) ∘ W = f ∘ π` near `z`
  have hGW : (F ∘ Ψ) ∘ W =ᶠ[𝓝 z] f ∘ π := by
    filter_upwards [hΦW] with p hp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    simp only [hF, Function.comp_apply, ← hp3, Φ.left_inv _ hp2, ex.val.left_inv hp1]
  have hDm : ∀ m, chartDeriv ez (EuclideanSpace.single m 1) ((F ∘ Ψ) ∘ W) =ᶠ[𝓝 z]
      chartDeriv ez (EuclideanSpace.single m 1) (f ∘ π) := fun m => chartDeriv_congr hzs hGW
  have hπc : ContinuousAt π z := (hπs z).continuousAt
  have hαz : ∀ᶠ p in 𝓝 z, chartDeriv e' v f (π p) = ∑ i, α i (π p) *
      fderiv ℂ F (Φ.toFun (ex.val (π p))) (EuclideanSpace.single i 1) := hπc.eventually hαeq
  refine ⟨fun m p => ∑ i, α i (π p) * ∑ l, P i l (W p) * c l m p, fun m => ?_, ?_,
    fun p => ∑ i, α i (π p) * R i (W p), ?_, ?_⟩
  · refine HolomorphicAt.sum _ fun i _ => ?_
    refine HolomorphicAt.mul ((hα i).comp_contMDiff (Eventually.of_forall fun p => hπs p))
      (HolomorphicAt.sum _ fun l _ => (hWhol _ (hP i l)).mul (hc l m))
  · filter_upwards [hαz, hΦW, hFp, eventually_all.2 (hceq (F ∘ Ψ) hFΨ),
      eventually_all.2 hDm] with p hp1 hp2 hp3 hp4 hp5
    rw [hp1, hp2.2.2, Finset.mul_sum]
    have h1 : ∀ i, Q (W p) * (α i (π p) * fderiv ℂ F (Ψ (W p)) (EuclideanSpace.single i 1)) =
        α i (π p) * ∑ l, P i l (W p) * ∑ m, c l m p *
          chartDeriv ez (EuclideanSpace.single m 1) (f ∘ π) p := fun i => by
      rw [mul_left_comm, hPΨ F (W p) hp3 i]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hp4 l]
      congr 1
      exact Finset.sum_congr rfl fun m _ => by rw [hp5 m]
    simp only [h1]
    exact sum_triple _ _ _ _
  · exact HolomorphicAt.sum _ fun i _ =>
      ((hα i).comp_contMDiff (Eventually.of_forall fun p => hπs p)).mul (hWhol _ (hR i))
  · filter_upwards [eventually_all.2 (hceq Q (Eventually.of_forall fun w => hQ w))] with p hp
    have hp' : ∀ l, ∑ m, c l m p * chartDeriv ez (EuclideanSpace.single m 1) (Q ∘ W) p =
        fderiv ℂ Q (W p) (EuclideanSpace.single l 1) := fun l => (hp l).symm
    rw [← sum_triple]
    simp only [hp', hPQ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring

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

variable (n) in
/-- **The data of the derivation `y σ^*(Der)` near a point `z` of the blowup**: an open `U ∋ z`
on which `y` generates `π^*𝓘_C = 𝒪_Y(-D)` and vanishes identically on no nonempty open set, and,
for every `f` holomorphic near `π z`, every chart `e'` at `π z` and every `v`, a derivation
`D' = ∑ₘ bₘ ∂^{e_z}_{eₘ}` with holomorphic coefficients, `y · (∂^{e'}_v f) ∘ π = D'(f ∘ π)` and
`D'(y) ∈ (y)` near `z`. -/
structure IsDerivationGenerator (π : Y → X) (C : Set X) (z : Y) (U : Set Y) (y : Y → ℂ) :
    Prop where
  isOpen : IsOpen U
  mem : z ∈ U
  holomorphicAt : ∀ p ∈ U, HolomorphicAt n y p
  generates : ∀ p ∈ U, ∀ g, (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).mem p g ↔
    IsInSpanAt (n := n) (· = y) p g
  exists_ne_zero : ∀ V : Set Y, IsOpen V → V ⊆ U → V.Nonempty → ∃ p ∈ V, y p ≠ 0
  derivation : ∀ f : X → ℂ, HolomorphicAt n f (π z) → ∀ e' : ComplexChart n X,
    π z ∈ e'.val.source → ∀ v : ComplexModel n,
    ∃ b : Fin n → Y → ℂ, (∀ m, HolomorphicAt n (b m) z) ∧
      (fun p => y p * chartDeriv e' v f (π p)) =ᶠ[𝓝 z] (fun p =>
        ∑ m, b m p * chartDeriv (complexChartAt (n := n) z) (EuclideanSpace.single m 1) (f ∘ π) p) ∧
      ∃ ρ : Y → ℂ, HolomorphicAt n ρ z ∧
        (fun p => ∑ m, b m p *
          chartDeriv (complexChartAt (n := n) z) (EuclideanSpace.single m 1) y p)
          =ᶠ[𝓝 z] fun p => ρ p * y p

/-- **Away from the centre**: `y = 1`, and `W = e_x ∘ π` is a local coordinate system. -/
theorem isDerivationGenerator_of_notMem (hπ : IsBlowupAlong n C π) {z : Y} (hz : π z ∉ C) :
    IsDerivationGenerator n π C z (π ⁻¹' Cᶜ) (fun _ => 1) := by
  classical
  have hπs := hπ.contMDiff
  have hUo : IsOpen (π ⁻¹' Cᶜ) := hπ.1.1.isOpen_compl.preimage hπs.continuous
  refine ⟨hUo, hz, fun p _ => holomorphicAt_const 1, fun p hp g => ?_, fun V _ _ hV => ?_,
    fun f hf e' hx' v => ?_⟩
  · constructor
    · intro hg
      exact isInSpanAt_of_eq_mul rfl hg.1 hg.1 (Eventually.of_forall fun q => by simp)
    · intro hg
      obtain ⟨hgh, c, hc, hgc⟩ := isInSpanAt_eq_iff.mp hg
      have h1 : (vanishingIdeal (n := n) C).mem (π p) (fun _ => 1) :=
        ⟨holomorphicAt_const 1, by
          filter_upwards [hπ.1.1.isOpen_compl.mem_nhds hp] with q hq hqC
          exact absurd hqC hq⟩
      show IsInSpanAt (n := n) (fun s => ∃ a, (vanishingIdeal (n := n) C).mem (π p) a ∧ s = a ∘ π)
        p g
      exact isInSpanAt_of_eq_mul ⟨fun _ => 1, h1, rfl⟩ hgh hc hgc
  · obtain ⟨p, hp⟩ := hV
    exact ⟨p, hp, one_ne_zero⟩
  · -- local coordinates `W = e_x ∘ π` at `z`
    set ex := complexChartAt (n := n) (π z) with hex
    set ez := complexChartAt (n := n) z with hez
    have hzs : z ∈ ez.val.source := mem_complexChartAt_source z
    have hxs : π z ∈ ex.val.source := mem_complexChartAt_source (π z)
    set N := coordinateDomain π ez ex with hN
    have hNo : IsOpen N := coordinateDomain_isOpen hπs ez ex
    have hzN : ez.val z ∈ N := mem_coordinateDomain hzs hxs
    have hFd : DifferentiableOn ℂ ((fun p => ex.val (π p)) ∘ ez.val.symm) N := fun ζ hζ =>
      ((coordinateMap_contDiffAt hπs ez ex hζ).differentiableAt (by simp)).differentiableWithinAt
    have hinj : Function.Injective
        (fderiv ℂ ((fun p => ex.val (π p)) ∘ ez.val.symm) (ez.val z)) := by
      have hbij : Function.Bijective
          (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z) := by
        by_contra h
        exact hz (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)
      have hd : DifferentiableAt ℂ (coordinateMap π ez ex) (ez.val z) :=
        (coordinateMap_contDiffAt hπs ez ex hzN).differentiableAt (by simp)
      refine (injective_iff_map_eq_zero _).mpr fun w hw => ?_
      have h0 : mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z w = 0 := by
        rw [← BlowupFibreDirection.fderiv_coordinateMap_eq_mfderiv hπs z w]
        change fderiv ℝ (coordinateMap π ez ex) (ez.val z) w = 0
        rw [hd.fderiv_restrictScalars ℝ]
        exact hw
      exact (injective_iff_map_eq_zero
        (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z)).mp hbij.1 w h0
    have hT : ex.val (π z) ∈ ex.val.target := ex.val.map_source hxs
    obtain ⟨b, hb, hbeq, ρ, hρ, hρeq⟩ := derivationData_of_coordinates hπs ex hxs
      (idOn ex.val.target ex.val.open_target hT) hNo hzN hFd hinj (Ψ := id) differentiable_id
      (by
        filter_upwards [(hπs z).continuousAt.preimage_mem_nhds
          (ex.val.open_source.mem_nhds hxs)] with p hp
        exact ⟨hp, ex.val.map_source hp, rfl⟩)
      (Q := fun _ => 1) (differentiable_const 1)
      (P := fun i l _ => if i = l then 1 else 0) (fun i l => differentiable_const _)
      (fun F w _ i => by simp [Finset.sum_ite_eq])
      (R := fun _ _ => 0) (fun _ => differentiable_const 0)
      (fun i w => by simp)
      hf e' hx' v
    exact ⟨b, hb, hbeq, ρ, hρ, hρeq⟩

/-- **Over the centre**: in a monomial chart `j` with local inverse `W` (`σⱼ ∘ W = Φ ∘ e_x ∘ π`),
`y = Wⱼ` generates `π^*𝓘_C` and `y σ^*(Der)` is the derivation `wⱼ σⱼ^*(∂)` of the source. -/
theorem exists_isDerivationGenerator_of_mem (hπ : IsBlowupAlong n C π) {z : Y} (hz : π z ∈ C) :
    ∃ (U : Set Y) (y : Y → ℂ), IsDerivationGenerator n π C z U y := by
  classical
  have hπs := hπ.contMDiff
  obtain ⟨k, hk⟩ := hπ.1.2 (π z) hz
  obtain ⟨-, -, Φ, hΦt, -, hflat⟩ := hk
  have hz' : π z ∈ flatDomain Φ := ⟨mem_chart_source _ (π z), Φ.center_mem_source⟩
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
    BlowupLocalSurjectivity.exists_monomialLocalInverse hπ hΦt hflat hz'
  have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ k j := fun z' hz' => by
    show monomial k j (W z') ∈ Φ.target
    rw [(hWeq z' hz').2]; exact Φ.mapsTo_toFun (hWeq z' hz').1.2
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := BlowupLocalSurjectivity.existsUnique_monomialLift hπ hΦt hflat hj
  -- the coordinate reading of `W` at `z`
  set ez := chartAt (ComplexModel n) z with hez
  set Nset : Set (ComplexModel n) := ez.target ∩ ez.symm ⁻¹' O with hNset
  have hNo : IsOpen Nset := ez.continuousOn_symm.isOpen_inter_preimage ez.open_target hO
  have hzN : ez z ∈ Nset :=
    ⟨ez.map_source (mem_chart_source _ z), by
      show ez.symm (ez z) ∈ O
      rw [ez.left_inv (mem_chart_source _ z)]; exact hzO⟩
  have hFd : DifferentiableOn ℂ (W ∘ ez.symm) Nset := by
    intro ζ hζ
    have h1 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n))
      (chart_mem_atlas (ComplexModel n) z) hζ.1
    have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W (ez.symm ζ) :=
      (hWs _ hζ.2).mdifferentiableAt (by simp)
    exact (mdifferentiableAt_iff_differentiableAt.mp (h2.comp _ h1)).differentiableWithinAt
  have hFinj : Function.Injective (fderiv ℂ (W ∘ ez.symm) (ez z)) := by
    have hdiff : DifferentiableAt ℂ (W ∘ ez.symm) (ez z) :=
      (hFd _ hzN).differentiableAt (hNo.mem_nhds hzN)
    refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
    by_contra hv0
    apply BlowupFibreDirection.fderiv_monomialInverse_ne_zero hO hWs hWmem hℓs
      (hℓ ℓ hℓs hℓπ) hzO hv0
    rw [show (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ)) = W ∘ ez.symm from rfl,
      hdiff.fderiv_restrictScalars ℝ]
    exact hv
  -- `Wⱼ = (flat coordinate j) ∘ π` on `O`
  have hWj : ∀ q ∈ O, W q j = flatCoord Φ j (π q) := fun q hq => by
    show W q j = Φ.toFun (chartAt (ComplexModel n) (π z) (π q)) j
    rw [← (hWeq q hq).2, monomial_apply]
    simp
  have hyhol : ∀ q ∈ O, HolomorphicAt n (fun p => W p j) q := fun q hq => by
    filter_upwards [hO.mem_nhds hq] with q' hq'
    exact (((EuclideanSpace.proj (𝕜 := ℂ) j : ComplexModel n →L[ℂ] ℂ).contMDiff.contMDiffAt.comp
      q' (hWs q' hq')).mdifferentiableAt (by simp))
  refine ⟨O, fun p => W p j, ⟨hO, hzO, hyhol, fun p hp g => ?_, fun V hVo hVO hV => ?_,
    fun f hf e' hx' v => ?_⟩⟩
  · -- `Wⱼ` generates `π^*𝓘_C` on `O`
    constructor
    · intro hg
      refine IsInSpanAt.of_forall_eq_mul ?_ (show IsInSpanAt (n := n)
        (fun s => ∃ a, (vanishingIdeal (n := n) C).mem (π p) a ∧ s = a ∘ π) p g from hg)
      rintro s ⟨a, ha, rfl⟩
      obtain ⟨bb, hb0, hbh, hbeq⟩ := exists_eq_sum_flatCoord Φ hΦt hflat (hWeq p hp).1 ha
      refine ⟨fun q => ∑ i, bb i (π q) * (if i = j then 1 else W q i), ?_, ?_⟩
      · refine HolomorphicAt.sum _ fun i _ => ?_
        refine ((hbh i).comp_contMDiff (Eventually.of_forall fun q => hπs q)).mul ?_
        split_ifs
        · exact holomorphicAt_const 1
        · filter_upwards [hO.mem_nhds hp] with q' hq'
          exact (((EuclideanSpace.proj (𝕜 := ℂ) i : ComplexModel n →L[ℂ] ℂ).contMDiff.contMDiffAt.comp
            q' (hWs q' hq')).mdifferentiableAt (by simp))
      · filter_upwards [(hπs p).continuousAt.eventually hbeq, hO.mem_nhds hp] with q hq hqO
        simp only [Function.comp_apply, hq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hfc : flatCoord Φ i (π q) = monomial k j (W q) i := by
          show Φ.toFun (chartAt (ComplexModel n) (π z) (π q)) i = _
          rw [← (hWeq q hqO).2]
        rw [hfc, monomial_apply]
        by_cases hki : k ≤ i.1
        · by_cases hij : i = j
          · subst hij; simp
          · simp [hki, hij]; ring
        · have : bb i = 0 := hb0 i (by omega)
          simp [this]
    · intro hg
      obtain ⟨hgh, c, hc, hgc⟩ := isInSpanAt_eq_iff.mp hg
      show IsInSpanAt (n := n) (fun s => ∃ a, (vanishingIdeal (n := n) C).mem (π p) a ∧ s = a ∘ π)
        p g
      refine isInSpanAt_of_eq_mul ⟨flatCoord Φ j,
        flatCoord_mem_vanishingIdeal Φ hflat hj (hWeq p hp).1, rfl⟩ hgh hc ?_
      filter_upwards [hgc, hO.mem_nhds hp] with q hq hqO
      rw [hq, Function.comp_apply, hWj q hqO]
  · -- `Wⱼ` vanishes identically on no nonempty open subset of `O`
    by_contra hall
    push Not at hall
    have hsub : V ⊆ π ⁻¹' C := fun p hp => by
      have hpO := hVO hp
      obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hWeq p hpO
      refine (hflat hp1 hp2).mpr ?_
      change Φ.toFun (chartAt (ComplexModel n) (π z) (π p)) ∈ _
      rw [← hp3]
      intro i hi
      rw [monomial_apply, hall p hp]
      split_ifs with h
      · ring
      · have : i = j := by by_contra hne; exact h ⟨hi, hne⟩
        rw [this, hall p hp]
    have := interior_maximal hsub hVo
    rw [ExceptionalFibres.interior_preimage_eq_empty hπ] at this
    obtain ⟨p, hp⟩ := hV
    exact this hp
  · -- the derivation `wⱼ σⱼ^*(∂)`
    have hΦW : ∀ᶠ p in 𝓝 z, π p ∈ (complexChartAt (n := n) (π z)).val.source ∧
        (complexChartAt (n := n) (π z)).val (π p) ∈ Φ.source ∧
        Φ.toFun ((complexChartAt (n := n) (π z)).val (π p)) = monomial k j (W p) := by
      filter_upwards [hO.mem_nhds hzO] with p hp
      exact ⟨(hWeq p hp).1.1, (hWeq p hp).1.2, (hWeq p hp).2.symm⟩
    have hproj : ∀ w : ComplexModel n, ∀ l : Fin n,
        fderiv ℂ (fun w : ComplexModel n => w j) w (EuclideanSpace.single l 1) =
          if l = j then 1 else 0 := fun w l => by
      have h : (fun w : ComplexModel n => w j) = ⇑(EuclideanSpace.proj (𝕜 := ℂ) j) := by
        funext w; rfl
      rw [h, ContinuousLinearMap.fderiv]
      simp [PiLp.single_apply, eq_comm]
    obtain ⟨b, hb, hbeq, ρ, hρ, hρeq⟩ := derivationData_of_coordinates hπs
      (complexChartAt (n := n) (π z)) (mem_complexChartAt_source _) Φ hNo hzN hFd hFinj
      (Ψ := monomial k j) ((contDiff_monomial k j).differentiable (by simp)) hΦW
      (Q := fun w => w j) (EuclideanSpace.proj (𝕜 := ℂ) j).differentiable
      (P := monomialCoeff k j) (differentiable_monomialCoeff k j)
      (fun F w hF i => mul_fderiv_monomial hj hF i)
      (R := fun i _ => if i = j then 1 else 0) (fun i => differentiable_const _)
      (fun i w => by
        simp only [hproj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          if_true, monomialCoeff_self]
        split_ifs <;> simp)
      hf e' hx' v
    exact ⟨b, hb, hbeq, ρ, hρ, hρeq⟩

/-- At every point of the blowup the data of `y σ^*(Der)` exist. -/
theorem exists_isDerivationGenerator (hπ : IsBlowupAlong n C π) (z : Y) :
    ∃ (U : Set Y) (y : Y → ℂ), IsDerivationGenerator n π C z U y := by
  by_cases hz : π z ∈ C
  · exact exists_isDerivationGenerator_of_mem hπ hz
  · exact ⟨_, _, isDerivationGenerator_of_notMem hπ hz⟩

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

/-- **Cancellation of a power of `y`**: if `y` vanishes identically on no nonempty open subset of
`U ∋ z` and `y^q g = y^q G` near `z` with `g`, `G` continuous near `z`, then `g = G` near `z`. -/
theorem eventuallyEq_of_pow_mul_eventuallyEq {U : Set M} (hU : IsOpen U) {z : M} (hz : z ∈ U)
    {y g G : M → ℂ}
    (hne : ∀ V : Set M, IsOpen V → V ⊆ U → V.Nonempty → ∃ p ∈ V, y p ≠ 0) (q : ℕ)
    (hg : ∀ᶠ p in 𝓝 z, ContinuousAt g p) (hG : ∀ᶠ p in 𝓝 z, ContinuousAt G p)
    (h : (fun p => y p ^ q * g p) =ᶠ[𝓝 z] fun p => y p ^ q * G p) : g =ᶠ[𝓝 z] G := by
  obtain ⟨V, hV, hVo, hzV⟩ := eventually_nhds_iff.mp
    ((hg.and hG).and (h.and (hU.mem_nhds hz)))
  filter_upwards [hVo.mem_nhds hzV] with p hp
  by_contra hne'
  have hcont : ContinuousAt (fun p => g p - G p) p := (hV p hp).1.1.sub (hV p hp).1.2
  have hopen : ∀ᶠ p' in 𝓝 p, g p' - G p' ≠ 0 :=
    hcont.eventually (isOpen_ne.mem_nhds (sub_ne_zero.mpr hne'))
  obtain ⟨W, hW, hWo, hpW⟩ := eventually_nhds_iff.mp (hopen.and (hVo.mem_nhds hp))
  obtain ⟨p', hp'W, hyp'⟩ := hne W hWo (fun p' hp' => (hV p' (hW p' hp').2).2.2) ⟨p, hpW⟩
  have h1 := (hV p' (hW p' hp'W).2).2.1
  have h2 : y p' ^ q * (g p' - G p') = 0 := by
    simp only at h1
    rw [mul_sub, h1, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hyp' (pow_eq_zero_iff'.mp h3).1
  · exact (hW p' hp'W).1 h3

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

/-- **Giraud--Villamayor, `le:inclusions` for `r = 1`** (Włodarczyk 2005, Lemma `le:inclusions`;
Bierstone--Milman 2008, Lemmas 3.1--3.3): for a coherent `𝔞 ⊆ 𝓘_C^{μ+1}`,
`σ^c(𝓓(𝔞), μ) ⊆ 𝓓(σ^c(𝔞, μ + 1))`. -/
theorem controlledTransform_derivIdeal_le (hπ : IsBlowupAlong n C π) {𝔞 : GermIdeal n X}
    (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hle : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) (μ + 1))) :
    (controlledTransform hπ (derivIdeal 𝔞) μ).Le
      (derivIdeal (controlledTransform hπ 𝔞 (μ + 1))) := by
  classical
  intro z g hg
  have hπs := hπ.contMDiff
  have hπc : ContinuousAt π z := (hπs z).continuousAt
  have h𝔞hol : ∀ x f, 𝔞.mem x f → HolomorphicAt n f x := fun _ _ hf =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hf
  obtain ⟨U, y, hy⟩ := exists_isDerivationGenerator hπ z
  have hzs : z ∈ (complexChartAt (n := n) z).val.source := mem_complexChartAt_source z
  have hyz : HolomorphicAt n y z := hy.holomorphicAt z hy.mem
  set 𝔠 := controlledTransform hπ 𝔞 (μ + 1) with h𝔠
  -- `y^q` generates `𝒪_Y(-qD)` on `U`
  have hpow : ∀ q, ∀ p ∈ U, ∀ g, (idealPow (exceptionalDivisor hπ).ideal q).mem p g ↔
      IsInSpanAt (n := n) (· = fun p => y p ^ q) p g :=
    idealPow_mem_iff_of_generator hy.holomorphicAt hy.generates
  have hpow_self : ∀ q, (idealPow (exceptionalDivisor hπ).ideal q).mem z (fun p => y p ^ q) :=
    fun q => (hpow q z hy.mem _).mpr (isInSpanAt_of_eq_mul rfl (holomorphicAt_pow hyz q)
      (holomorphicAt_const 1) (Eventually.of_forall fun p => by simp))
  -- Claim C: `s ∘ π = y^{μ+1} H` with `H ∈ σ^c(𝔞, μ + 1)`
  have hC : ∀ s, 𝔞.mem (π z) s → ∃ H, 𝔠.mem z H ∧
      (fun p => s (π p)) =ᶠ[𝓝 z] fun p => y p ^ (μ + 1) * H p := by
    intro s hs
    have hshol : HolomorphicAt n (fun p => s (π p)) z :=
      (h𝔞hol _ _ hs).comp_contMDiff (Eventually.of_forall fun p => hπs p)
    have h1 : (GermIdeal.pullback (m := n) π 𝔞).mem z (fun p => s (π p)) :=
      comp_mem_pullback hs hshol (holomorphicAt_const 1) (Eventually.of_forall fun p => by simp)
    have h2 := pullback_le_idealPow_exceptionalDivisor hπ hle z _ h1
    obtain ⟨-, H, hH, hHeq⟩ := isInSpanAt_eq_iff.mp ((hpow (μ + 1) z hy.mem _).mp h2)
    refine ⟨H, ⟨hH, fun ℓ hℓ => ?_⟩, ?_⟩
    · obtain ⟨hℓh, d, hd, hℓd⟩ := isInSpanAt_eq_iff.mp ((hpow (μ + 1) z hy.mem ℓ).mp hℓ)
      refine comp_mem_pullback hs (hℓh.mul hH) hd ?_
      filter_upwards [hℓd, hHeq] with p hp1 hp2
      simp only [hp1, hp2]
      ring
    · filter_upwards [hHeq] with p hp
      rw [hp]; ring
  -- Claim B: generators of `𝓓(𝔞)` at `π z`
  have hB : ∀ s, DerivGen 𝔞 (π z) s → ∃ K, (derivIdeal 𝔠).mem z K ∧
      (fun p => y p * s (π p)) =ᶠ[𝓝 z] fun p => y p ^ (μ + 1) * K p := by
    rintro s (hs | ⟨e', v, f, hx', hf, rfl⟩)
    · obtain ⟨H, hH, hHeq⟩ := hC s hs
      refine ⟨fun p => y p * H p, isInSpanAt_of_eq_mul (Or.inl hH) (hyz.mul hH.1) hyz
        (Eventually.of_forall fun p => rfl), ?_⟩
      filter_upwards [hHeq] with p hp
      rw [hp]; ring
    · obtain ⟨H, hH, hHeq⟩ := hC f hf
      obtain ⟨b, hb, hbeq, ρ, hρ, hρeq⟩ := hy.derivation f (h𝔞hol _ _ hf) e' hx' v
      set ez := complexChartAt (n := n) z with hez
      -- `∂ₘ(f ∘ π) = (μ+1) y^μ ∂ₘy H + y^{μ+1} ∂ₘH` near `z`
      have hfπ : f ∘ π =ᶠ[𝓝 z] fun p => y p ^ (μ + 1) * H p := hHeq
      have hD : ∀ m, chartDeriv ez (EuclideanSpace.single m 1) (f ∘ π) =ᶠ[𝓝 z] fun p =>
          ((μ : ℂ) + 1) * y p ^ μ * chartDeriv ez (EuclideanSpace.single m 1) y p * H p +
            y p ^ (μ + 1) * chartDeriv ez (EuclideanSpace.single m 1) H p := fun m => by
        have h1 := chartDeriv_congr (e := ez) (v := EuclideanSpace.single m 1) hzs hfπ
        have h2 := chartDeriv_eventuallyEq_sum_mul (e := ez) (v := EuclideanSpace.single m 1)
          (N := 1) (f := fun p => y p ^ (μ + 1) * H p) (a := fun _ => fun p => y p ^ (μ + 1))
          (s := fun _ => H) hzs (fun _ => holomorphicAt_pow hyz (μ + 1)) (fun _ => hH.1)
          (Eventually.of_forall fun p => by simp)
        filter_upwards [h1, h2, chartDeriv_pow (v := EuclideanSpace.single m 1) hzs hyz μ]
          with p hp1 hp2 hp3
        simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at hp2
        rw [hp1, hp2, hp3]
      refine ⟨fun p => ((μ : ℂ) + 1) * ρ p * H p +
        ∑ m, b m p * chartDeriv ez (EuclideanSpace.single m 1) H p, ?_, ?_⟩
      · refine RelativePrincipalizationSpan.IsInSpanAt.add ?_ ?_
        · exact isInSpanAt_of_eq_mul (Or.inl hH)
            (((holomorphicAt_const _).mul hρ).mul hH.1) ((holomorphicAt_const _).mul hρ)
            (Eventually.of_forall fun p => rfl)
        · refine RelativePrincipalizationSpan.IsInSpanAt.sum _ fun m _ => ?_
          exact isInSpanAt_of_eq_mul (Or.inr ⟨ez, EuclideanSpace.single m 1, H, hzs, hH, rfl⟩)
            ((hb m).mul (holomorphicAt_chartDeriv hzs hH.1)) (hb m)
            (Eventually.of_forall fun p => rfl)
      · filter_upwards [hbeq, hρeq, eventually_all.2 hD] with p hp1 hp2 hp3
        rw [hp1]
        simp only [hp3, mul_add, Finset.sum_add_distrib]
        have e1 : ∑ m, b m p * (((μ : ℂ) + 1) * y p ^ μ *
            chartDeriv ez (EuclideanSpace.single m 1) y p * H p) =
            ((μ : ℂ) + 1) * y p ^ μ * H p *
              ∑ m, b m p * chartDeriv ez (EuclideanSpace.single m 1) y p := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
        have e2 : ∑ m, b m p * (y p ^ (μ + 1) * chartDeriv ez (EuclideanSpace.single m 1) H p) =
            y p ^ (μ + 1) * ∑ m, b m p * chartDeriv ez (EuclideanSpace.single m 1) H p := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
        rw [e1, e2, hp2]
        ring
  -- Claim A: elements of `𝓓(𝔞)` at `π z`
  have hA : ∀ t, (derivIdeal 𝔞).mem (π z) t → ∃ K, (derivIdeal 𝔠).mem z K ∧
      (fun p => y p * t (π p)) =ᶠ[𝓝 z] fun p => y p ^ (μ + 1) * K p := by
    intro t ht
    obtain ⟨-, N, s, a, hs, ha, hsum⟩ := ht
    choose K hK hKeq using fun i => hB (s i) (hs i)
    refine ⟨fun p => ∑ i, a i (π p) * K i p, ?_, ?_⟩
    · refine RelativePrincipalizationSpan.IsInSpanAt.sum _ fun i _ => ?_
      exact RelativePrincipalizationSpan.IsInSpanAt.mul_left
        ((ha i).comp_contMDiff (Eventually.of_forall fun p => hπs p)) (hK i)
    · filter_upwards [hπc.eventually hsum, eventually_all.2 hKeq] with p hp1 hp2
      rw [hp1, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [show y p * (a i (π p) * s i (π p)) = a i (π p) * (y p * s i (π p)) by ring, hp2 i]
        ring
  -- the main computation
  obtain ⟨hgh, hgall⟩ := hg
  have hyg := hgall _ (hpow_self μ)
  obtain ⟨-, N, s, c, hs, hc, hsum⟩ := (show IsInSpanAt (n := n)
    (fun t => ∃ a, (derivIdeal 𝔞).mem (π z) a ∧ t = a ∘ π) z (fun p => y p ^ μ * g p) from hyg)
  choose t ht hst using hs
  choose K hK hKeq using fun i => hA (t i) (ht i)
  have hsumK : (derivIdeal 𝔠).mem z (fun p => ∑ i, c i p * K i p) :=
    RelativePrincipalizationSpan.IsInSpanAt.sum _ fun i _ =>
      RelativePrincipalizationSpan.IsInSpanAt.mul_left (hc i) (hK i)
  have hcanc : g =ᶠ[𝓝 z] fun p => ∑ i, c i p * K i p := by
    refine eventuallyEq_of_pow_mul_eventuallyEq hy.isOpen hy.mem hy.exists_ne_zero (μ + 1)
      (hgh.eventually.mono fun p hp => hp.continuousAt)
      (hsumK.1.eventually.mono fun p hp => hp.continuousAt) ?_
    filter_upwards [hsum, eventually_all.2 hKeq] with p hp1 hp2
    have : y p ^ (μ + 1) * g p = y p * (y p ^ μ * g p) := by ring
    rw [this, hp1, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hst i, Function.comp_apply,
      show y p * (c i p * t i (π p)) = c i p * (y p * t i (π p)) by ring, hp2 i]
    ring
  exact isInSpanAt_congr hsumK hcanc.symm

/-- **Giraud--Villamayor, `le:inclusions`** (Włodarczyk 2005): for a coherent `𝔞 ⊆ 𝓘_C^{μ+r}`,
`σ^c(𝓓^r(𝔞), μ) ⊆ 𝓓^r(σ^c(𝔞, μ + r))`. -/
theorem controlledTransform_iterDerivIdeal_le (hπ : IsBlowupAlong n C π) {𝔞 : GermIdeal n X}
    (h𝔞 : 𝔞.IsCoherent) :
    ∀ (r μ : ℕ), 𝔞.Le (idealPow (vanishingIdeal (n := n) C) (μ + r)) →
      (controlledTransform hπ (iterDerivIdeal 𝔞 r) μ).Le
        (iterDerivIdeal (controlledTransform hπ 𝔞 (μ + r)) r)
  | 0, μ, _ => fun _ _ h => h
  | r + 1, μ, hle => by
    have hC : ∀ y g, (vanishingIdeal (n := n) C).mem y g → HolomorphicAt n g y := fun _ _ h => h.1
    have h1 : (iterDerivIdeal 𝔞 r).Le (idealPow (vanishingIdeal (n := n) C) (μ + 1)) :=
      iterDerivIdeal_le_idealPow hC r (by rwa [show μ + 1 + r = μ + (r + 1) by omega])
    have h2 := controlledTransform_derivIdeal_le hπ (isCoherent_iterDerivIdeal h𝔞 r) h1
    have h3 := controlledTransform_iterDerivIdeal_le hπ h𝔞 r (μ + 1)
      (by rwa [show μ + 1 + r = μ + (r + 1) by omega])
    rw [show μ + 1 + r = μ + (r + 1) by omega] at h3
    intro z g hg
    exact derivIdeal_mono h3 z g (h2 z g hg)

/-- **Villamayor**: the controlled transform of a coherent marked ideal of maximal order `(𝔞, μ)`
along a blowup with `𝔞 ⊆ 𝓘_C^μ` is of maximal order. -/
theorem _root_.Hironaka.MaximalContact.IsMaximalOrder.controlledTransform
    (hπ : IsBlowupAlong n C π) {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ}
    (hmax : MaximalContact.IsMaximalOrder 𝔞 μ)
    (hle : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) μ)) :
    MaximalContact.IsMaximalOrder (controlledTransform hπ 𝔞 μ) μ := by
  intro z
  have h := controlledTransform_iterDerivIdeal_le hπ h𝔞 μ 0 (by rwa [Nat.zero_add])
  rw [Nat.zero_add] at h
  refine h z _ ⟨holomorphicAt_const 1, fun ℓ hℓ => ?_⟩
  have hℓh : HolomorphicAt n ℓ z := hℓ
  exact comp_mem_pullback (s := fun _ => 1) (hmax (π z)) (hℓh.mul (holomorphicAt_const 1)) hℓh
    (Eventually.of_forall fun p => rfl)

/-- **Villamayor**, with the hypothesis of the source: the centre lies in the cosupport
(`C ⊆ cosupp(𝔞, μ)`, via TN-CLASSICAL's Hadamard bridge). -/
theorem _root_.Hironaka.MaximalContact.IsMaximalOrder.controlledTransform_of_subset_cosupport
    (hπ : IsBlowupAlong n C π) {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ}
    (hmax : MaximalContact.IsMaximalOrder 𝔞 μ) (hsub : C ⊆ cosupport n univ 𝔞 μ) :
    MaximalContact.IsMaximalOrder (controlledTransform hπ 𝔞 μ) μ :=
  hmax.controlledTransform hπ h𝔞
    (HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport h𝔞 hπ.1 hsub)

/-- `le:inclusions` with the hypothesis of the source, `C ⊆ cosupp(𝔞, μ + r)`. -/
theorem controlledTransform_iterDerivIdeal_le_of_subset_cosupport (hπ : IsBlowupAlong n C π)
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) {r μ : ℕ} (hsub : C ⊆ cosupport n univ 𝔞 (μ + r)) :
    (controlledTransform hπ (iterDerivIdeal 𝔞 r) μ).Le
      (iterDerivIdeal (controlledTransform hπ 𝔞 (μ + r)) r) :=
  controlledTransform_iterDerivIdeal_le hπ h𝔞 r μ
    (HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport h𝔞 hπ.1 hsub)

end Blowup


end

end Hironaka.BlowupDerivativeIdeal
