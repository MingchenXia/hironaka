import Hironaka.Analytic.OrderInvariance

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Derivative ideals commute with pullback by biholomorphisms

Blueprint `hir:derivative-chain-rule`, `hir:derivative-invariance` (`blueprint/src/hironaka.tex`, Hironaka
phase H1).  Sources: Włodarczyk 2005 §2.4 (functoriality of the derivative ideals and of the invariants under
étale maps, here biholomorphisms), Bierstone--Milman 2008 §3.2 (`𝓓(𝓘)` is intrinsic: the image of
`Der × 𝓘 → 𝒪`).

* `chartDeriv_comp_eventuallyEq_sum` (**chain rule**): for a holomorphic map `φ : M' → M`, charts `e'` at `y` and
  `e` at `φ y`, the partial derivative of `f ∘ φ` in `e'` is near `y` the combination
  `∑ⱼ cⱼ · (∂ⱼ^e f) ∘ φ` with holomorphic coefficients `cⱼ` (entries of the Jacobian of `e ∘ φ ∘ e'⁻¹`).
* `derivIdeal_pullback_le`: `𝓓(φ^*𝔞) ⊆ φ^*𝓓(𝔞)` for every holomorphic `φ`;
* `pullback_derivIdeal` (**invariance**): `φ^*𝓓(𝔞) = 𝓓(φ^*𝔞)` for a biholomorphism `φ`, and
  `pullback_iterDerivIdeal`: `φ^*𝓓^j(𝔞) = 𝓓^j(φ^*𝔞)`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.DerivativeIdealInvariance

open Hironaka.HolomorphicIdealSheaves
open Hironaka.DerivativeIdeal Hironaka.IdealOrderArithmetic
  Hironaka.HadamardBridge

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-! ### The chain rule in charts -/

section ChainRule

variable {φ : M' → M} (e : ComplexChart n M) (e' : ComplexChart n M') {y : M'}

/-- The map `φ` in the charts `e'` (source) and `e` (target) is holomorphic near `e' y`. -/
theorem eventually_differentiableAt_chartMap
    (hφ : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p)
    (hy' : y ∈ e'.val.source) (hy : φ y ∈ e.val.source) :
    ∀ᶠ z in 𝓝 (e'.val y), DifferentiableAt ℂ (e.val ∘ φ ∘ e'.val.symm) z := by
  have hT : Tendsto e'.val.symm (𝓝 (e'.val y)) (𝓝 y) := by
    have := e'.val.continuousAt_symm (e'.val.map_source hy')
    rwa [ContinuousAt, e'.val.left_inv hy'] at this
  have hφT : Tendsto (φ ∘ e'.val.symm) (𝓝 (e'.val y)) (𝓝 (φ y)) :=
    ((hφ y).continuousAt.tendsto).comp hT
  filter_upwards [e'.val.open_target.mem_nhds (e'.val.map_source hy'),
    hφT.eventually (e.val.open_source.mem_nhds hy)] with z hz hze
  rw [← mdifferentiableAt_iff_differentiableAt]
  exact (mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) e.property hze).comp z
    ((hφ _).comp z (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e'.property hz))

/-- The coefficient of the chain rule: the `j`-th coordinate of `D(e ∘ φ ∘ e'⁻¹)(e' p) v`. -/
def chainCoeff (φ : M' → M) (v : ComplexModel n) (j : Fin n) : M' → ℂ :=
  fun p => fderiv ℂ (e.val ∘ φ ∘ e'.val.symm) (e'.val p) v j

/-- The coefficients of the chain rule are holomorphic. -/
theorem holomorphicAt_chainCoeff
    (hφ : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p)
    (hy' : y ∈ e'.val.source) (hy : φ y ∈ e.val.source) (v : ComplexModel n) (j : Fin n) :
    HolomorphicAt n (chainCoeff e e' φ v j) y := by
  obtain ⟨U, hU, hUo, hyU⟩ :=
    eventually_nhds_iff.mp (eventually_differentiableAt_chartMap e e' hφ hy' hy)
  have hd : DifferentiableOn ℂ (e.val ∘ φ ∘ e'.val.symm) U :=
    fun z hz => (hU z hz).differentiableWithinAt
  have hd' := Hironaka.differentiableOn_fderiv_apply_of_isOpen hd hUo v
  refine holomorphicAt_comp_chart e' (W := fun z => fderiv ℂ (e.val ∘ φ ∘ e'.val.symm) z v j) hy' ?_
  filter_upwards [hUo.mem_nhds hyU] with z hz
  have hlin : DifferentiableAt ℂ (fun w : ComplexModel n => w j)
      (fderiv ℂ (e.val ∘ φ ∘ e'.val.symm) z v) :=
    (EuclideanSpace.proj (𝕜 := ℂ) j).differentiableAt
  exact hlin.comp z ((hd' z hz).differentiableAt (hUo.mem_nhds hz))

/-- **Chain rule in charts**: near `y`, `∂_v^{e'}(f ∘ φ) = ∑ⱼ cⱼ · (∂ⱼ^e f) ∘ φ`. -/
theorem chartDeriv_comp_eventuallyEq_sum
    (hφ : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p)
    (hy' : y ∈ e'.val.source) (hy : φ y ∈ e.val.source) {f : M → ℂ} (hf : HolomorphicAt n f (φ y))
    (v : ComplexModel n) :
    chartDeriv e' v (f ∘ φ) =ᶠ[𝓝 y] fun p =>
      ∑ j, chainCoeff e e' φ v j p * chartDeriv e (EuclideanSpace.single j 1) f (φ p) := by
  have hφc : ContinuousAt φ y := (hφ y).continuousAt
  filter_upwards [hφc.eventually hf.eventually_nhds, e'.val.open_source.mem_nhds hy',
    hφc.eventually (e.val.open_source.mem_nhds hy)] with p hfp hpe' hpe
  have hT := (eventually_differentiableAt_chartMap (y := p) e e' hφ hpe' hpe).self_of_nhds
  have hF : DifferentiableAt ℂ (f ∘ e.val.symm) ((e.val ∘ φ ∘ e'.val.symm) (e'.val p)) := by
    simp only [Function.comp_apply, e'.val.left_inv hpe']
    exact (eventually_differentiableAt_comp_symm e hpe hfp).self_of_nhds
  have hloc : (f ∘ φ) ∘ e'.val.symm =ᶠ[𝓝 (e'.val p)] (f ∘ e.val.symm) ∘ (e.val ∘ φ ∘ e'.val.symm) := by
    have hTc : Tendsto e'.val.symm (𝓝 (e'.val p)) (𝓝 p) := by
      have := e'.val.continuousAt_symm (e'.val.map_source hpe')
      rwa [ContinuousAt, e'.val.left_inv hpe'] at this
    have hφp : Tendsto (φ ∘ e'.val.symm) (𝓝 (e'.val p)) (𝓝 (φ p)) :=
      ((hφ p).continuousAt.tendsto).comp hTc
    filter_upwards [hφp.eventually (e.val.open_source.mem_nhds hpe)] with z hz
    simp only [Function.comp_apply] at hz ⊢
    rw [e.val.left_inv hz]
  simp only [chartDeriv]
  rw [hloc.fderiv_eq, fderiv_comp _ hF hT, ContinuousLinearMap.comp_apply]
  simp only [Function.comp_apply, e'.val.left_inv hpe']
  conv_lhs => rw [← sum_smul_single (fderiv ℂ (e.val ∘ φ ∘ e'.val.symm) (e'.val p) v)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul]
  simp only [chainCoeff]

end ChainRule

/-! ### Derivative ideals under pullback -/

section Pullback

variable {φ : M' → M} {𝔞 : GermIdeal n M}

/-- A pulled-back germ of `𝓓(𝔞)` is a generator of `φ^*𝓓(𝔞)`, hence in its span. -/
theorem isInSpanAt_comp_of_mem_derivIdeal
    (hφ : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p) {y : M'}
    {a : M → ℂ} (ha : (derivIdeal 𝔞).mem (φ y) a) :
    IsInSpanAt (n := n) (fun s => ∃ b, (derivIdeal 𝔞).mem (φ y) b ∧ s = b ∘ φ) y (a ∘ φ) :=
  InvertibleIdealQuotient.isInSpanAt_self ⟨a, ha, rfl⟩
    (holomorphicAt_comp_map (Eventually.of_forall hφ) ha.1)

/-- **`𝓓(φ^*𝔞) ⊆ φ^*𝓓(𝔞)`** for every holomorphic map `φ` (chain rule). -/
theorem derivIdeal_pullback_le
    (hφ : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    (derivIdeal (GermIdeal.pullback (m := n) φ 𝔞)).Le
      (GermIdeal.pullback (m := n) φ (derivIdeal 𝔞)) := by
  intro y g hg
  refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
    (RelativePrincipalizationSpan.IsInSpanAt.trans ?_ (mem_derivIdeal_iff.mp hg))
  have hφev : ∀ᶠ w in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ w :=
    Eventually.of_forall hφ
  rintro s (hs | ⟨e', v, f, hy, hf, rfl⟩)
  · -- a germ of `φ^*𝔞` is a combination of pullbacks of germs of `𝔞 ⊆ 𝓓(𝔞)`
    exact (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hs).mono
      fun t ⟨a, ha, ht⟩ => ⟨a, le_derivIdeal h𝔞 _ a ha, ht⟩
  · obtain ⟨-, K, r, c, hr, hc, hsum⟩ := RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hf
    choose a ha hra using hr
    have hahol : ∀ k, HolomorphicAt n (a k) (φ y) := fun k => h𝔞 _ _ (ha k)
    have hrhol : ∀ k, HolomorphicAt n (r k) y := fun k => by
      rw [hra k]
      exact holomorphicAt_comp_map hφev (hahol k)
    set e := complexChartAt (n := n) (φ y)
    have hey : φ y ∈ e.val.source := mem_complexChartAt_source (φ y)
    have hprod := chartDeriv_eventuallyEq_sum_mul (e := e') (v := v) hy hc hrhol hsum
    have hchain : ∀ k, chartDeriv e' v (r k) =ᶠ[𝓝 y] fun p =>
        ∑ j, chainCoeff e e' φ v j p * chartDeriv e (EuclideanSpace.single j 1) (a k) (φ p) := by
      intro k
      rw [hra k]
      exact chartDeriv_comp_eventuallyEq_sum e e' hφ hy hey (hahol k) v
    have hexp : (fun p => ∑ k, (chartDeriv e' v (c k) p * (a k ∘ φ) p +
        ∑ j, c k p * chainCoeff e e' φ v j p *
          (chartDeriv e (EuclideanSpace.single j 1) (a k) ∘ φ) p)) =ᶠ[𝓝 y] chartDeriv e' v f := by
      filter_upwards [hprod, eventually_all.2 hchain] with p hp hp'
      rw [hp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hp' k, hra k, Finset.mul_sum]
      simp only [Function.comp_apply]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    refine isInSpanAt_congr ?_ hexp
    refine RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun k _ => ?_
    refine RelativePrincipalizationSpan.IsInSpanAt.add ?_
      (RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun j _ => ?_)
    · exact RelativePrincipalizationSpan.IsInSpanAt.mul_left
        (holomorphicAt_chartDeriv (v := v) hy (hc k))
        (isInSpanAt_comp_of_mem_derivIdeal hφ (le_derivIdeal h𝔞 _ _ (ha k)))
    · exact RelativePrincipalizationSpan.IsInSpanAt.mul_left
        ((hc k).mul (holomorphicAt_chainCoeff e e' hφ hy hey v j))
        (isInSpanAt_comp_of_mem_derivIdeal hφ (chartDeriv_mem_derivIdeal h𝔞 hey (ha k)))

/-- **`φ^*𝓓(𝔞) ⊆ 𝓓(φ^*𝔞)`** for a biholomorphism `φ` (chain rule for the inverse `ψ`). -/
theorem pullback_derivIdeal_le {ψ : M → M'}
    (hφ : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p)
    (hψ : ∀ x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ x)
    (hφψ : ∀ x, φ (ψ x) = x) (hψφ : ∀ p, ψ (φ p) = p)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    (GermIdeal.pullback (m := n) φ (derivIdeal 𝔞)).Le
      (derivIdeal (GermIdeal.pullback (m := n) φ 𝔞)) := by
  intro y g hg
  have hφev : ∀ᶠ w in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ w :=
    Eventually.of_forall hφ
  have hpb : ∀ {b : M → ℂ}, 𝔞.mem (φ y) b →
      (GermIdeal.pullback (m := n) φ 𝔞).mem y (b ∘ φ) := fun {b} hb =>
    RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
      (InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ a, 𝔞.mem (φ y) a ∧ s = a ∘ φ)
        ⟨b, hb, rfl⟩ (holomorphicAt_comp_map hφev (h𝔞 _ _ hb)))
  refine mem_derivIdeal_iff.mpr (RelativePrincipalizationSpan.IsInSpanAt.trans ?_
    (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg))
  rintro s ⟨a, ha, rfl⟩
  -- `a` is a combination of germs of `𝔞` and of their chart derivatives at `x = φ y`
  obtain ⟨-, K, t, c, ht, hc, hsum⟩ := mem_derivIdeal_iff.mp ha
  have hthol : ∀ k, HolomorphicAt n (t k) (φ y) := fun k => by
    rcases ht k with htk | ⟨e, w, f, hx, hf, htk⟩
    · exact h𝔞 _ _ htk
    · rw [htk]; exact holomorphicAt_chartDeriv hx (h𝔞 _ _ hf)
  have hcomp : (a ∘ φ) =ᶠ[𝓝 y] fun p => ∑ k, (c k ∘ φ) p * (t k ∘ φ) p :=
    (hφ y).continuousAt.eventually hsum
  refine isInSpanAt_congr ?_ hcomp.symm
  refine RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun k _ => ?_
  refine RelativePrincipalizationSpan.IsInSpanAt.mul_left (holomorphicAt_comp_map hφev (hc k)) ?_
  rcases ht k with htk | ⟨e, w, f, hx, hf, htk⟩
  · exact le_derivIdeal (fun x g (hg : (GermIdeal.pullback (m := n) φ 𝔞).mem x g) =>
      (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg).holomorphicAt) y _ (hpb htk)
  · -- `∂_w^e f ∘ φ = ∑ⱼ (cⱼ ∘ φ) · ∂ⱼ^{e'} (f ∘ φ)` by the chain rule for `ψ` applied to `f ∘ φ`
    set e' := complexChartAt (n := n) y
    have hey : y ∈ e'.val.source := mem_complexChartAt_source y
    have hψx : ψ (φ y) ∈ e'.val.source := by rw [hψφ]; exact hey
    have hfφ : HolomorphicAt n (f ∘ φ) (ψ (φ y)) := by
      rw [hψφ]; exact holomorphicAt_comp_map hφev (h𝔞 _ _ hf)
    have hchain := chartDeriv_comp_eventuallyEq_sum e' e (φ := ψ) hψ hx hψx hfφ w
    have hfid : (f ∘ φ) ∘ ψ = f := funext fun x => by simp [hφψ x]
    rw [hfid] at hchain
    have hchain' : (t k ∘ φ) =ᶠ[𝓝 y] fun p => ∑ j, (chainCoeff e' e ψ w j ∘ φ) p *
        chartDeriv e' (EuclideanSpace.single j 1) (f ∘ φ) p := by
      rw [htk]
      filter_upwards [(hφ y).continuousAt.eventually hchain] with p hp
      simp only [Function.comp_apply] at hp ⊢
      rw [hp]
      simp only [hψφ]
    refine isInSpanAt_congr ?_ hchain'.symm
    refine RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun j _ => ?_
    have hcoef : HolomorphicAt n (chainCoeff e' e ψ w j ∘ φ) y :=
      holomorphicAt_comp_map hφev (holomorphicAt_chainCoeff e' e hψ hx hψx w j)
    have hgen : DerivGen (GermIdeal.pullback (m := n) φ 𝔞) y
        (chartDeriv e' (EuclideanSpace.single j 1) (f ∘ φ)) :=
      Or.inr ⟨e', _, f ∘ φ, hey, hpb hf, rfl⟩
    exact isInSpanAt_mul_of_mem hgen hcoef
      (holomorphicAt_chartDeriv hey (holomorphicAt_comp_map hφev (h𝔞 _ _ hf)))

/-- **Derivative ideals commute with pullback by a biholomorphism**: `φ^*𝓓(𝔞) = 𝓓(φ^*𝔞)`. -/
theorem pullback_derivIdeal {ψ : M → M'}
    (hφ : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p)
    (hψ : ∀ x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ x)
    (hφψ : ∀ x, φ (ψ x) = x) (hψφ : ∀ p, ψ (φ p) = p)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    GermIdeal.pullback (m := n) φ (derivIdeal 𝔞) = derivIdeal (GermIdeal.pullback (m := n) φ 𝔞) :=
  GermIdeal.ext (funext fun y => funext fun g => propext
    ⟨pullback_derivIdeal_le hφ hψ hφψ hψφ h𝔞 y g, derivIdeal_pullback_le hφ h𝔞 y g⟩)

/-- **Iterated derivative ideals commute with pullback by a biholomorphism**: `φ^*𝓓^j(𝔞) = 𝓓^j(φ^*𝔞)`. -/
theorem pullback_iterDerivIdeal {ψ : M → M'}
    (hφ : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p)
    (hψ : ∀ x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ x)
    (hφψ : ∀ x, φ (ψ x) = x) (hψφ : ∀ p, ψ (φ p) = p)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    ∀ j : ℕ, GermIdeal.pullback (m := n) φ (iterDerivIdeal 𝔞 j) =
      iterDerivIdeal (GermIdeal.pullback (m := n) φ 𝔞) j
  | 0 => rfl
  | j + 1 => by
      rw [iterDerivIdeal_succ, iterDerivIdeal_succ,
        pullback_derivIdeal hφ hψ hφψ hψφ (holomorphicAt_of_mem_iterDerivIdeal h𝔞 j),
        pullback_iterDerivIdeal hφ hψ hφψ hψφ h𝔞 j]

end Pullback

end

end Hironaka.DerivativeIdealInvariance
