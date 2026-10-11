/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.OrderInvariance
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.DerivativeIdealInvariance

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSmoothPullbackDerivatives
open Hironaka.HolomorphicIdealSheaves
open DerivativeIdeal GermIdealOrder OrderInvariance InvertibleIdealQuotient HadamardBridge
open Hironaka
noncomputable section
variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
 {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ComplexModel m) M'] [IsComplexManifold m M']
section ChainRule

variable {φ : M' → M} (e : ComplexChart n M) (e' : ComplexChart m M') {y : M'}

/-- The map `φ` in the charts `e'` (source) and `e` (target) is holomorphic near `e' y`. -/
theorem eventually_differentiableAt_chartMap
    (hφ : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) φ p)
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
    ((hφ _).comp z (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel m)) e'.property hz))

/-- The coefficient of the chain rule: the `j`-th coordinate of `D(e ∘ φ ∘ e'⁻¹)(e' p) v`. -/
def chainCoeff (φ : M' → M) (v : ComplexModel m) (j : Fin n) : M' → ℂ :=
  fun p => fderiv ℂ (e.val ∘ φ ∘ e'.val.symm) (e'.val p) v j

/-- The coefficients of the chain rule are holomorphic. -/
theorem holomorphicAt_chainCoeff
    (hφ : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) φ p)
    (hy' : y ∈ e'.val.source) (hy : φ y ∈ e.val.source) (v : ComplexModel m) (j : Fin n) :
    HolomorphicAt m (chainCoeff e e' φ v j) y := by
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
    (hφ : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) φ p)
    (hy' : y ∈ e'.val.source) (hy : φ y ∈ e.val.source) {f : M → ℂ} (hf : HolomorphicAt n f (φ y))
    (v : ComplexModel m) :
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

omit [IsComplexManifold m M'] in
/-- A pulled-back germ of `𝓓(𝔞)` is a generator of `φ^*𝓓(𝔞)`, hence in its span. -/
theorem isInSpanAt_comp_of_mem_derivIdeal
    (hφ : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) φ p) {y : M'}
    {a : M → ℂ} (ha : (derivIdeal 𝔞).mem (φ y) a) :
    IsInSpanAt (n := m) (fun s => ∃ b, (derivIdeal 𝔞).mem (φ y) b ∧ s = b ∘ φ) y (a ∘ φ) :=
  InvertibleIdealQuotient.isInSpanAt_self ⟨a, ha, rfl⟩
    (holomorphicAt_comp_map (Eventually.of_forall hφ) ha.1)

/-- **`𝓓(φ^*𝔞) ⊆ φ^*𝓓(𝔞)`** for every holomorphic map `φ` (chain rule). -/
theorem derivIdeal_pullback_le
    (hφ : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) φ p)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    (derivIdeal (GermIdeal.pullback (m := m) φ 𝔞)).Le
      (GermIdeal.pullback (m := m) φ (derivIdeal 𝔞)) := by
  intro y g hg
  refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
    (RelativePrincipalizationSpan.IsInSpanAt.trans ?_ hg)
  have hφev : ∀ᶠ w in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) φ w :=
    Eventually.of_forall hφ
  rintro s (hs | ⟨e', v, f, hy, hf, rfl⟩)
  · -- a germ of `φ^*𝔞` is a combination of pullbacks of germs of `𝔞 ⊆ 𝓓(𝔞)`
    exact (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hs).mono
      fun t ⟨a, ha, ht⟩ => ⟨a, le_derivIdeal h𝔞 _ a ha, ht⟩
  · obtain ⟨-, K, r, c, hr, hc, hsum⟩ := RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hf
    choose a ha hra using hr
    have hahol : ∀ k, HolomorphicAt n (a k) (φ y) := fun k => h𝔞 _ _ (ha k)
    have hrhol : ∀ k, HolomorphicAt m (r k) y := fun k => by
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


end Pullback

theorem iterDerivIdeal_pullback_le {φ : M' → M} {I : GermIdeal n M}
    (hφ : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) φ p)
    (hI : ∀ x g, I.mem x g → HolomorphicAt n g x) :
    ∀ r, (iterDerivIdeal (GermIdeal.pullback (m := m) φ I) r).Le
      (GermIdeal.pullback (m := m) φ (iterDerivIdeal I r))
  | 0 => fun _ _ h => h
  | r + 1 => by
      exact fun x g hg => derivIdeal_pullback_le hφ
        (fun x g hg => holomorphicAt_of_mem_iterDerivIdeal hI r x g hg) x g
        (derivIdeal_mono (iterDerivIdeal_pullback_le hφ hI r) x g hg)

end
end Hironaka.HironakaSmoothPullbackDerivatives
