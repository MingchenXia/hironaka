/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent
import Hironaka.MarkedIdeal.DerivativeIdealInvariance
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Manifold.ComplexManifold
import Hironaka.Manifold.HolomorphicContDiff
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The derivative ideal along a submanifold is étale-local

Source: Włodarczyk 2005, Lemmas ``le:etale2'' / ``le:etale3'' (derivative ideals commute with étale maps), here for
the derivative ideal `𝓓_N` along a submanifold and for local biholomorphisms.

Let `φ : M' → M` be holomorphic and a local biholomorphism: near every `y` it has a holomorphic local inverse `ψ`
(`ψ ∘ φ = id` near `y`, `φ ∘ ψ = id` near `φ y`, `ψ` holomorphic near `φ y`).  Then for every ideal `𝔞` of holomorphic germs
and every set `N ⊆ M`,

  `φ^*(𝓓_N 𝔞) = 𝓓_{φ⁻¹N}(φ^*𝔞)`  (`pullback_derivIdealAlong`),  and  `φ^*(𝓓_N^j 𝔞) = 𝓓_{φ⁻¹N}^j(φ^*𝔞)`.

The two cases used later are biholomorphisms (`pullback_derivIdealAlong_of_inverse`) and inclusions of open sets
(`pullback_val_derivIdealAlong`, with the local inverse `openInv U y` of `Subtype.val`).

## Proof

A holomorphic vector field `ξ` near `φ y` (written in a chart `e`) is transferred to the field `ξ'` near `y` (in a chart `e'`)
with coefficients `ξ'_j = ∑_m (ξ_m ∘ φ) · (c_{mj} ∘ φ)`, `c` the Jacobian of `ψ` in the charts (`transferField`), so that
`ξ'(g) = (ξ(g ∘ ψ)) ∘ φ` near `y` (`fieldDeriv_transfer`, the chain rule for `ψ`).  Tangency transfers: `g ↦ g ∘ ψ` maps
`𝓘_{φ⁻¹N}` at `y` into `𝓘_N` at `φ y` (`isTangentField_transfer`).  Generators of `𝓓_N 𝔞` at `φ y` pulled back by `φ` are
generators of `𝓓_{φ⁻¹N}(φ^*𝔞)` at `y`; conversely, by the product rule a generator `ξ'(f')` of the right side, `f' = ∑ cₖ (bₖ ∘ φ)`,
is a combination of the `bₖ ∘ φ` and of the `ξ'(bₖ ∘ φ) = (ξ(bₖ)) ∘ φ` for the field `ξ` transferred back along `ψ`, tangent to
`ψ⁻¹φ⁻¹N`, which agrees with `N` near `φ y`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.DerivativeIdealAlongEtale

open Hironaka.HolomorphicIdealSheaves
open Hironaka.DerivativeIdeal Hironaka.DerivativeIdealAlong Hironaka.DerivativeIdealInvariance Hironaka.HadamardBridge Hironaka.DerivativeIdealAlongCoherent Hironaka.RelativePrincipalizationSpan

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-! ### Elementary facts on fields and vanishing ideals -/

section Elementary

/-- Derivatives along a vector field only depend on the germ. -/
theorem fieldDeriv_congr {e : ComplexChart n M} {ξ : Fin n → M → ℂ} {f g : M → ℂ} {x : M}
    (hx : x ∈ e.val.source) (hfg : f =ᶠ[𝓝 x] g) : fieldDeriv e ξ f =ᶠ[𝓝 x] fieldDeriv e ξ g := by
  filter_upwards [eventually_all.2 fun m =>
    chartDeriv_congr (v := EuclideanSpace.single m (1 : ℂ)) hx hfg] with p hp
  simp only [fieldDeriv, hp]

/-- The vanishing ideal at `x` only depends on the set near `x`. -/
theorem vanishingIdeal_mem_congr {A B : Set M} {x : M} (hAB : ∀ᶠ q in 𝓝 x, q ∈ A ↔ q ∈ B) {g : M → ℂ}
    (hg : (vanishingIdeal (n := n) A).mem x g) : (vanishingIdeal (n := n) B).mem x g := by
  refine ⟨hg.1, ?_⟩
  filter_upwards [hg.2, hAB] with q hq hq' hqB
  exact hq (hq'.mpr hqB)

/-- Tangency at `x` only depends on the set near `x`. -/
theorem isTangentField_congr_set {A B : Set M} {e : ComplexChart n M} {ξ : Fin n → M → ℂ} {x : M}
    (h : IsTangentField A e ξ x) (hAB : ∀ᶠ q in 𝓝 x, q ∈ A ↔ q ∈ B) : IsTangentField B e ξ x := by
  have hBA : ∀ᶠ q in 𝓝 x, q ∈ B ↔ q ∈ A := hAB.mono fun _ h => h.symm
  exact ⟨h.mem_source, h.holomorphicAt, fun g hg =>
    vanishingIdeal_mem_congr hAB (h.preserves g (vanishingIdeal_mem_congr hBA hg))⟩

end Elementary

/-! ### The chain rule for maps holomorphic near a point -/

section ChainLocal

variable {φ : M' → M} (e : ComplexChart n M) (e' : ComplexChart n M') {y : M'}

/-- The map `φ` in the charts `e'` and `e` is holomorphic near `e' y` (`φ` holomorphic near `y`). -/
theorem eventually_differentiableAt_chartMap_of_eventually
    (hφ : ∀ᶠ p in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p)
    (hy' : y ∈ e'.val.source) (hy : φ y ∈ e.val.source) :
    ∀ᶠ z in 𝓝 (e'.val y), DifferentiableAt ℂ (e.val ∘ φ ∘ e'.val.symm) z := by
  have hT : Tendsto e'.val.symm (𝓝 (e'.val y)) (𝓝 y) := by
    have := e'.val.continuousAt_symm (e'.val.map_source hy')
    rwa [ContinuousAt, e'.val.left_inv hy'] at this
  have hφT : Tendsto (φ ∘ e'.val.symm) (𝓝 (e'.val y)) (𝓝 (φ y)) :=
    (hφ.self_of_nhds.continuousAt.tendsto).comp hT
  filter_upwards [e'.val.open_target.mem_nhds (e'.val.map_source hy'),
    hφT.eventually (e.val.open_source.mem_nhds hy), hT.eventually hφ] with z hz hze hzφ
  rw [← mdifferentiableAt_iff_differentiableAt]
  exact (mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) e.property hze).comp z
    (hzφ.comp z (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e'.property hz))

/-- The coefficients of the chain rule are holomorphic (`φ` holomorphic near `y`). -/
theorem holomorphicAt_chainCoeff_of_eventually
    (hφ : ∀ᶠ p in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p)
    (hy' : y ∈ e'.val.source) (hy : φ y ∈ e.val.source) (v : ComplexModel n) (j : Fin n) :
    HolomorphicAt n (chainCoeff e e' φ v j) y := by
  obtain ⟨U, hU, hUo, hyU⟩ :=
    eventually_nhds_iff.mp (eventually_differentiableAt_chartMap_of_eventually e e' hφ hy' hy)
  have hd : DifferentiableOn ℂ (e.val ∘ φ ∘ e'.val.symm) U :=
    fun z hz => (hU z hz).differentiableWithinAt
  have hd' := Hironaka.differentiableOn_fderiv_apply_of_isOpen hd hUo v
  refine holomorphicAt_comp_chart e' (W := fun z => fderiv ℂ (e.val ∘ φ ∘ e'.val.symm) z v j) hy' ?_
  filter_upwards [hUo.mem_nhds hyU] with z hz
  have hlin : DifferentiableAt ℂ (fun w : ComplexModel n => w j)
      (fderiv ℂ (e.val ∘ φ ∘ e'.val.symm) z v) :=
    (EuclideanSpace.proj (𝕜 := ℂ) j).differentiableAt
  exact hlin.comp z ((hd' z hz).differentiableAt (hUo.mem_nhds hz))

/-- **Chain rule in charts** (`φ` holomorphic near `y`): near `y`, `∂_v^{e'}(f ∘ φ) = ∑ⱼ cⱼ · (∂ⱼ^e f) ∘ φ`. -/
theorem chartDeriv_comp_eventuallyEq_sum_of_eventually
    (hφ : ∀ᶠ p in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p)
    (hy' : y ∈ e'.val.source) (hy : φ y ∈ e.val.source) {f : M → ℂ} (hf : HolomorphicAt n f (φ y))
    (v : ComplexModel n) :
    chartDeriv e' v (f ∘ φ) =ᶠ[𝓝 y] fun p =>
      ∑ j, chainCoeff e e' φ v j p * chartDeriv e (EuclideanSpace.single j 1) f (φ p) := by
  have hφc : ContinuousAt φ y := hφ.self_of_nhds.continuousAt
  filter_upwards [hφc.eventually hf.eventually_nhds, e'.val.open_source.mem_nhds hy',
    hφc.eventually (e.val.open_source.mem_nhds hy), hφ.eventually_nhds] with p hfp hpe' hpe hpφ
  have hT := (eventually_differentiableAt_chartMap_of_eventually (y := p) e e' hpφ hpe' hpe).self_of_nhds
  have hF : DifferentiableAt ℂ (f ∘ e.val.symm) ((e.val ∘ φ ∘ e'.val.symm) (e'.val p)) := by
    simp only [Function.comp_apply, e'.val.left_inv hpe']
    exact (eventually_differentiableAt_comp_symm e hpe hfp).self_of_nhds
  have hloc : (f ∘ φ) ∘ e'.val.symm =ᶠ[𝓝 (e'.val p)] (f ∘ e.val.symm) ∘ (e.val ∘ φ ∘ e'.val.symm) := by
    have hTc : Tendsto e'.val.symm (𝓝 (e'.val p)) (𝓝 p) := by
      have := e'.val.continuousAt_symm (e'.val.map_source hpe')
      rwa [ContinuousAt, e'.val.left_inv hpe'] at this
    have hφp : Tendsto (φ ∘ e'.val.symm) (𝓝 (e'.val p)) (𝓝 (φ p)) :=
      (hpφ.self_of_nhds.continuousAt.tendsto).comp hTc
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

end ChainLocal

/-! ### Transfer of vector fields along a local biholomorphism -/

section Transfer

variable (φ : M' → M) (ψ : M → M')

/-- **The field `ξ` near `φ y` transferred to `M'`** (in the chart `e'`): `ξ'_j = ∑_m (ξ_m ∘ φ) · (c_{mj} ∘ φ)`, `c` the
Jacobian of `ψ` in the charts `e` and `e'`. -/
def transferField (e : ComplexChart n M) (e' : ComplexChart n M') (ξ : Fin n → M → ℂ) : Fin n → M' → ℂ :=
  fun j p => ∑ m, ξ m (φ p) * chainCoeff e' e ψ (EuclideanSpace.single m 1) j (φ p)

variable {φ ψ}

variable (n) in
/-- Hypotheses of a local inverse `ψ` of `φ` at `y`. -/
structure IsLocalInverseAt (φ : M' → M) (ψ : M → M') (y : M') : Prop where
  mdiff : ∀ᶠ p in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p
  mdiff_inv : ∀ᶠ q in 𝓝 (φ y), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ q
  left_inv : ∀ᶠ p in 𝓝 y, ψ (φ p) = p
  right_inv : ∀ᶠ q in 𝓝 (φ y), φ (ψ q) = q

variable {y : M'}

/-- The inverse data seen from `φ y`. -/
theorem IsLocalInverseAt.symm (h : IsLocalInverseAt n φ ψ y) : IsLocalInverseAt n ψ φ (φ y) := by
  have hy : ψ (φ y) = y := h.left_inv.self_of_nhds
  refine ⟨h.mdiff_inv, ?_, h.right_inv, ?_⟩
  · rw [hy]; exact h.mdiff
  · rw [hy]; exact h.left_inv

/-- `ψ` maps a neighbourhood of `φ y` into a neighbourhood of `y`. -/
theorem IsLocalInverseAt.tendsto (h : IsLocalInverseAt n φ ψ y) : Tendsto ψ (𝓝 (φ y)) (𝓝 y) := by
  have := h.mdiff_inv.self_of_nhds.continuousAt.tendsto
  rwa [h.left_inv.self_of_nhds] at this

/-- **The transferred field computes the transferred derivative**: `ξ'(g) = (ξ(g ∘ ψ)) ∘ φ` near `y`. -/
theorem fieldDeriv_transfer (h : IsLocalInverseAt n φ ψ y) {e : ComplexChart n M} {e' : ComplexChart n M'}
    (hy' : y ∈ e'.val.source) (hy : φ y ∈ e.val.source) (ξ : Fin n → M → ℂ) {g : M' → ℂ} (hg : HolomorphicAt n g y) :
    fieldDeriv e' (transferField φ ψ e e' ξ) g =ᶠ[𝓝 y] fun p => fieldDeriv e ξ (g ∘ ψ) (φ p) := by
  have hψy : ψ (φ y) = y := h.left_inv.self_of_nhds
  have hg' : HolomorphicAt n g (ψ (φ y)) := by rw [hψy]; exact hg
  have hy'' : ψ (φ y) ∈ e'.val.source := by rw [hψy]; exact hy'
  have hchain : ∀ m, chartDeriv e (EuclideanSpace.single m 1) (g ∘ ψ) =ᶠ[𝓝 (φ y)] fun q =>
      ∑ j, chainCoeff e' e ψ (EuclideanSpace.single m 1) j q * chartDeriv e' (EuclideanSpace.single j 1) g (ψ q) :=
    fun m => chartDeriv_comp_eventuallyEq_sum_of_eventually e' e h.mdiff_inv hy hy'' hg' _
  have hφc : ContinuousAt φ y := h.mdiff.self_of_nhds.continuousAt
  filter_upwards [hφc.eventually (eventually_all.2 hchain), h.left_inv] with p hp hpψ
  simp only [fieldDeriv, transferField, hp, hpψ, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by ring

/-- The transferred field has holomorphic coefficients. -/
theorem holomorphicAt_transferField (h : IsLocalInverseAt n φ ψ y) {e : ComplexChart n M} {e' : ComplexChart n M'}
    (hy' : y ∈ e'.val.source) (hy : φ y ∈ e.val.source) {ξ : Fin n → M → ℂ} (hξ : ∀ m, HolomorphicAt n (ξ m) (φ y))
    (j : Fin n) : HolomorphicAt n (transferField φ ψ e e' ξ j) y := by
  have hψy : ψ (φ y) = y := h.left_inv.self_of_nhds
  refine Hironaka.HolomorphicIdealSheaves.HolomorphicAt.sum _ fun m _ => ?_
  refine (holomorphicAt_comp_map (f := ξ m) h.mdiff (hξ m)).mul
    (holomorphicAt_comp_map (f := chainCoeff e' e ψ (EuclideanSpace.single m 1) j) h.mdiff ?_)
  exact holomorphicAt_chainCoeff_of_eventually e' e h.mdiff_inv hy (by rw [hψy]; exact hy') _ j

/-- `g ↦ g ∘ ψ` maps germs vanishing on `φ⁻¹N` at `y` to germs vanishing on `N` at `φ y`. -/
theorem comp_mem_vanishingIdeal (h : IsLocalInverseAt n φ ψ y) {N : Set M} {g : M' → ℂ}
    (hg : (vanishingIdeal (n := n) (φ ⁻¹' N)).mem y g) : (vanishingIdeal (n := n) N).mem (φ y) (g ∘ ψ) := by
  have hψy : ψ (φ y) = y := h.left_inv.self_of_nhds
  refine ⟨holomorphicAt_comp_map h.mdiff_inv (by rw [hψy]; exact hg.1), ?_⟩
  filter_upwards [h.tendsto.eventually hg.2, h.right_inv] with q hq hqφ hqN
  exact hq (by rw [mem_preimage, hqφ]; exact hqN)

/-- `b ↦ b ∘ φ` maps germs vanishing on `N` at `φ y` to germs vanishing on `φ⁻¹N` at `y`. -/
theorem comp_mem_vanishingIdeal_preimage (h : IsLocalInverseAt n φ ψ y) {N : Set M} {b : M → ℂ}
    (hb : (vanishingIdeal (n := n) N).mem (φ y) b) : (vanishingIdeal (n := n) (φ ⁻¹' N)).mem y (b ∘ φ) := by
  refine ⟨holomorphicAt_comp_map h.mdiff hb.1, ?_⟩
  filter_upwards [h.mdiff.self_of_nhds.continuousAt.eventually hb.2] with p hp hpN
  exact hp hpN

/-- **Tangency transfers**: if `ξ` is tangent to `N` at `φ y`, the transferred field is tangent to `φ⁻¹N` at `y`. -/
theorem isTangentField_transfer (h : IsLocalInverseAt n φ ψ y) {N : Set M} {e : ComplexChart n M}
    {e' : ComplexChart n M'} (hy' : y ∈ e'.val.source) {ξ : Fin n → M → ℂ} (hξ : IsTangentField N e ξ (φ y)) :
    IsTangentField (φ ⁻¹' N) e' (transferField φ ψ e e' ξ) y := by
  refine ⟨hy', fun j => holomorphicAt_transferField h hy' hξ.mem_source hξ.holomorphicAt j, fun g hg => ?_⟩
  have h1 := hξ.preserves _ (comp_mem_vanishingIdeal h hg)
  have h2 := comp_mem_vanishingIdeal_preimage h h1
  have hcongr := fieldDeriv_transfer h hy' hξ.mem_source ξ hg.1
  exact ⟨h2.1.congr hcongr.symm, by
    filter_upwards [h2.2, hcongr] with p hp hpe hpN
    rw [hpe]
    exact hp hpN⟩

end Transfer

/-! ### The derivative ideal along `N` under local biholomorphisms -/

section Pullback

variable {φ : M' → M} {𝔞 : GermIdeal n M} {N : Set M}

/-- Every germ of `𝔞` at `φ y` pulled back is a germ of `φ^*𝔞` at `y`. -/
theorem comp_mem_pullback {y : M'}
    (hφ : ∀ᶠ p in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p)
    {𝔟 : GermIdeal n M} {b : M → ℂ} (hb : 𝔟.mem (φ y) b) (hbhol : HolomorphicAt n b (φ y)) :
    (GermIdeal.pullback (m := n) φ 𝔟).mem y (b ∘ φ) :=
  GermIdeal.mem_pullback_iff.mpr
    (InvertibleIdealQuotient.isInSpanAt_self ⟨b, hb, rfl⟩ (holomorphicAt_comp_map hφ hbhol))

/-- **`φ^*(𝓓_N 𝔞) ⊆ 𝓓_{φ⁻¹N}(φ^*𝔞)`** for a local biholomorphism `φ`. -/
theorem pullback_derivIdealAlong_le
    (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    (GermIdeal.pullback (m := n) φ (derivIdealAlong N 𝔞)).Le
      (derivIdealAlong (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞)) := by
  intro y g hg
  obtain ⟨ψ, hψ⟩ := hloc y
  refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
  rintro s ⟨b, hb, rfl⟩
  obtain ⟨hbhol, K, t, c, ht, hc, hsum⟩ := hb
  have hcomp : (b ∘ φ) =ᶠ[𝓝 y] fun p => ∑ k, (c k ∘ φ) p * (t k ∘ φ) p :=
    hψ.mdiff.self_of_nhds.continuousAt.eventually hsum
  refine DerivativeIdeal.isInSpanAt_congr ?_ hcomp.symm
  refine IsInSpanAt.sum Finset.univ fun k _ => IsInSpanAt.mul_left (holomorphicAt_comp_map hψ.mdiff (hc k)) ?_
  have hgen1 : ∀ {u : M' → ℂ}, DerivGenAlong (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) y u →
      HolomorphicAt n u y →
      IsInSpanAt (n := n) (DerivGenAlong (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) y) y u :=
    fun hu hhu => InvertibleIdealQuotient.isInSpanAt_self hu hhu
  rcases ht k with htk | htk | ⟨e, ξ, f, hξ, hf, htk⟩
  · exact hgen1 (Or.inl (comp_mem_pullback hψ.mdiff htk (h𝔞 _ _ htk)))
      (holomorphicAt_comp_map hψ.mdiff (h𝔞 _ _ htk))
  · have hv := comp_mem_vanishingIdeal_preimage hψ htk
    exact hgen1 (Or.inr (Or.inl hv)) hv.1
  · -- `(ξ f) ∘ φ = ξ'(f ∘ φ)` for the transferred field `ξ'`, tangent to `φ⁻¹N`
    set e' := complexChartAt (n := n) y
    have hy' : y ∈ e'.val.source := mem_complexChartAt_source y
    have hfhol := h𝔞 _ _ hf
    have hfφ : HolomorphicAt n (f ∘ φ) y := holomorphicAt_comp_map hψ.mdiff hfhol
    have htr := fieldDeriv_transfer hψ hy' hξ.mem_source ξ hfφ
    -- `(f ∘ φ) ∘ ψ = f` near `φ y`
    have hfψ : (f ∘ φ) ∘ ψ =ᶠ[𝓝 (φ y)] f := by
      filter_upwards [hψ.right_inv] with q hq
      simp [hq]
    have hloc' := fieldDeriv_congr (ξ := ξ) hξ.mem_source hfψ
    have hloc'' : (fun p => fieldDeriv e ξ ((f ∘ φ) ∘ ψ) (φ p)) =ᶠ[𝓝 y] fun p => fieldDeriv e ξ f (φ p) :=
      hψ.mdiff.self_of_nhds.continuousAt.eventually hloc'
    have heq : fieldDeriv e' (transferField φ ψ e e' ξ) (f ∘ φ) =ᶠ[𝓝 y] t k ∘ φ := by
      filter_upwards [htr, hloc''] with p hp hp'
      rw [hp, hp', htk]
      rfl
    have hgen : DerivGenAlong (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) y
        (fieldDeriv e' (transferField φ ψ e e' ξ) (f ∘ φ)) :=
      Or.inr (Or.inr ⟨e', _, f ∘ φ, isTangentField_transfer hψ hy' hξ, comp_mem_pullback hψ.mdiff hf hfhol, rfl⟩)
    exact DerivativeIdeal.isInSpanAt_congr (hgen1 hgen (holomorphicAt_fieldDeriv hy'
      (fun j => holomorphicAt_transferField hψ hy' hξ.mem_source hξ.holomorphicAt j) hfφ)) heq

/-- **`𝓓_{φ⁻¹N}(φ^*𝔞) ⊆ φ^*(𝓓_N 𝔞)`** for a local biholomorphism `φ`. -/
theorem derivIdealAlong_pullback_le
    (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    (derivIdealAlong (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞)).Le
      (GermIdeal.pullback (m := n) φ (derivIdealAlong N 𝔞)) := by
  intro y g hg
  obtain ⟨ψ, hψ⟩ := hloc y
  have hψy : ψ (φ y) = y := hψ.left_inv.self_of_nhds
  have hDhol : ∀ x g, (derivIdealAlong N 𝔞).mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
  -- generators of the pullback of `𝓓_N 𝔞`
  have hpb : ∀ {b : M → ℂ}, (derivIdealAlong N 𝔞).mem (φ y) b →
      IsInSpanAt (n := n) (fun s => ∃ a, (derivIdealAlong N 𝔞).mem (φ y) a ∧ s = a ∘ φ) y (b ∘ φ) :=
    fun {b} hb => comp_mem_pullback hψ.mdiff hb hb.1
  refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_ hg)
  rintro t (ht | ht | ⟨e', ξ', f', hξ', hf', rfl⟩)
  · -- a germ of `φ^*𝔞`
    exact (GermIdeal.mem_pullback_iff.mp ht).mono fun s ⟨a, ha, hs⟩ =>
      ⟨a, le_derivIdealAlong h𝔞 _ _ ha, hs⟩
  · -- a germ vanishing on `φ⁻¹N`: `t = (t ∘ ψ) ∘ φ` near `y`
    have hv := comp_mem_vanishingIdeal hψ ht
    have heq : (t ∘ ψ) ∘ φ =ᶠ[𝓝 y] t := by
      filter_upwards [hψ.left_inv] with p hp
      simp [hp]
    exact DerivativeIdeal.isInSpanAt_congr (hpb (vanishingIdeal_le_derivIdealAlong _ _ hv)) heq
  · -- `ξ'(f')` with `f' = ∑ cₖ (bₖ ∘ φ)`: product rule and transfer of `ξ'` back to `M`
    obtain ⟨-, K, s, c, hs, hc, hsum⟩ := GermIdeal.mem_pullback_iff.mp hf'
    choose b hb hsb using hs
    have hbhol : ∀ k, HolomorphicAt n (b k) (φ y) := fun k => h𝔞 _ _ (hb k)
    have hsφ : ∀ k, HolomorphicAt n (s k) y := fun k => hsb k ▸ holomorphicAt_comp_map hψ.mdiff (hbhol k)
    have hprod := fieldDeriv_eventuallyEq_sum_mul (ξ := ξ') hξ'.mem_source hc hsφ hsum
    refine DerivativeIdeal.isInSpanAt_congr ?_ hprod.symm
    refine IsInSpanAt.sum Finset.univ fun k _ => IsInSpanAt.add ?_ ?_
    · refine IsInSpanAt.mul_left (holomorphicAt_fieldDeriv hξ'.mem_source hξ'.holomorphicAt (hc k)) ?_
      rw [hsb k]
      exact hpb (le_derivIdealAlong h𝔞 _ _ (hb k))
    · refine IsInSpanAt.mul_left (hc k) ?_
      -- the field `ξ'` transferred to `M` along `ψ`
      set e := complexChartAt (n := n) (φ y)
      have hey : φ y ∈ e.val.source := mem_complexChartAt_source (φ y)
      have hψs := hψ.symm
      have hey' : ψ (φ y) ∈ e'.val.source := by rw [hψy]; exact hξ'.mem_source
      have hξ'' : IsTangentField (φ ⁻¹' N) e' ξ' (ψ (φ y)) := by rw [hψy]; exact hξ'
      set ξ := transferField ψ φ e' e ξ'
      have htan : IsTangentField N e ξ (φ y) := by
        refine isTangentField_congr_set (isTangentField_transfer hψs hey hξ'') ?_
        filter_upwards [hψ.right_inv] with q hq
        simp only [mem_preimage, hq]
      -- `ξ(bₖ) ∘ φ = ξ'(bₖ ∘ φ)` near `y`
      have htr := fieldDeriv_transfer hψs hey hey' ξ' (hbhol k)
      have heq : (fieldDeriv e ξ (b k)) ∘ φ =ᶠ[𝓝 y] fieldDeriv e' ξ' (s k) := by
        have h1 := hψ.mdiff.self_of_nhds.continuousAt.eventually htr
        filter_upwards [h1, hψ.left_inv] with p hp hpψ
        simp only [Function.comp_apply]
        refine hp.trans ?_
        simp only [hpψ, hsb k]
      refine DerivativeIdeal.isInSpanAt_congr (hpb ?_) heq
      exact InvertibleIdealQuotient.isInSpanAt_self (Or.inr (Or.inr ⟨e, ξ, b k, htan, hb k, rfl⟩))
        (holomorphicAt_fieldDeriv hey htan.holomorphicAt (hbhol k))

/-- **The derivative ideal along `N` commutes with pullback by a local biholomorphism**:
`φ^*(𝓓_N 𝔞) = 𝓓_{φ⁻¹N}(φ^*𝔞)`. -/
theorem pullback_derivIdealAlong
    (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    GermIdeal.pullback (m := n) φ (derivIdealAlong N 𝔞) =
      derivIdealAlong (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) :=
  GermIdeal.ext (funext fun y => funext fun g => propext
    ⟨pullback_derivIdealAlong_le hloc h𝔞 y g, derivIdealAlong_pullback_le hloc h𝔞 y g⟩)

/-- **Iterated derivative ideals along `N` commute with pullback by a local biholomorphism**. -/
theorem pullback_iterDerivIdealAlong
    (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    ∀ j : ℕ, GermIdeal.pullback (m := n) φ (iterDerivIdealAlong N 𝔞 j) =
      iterDerivIdealAlong (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) j
  | 0 => rfl
  | j + 1 => by
      show GermIdeal.pullback (m := n) φ (derivIdealAlong N (iterDerivIdealAlong N 𝔞 j)) =
        derivIdealAlong (φ ⁻¹' N) (iterDerivIdealAlong (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) j)
      rw [pullback_derivIdealAlong hloc (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 j),
        pullback_iterDerivIdealAlong hloc h𝔞 j]

end Pullback

/-! ### Biholomorphisms and open sets -/

section Cases

variable {𝔞 : GermIdeal n M} {N : Set M}

/-- A biholomorphism is a local biholomorphism at every point. -/
theorem isLocalInverseAt_of_inverse {φ : M' → M} {ψ : M → M'}
    (hφ : ∀ p, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p)
    (hψ : ∀ x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ x)
    (hφψ : ∀ x, φ (ψ x) = x) (hψφ : ∀ p, ψ (φ p) = p) (y : M') : IsLocalInverseAt n φ ψ y :=
  ⟨Eventually.of_forall hφ, Eventually.of_forall hψ, Eventually.of_forall hψφ, Eventually.of_forall hφψ⟩

variable (U : TopologicalSpace.Opens M)

open Classical in
/-- The local inverse of the inclusion of an open set: the identity on `U`, the constant `y` elsewhere. -/
def openInv (y : U) : M → U := fun q => if h : q ∈ U then ⟨q, h⟩ else y

/-- The inclusion of an open set is a local biholomorphism, with local inverse `openInv`. -/
theorem isLocalInverseAt_val (y : U) : IsLocalInverseAt n (Subtype.val : U → M) (openInv U y) y := by
  have hUy : ∀ᶠ q in 𝓝 (y : M), q ∈ U := U.isOpen.mem_nhds y.2
  refine ⟨Eventually.of_forall fun p =>
      (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel n)) (n := ∞) p).mdifferentiableAt (by simp), ?_,
    Eventually.of_forall fun p => by simp [openInv, p.2], ?_⟩
  · filter_upwards [hUy.eventually_nhds] with q hq
    have hval : (Subtype.val ∘ openInv U y) =ᶠ[𝓝 q] id := by
      filter_upwards [hq] with q' hq'
      simp [openInv, hq']
    have hc : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val ∘ openInv U y) q :=
      contMDiffAt_id.congr_of_eventuallyEq hval
    exact ((ContMDiffAt.subtypeVal_comp_iff U (openInv U y) q).mp hc).mdifferentiableAt (by simp)
  · filter_upwards [hUy] with q hq
    simp [openInv, hq]

/-- **`𝓓_N` commutes with restriction to an open set**: `ι^*(𝓓_N^j 𝔞) = 𝓓_{ι⁻¹N}^j(ι^*𝔞)` for the inclusion `ι` of `U`. -/
theorem pullback_val_iterDerivIdealAlong (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (j : ℕ) :
    GermIdeal.pullback (m := n) (Subtype.val : U → M) (iterDerivIdealAlong N 𝔞 j) =
      iterDerivIdealAlong ((Subtype.val : U → M) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : U → M) 𝔞) j :=
  pullback_iterDerivIdealAlong (fun y => ⟨openInv U y, isLocalInverseAt_val U y⟩) h𝔞 j

end Cases

end

end Hironaka.DerivativeIdealAlongEtale
