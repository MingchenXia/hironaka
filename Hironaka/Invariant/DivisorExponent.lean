/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Invariant.OrderMultiplicativity
import Hironaka.Analytic.GermOrderProduct
import Hironaka.Analytic.HolomorphicAnalytic
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.HolomorphicTaylorTail
import Hironaka.Analytic.IdealPowers
import Hironaka.Invariant.OrderTaylor
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Exponents of an ideal along a submanifold

* `eventually_eq_zero_of_forall_mem_idealPow`: a germ lying in every power `𝔪_x^q` vanishes near `x` (Krull, from
  the power series); hence the exponent is finite when `𝔞_x` contains a germ that does not vanish near `x`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.DivisorExponent

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder Hironaka.DerivativeIdeal Hironaka.HolomorphicTaylorTail Hironaka.OrderTaylor Hironaka.BlowupFlatCoordinates Hironaka.HadamardBridge Hironaka.HadamardBridgeAlong Hironaka.IdealOrderArithmetic Hironaka.GiraudAlong Hironaka.OrderMultiplicativity Hironaka.GermOrderProduct Hironaka.HolomorphicAnalytic

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Krull: a germ of infinite order vanishes -/

section Krull

/-- **A germ lying in every power of `𝔪_x` vanishes near `x`** (its Taylor series is zero). -/
theorem eventually_eq_zero_of_forall_mem_idealPow {x : M} {g : M → ℂ} (hg : HolomorphicAt n g x)
    (h : ∀ q, (idealPow (pointIdeal n x) q).mem x g) : g =ᶠ[𝓝 x] fun _ => 0 := by
  set e := complexChartAt (n := n) x
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  set G := g ∘ e.val.symm
  have hall : ∀ j, iteratedFDeriv ℂ j G (e.val x) = 0 := fun j =>
    (mem_idealPow_pointIdeal_iff_iteratedFDeriv hg (j + 1)).mp (h (j + 1)) j (Nat.lt_succ_self j)
  obtain ⟨U, hU, hUo, hpU⟩ := eventually_nhds_iff.mp (eventually_differentiableAt_comp_symm e hxe hg)
  have hGan : AnalyticAt ℂ G (e.val x) :=
    analyticOnNhd_of_differentiableOn hUo (fun z hz => (hU z hz).differentiableWithinAt) _ hpU
  obtain ⟨p, r, hp⟩ := hGan
  -- `G (e x + y) = ∑ (j!)⁻¹ D^j G (e x) (y, …, y) = 0` for small `y`
  have hzero : ∀ᶠ y in 𝓝 (0 : ComplexModel n), G (e.val x + y) = 0 := by
    filter_upwards [Metric.eball_mem_nhds (0 : ComplexModel n) hp.r_pos] with y hy
    have hs := hp.hasSum_iteratedFDeriv hy
    simp only [hall, zero_apply, smul_zero] at hs
    exact hs.unique hasSum_zero
  have hT : Tendsto (fun p => e.val p - e.val x) (𝓝 x) (𝓝 0) := by
    have := ((e.val.continuousAt hxe).tendsto).sub_const (e.val x)
    simpa using this
  filter_upwards [hT.eventually hzero, e.val.open_source.mem_nhds hxe] with p hp hpe
  have : g p = G (e.val x + (e.val p - e.val x)) := by
    simp [G, e.val.left_inv hpe]
  rw [this, hp]

/-- A germ that does not vanish near `x` lies outside some power of `𝔪_x`. -/
theorem exists_notMem_idealPow_of_frequently {x : M} {g : M → ℂ} (hg : HolomorphicAt n g x)
    (hne : ∃ᶠ y in 𝓝 x, g y ≠ 0) : ∃ q, ¬ (idealPow (pointIdeal n x) q).mem x g := by
  by_contra! h
  exact hne ((eventually_eq_zero_of_forall_mem_idealPow hg h).mono fun _ hy hy' => hy' hy)

end Krull

/-! ### Powers of the ideal of a submanifold -/

section Powers

variable {C : Set M}

/-- Germs of `𝓘_C^μ` at `x` are germs of `𝓘_C^μ` at every point near `x`. -/
theorem eventually_mem_idealPow_vanishingIdeal {x : M} {g : M → ℂ} :
    ∀ {μ : ℕ}, (idealPow (vanishingIdeal (n := n) C) μ).mem x g →
      ∀ᶠ y in 𝓝 x, (idealPow (vanishingIdeal (n := n) C) μ).mem y g
  | 0, h => h.eventually_nhds
  | μ + 1, h => by
    obtain ⟨hghol, K, r, c, hr, hc, hsum⟩ := mem_idealPow_succ_iff.mp h
    choose a b ha hb hab using hr
    have hev : ∀ᶠ y in 𝓝 x, ∀ k, (idealPow (vanishingIdeal (n := n) C) μ).mem y (a k) ∧
        (vanishingIdeal (n := n) C).mem y (b k) ∧ HolomorphicAt n (c k) y := by
      refine eventually_all.mpr fun k => ?_
      filter_upwards [eventually_mem_idealPow_vanishingIdeal (ha k), (hb k).1.eventually_nhds,
        (hb k).2.eventually_nhds, (hc k).eventually_nhds] with y h1 h2 h3 h4
      exact ⟨h1, ⟨h2, h3⟩, h4⟩
    filter_upwards [hev, hghol.eventually_nhds, hsum.eventually_nhds] with y hy hgy hsumy
    exact mem_idealPow_succ_iff.mpr ⟨hgy, K, r, c, fun k => ⟨a k, b k, (hy k).1, (hy k).2.1, hab k⟩,
      fun k => (hy k).2.2, hsumy⟩

/-- Powers are monotone in the ideal. -/
theorem idealPow_le_idealPow {I J : GermIdeal n M} (h : I.Le J) : ∀ k, (idealPow I k).Le (idealPow J k)
  | 0 => fun _ _ hg => hg
  | k + 1 => fun y _ hg => mem_idealPow_succ_iff.mpr ((mem_idealPow_succ_iff.mp hg).mono
      fun _ ⟨a, b, ha, hb, hs⟩ => ⟨a, b, idealPow_le_idealPow h k y a ha, h y b hb, hs⟩)

/-- At a point `z ∈ C`, `𝓘_C^μ ⊆ 𝔪_z^μ`. -/
theorem mem_idealPow_pointIdeal_of_mem_idealPow_vanishingIdeal {z : M} (hz : z ∈ C) {g : M → ℂ} {μ : ℕ}
    (h : (idealPow (vanishingIdeal (n := n) C) μ).mem z g) : (idealPow (pointIdeal n z) μ).mem z g :=
  idealPow_le_idealPow (I := vanishingIdeal (n := n) C) (J := pointIdeal n z)
    (fun _ _ hs => ⟨hs.1, hs.2.mono fun _ hw hwz => hw (hwz ▸ hz)⟩) μ z g h

end Powers

/-! ### The Taylor criterion in flat coordinates, without retraction -/

section FlatUniv

variable {x : M} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}

/-- With `k = n` the retraction is the identity: the flattened function is `f ∘ φ`. -/
theorem flatten_univ (f : M → ℂ) (w : ComplexModel n) : flatten Φ n f w = f (flatInv Φ w) := by
  simp only [flatten, planeRetract_of_mem (k := n) (w := w) fun i hi => absurd hi (not_le.mpr i.2)]

/-- Every point is in `univ`, and every vector is in `ℂⁿ × 0`. -/
theorem flat_univ {y : M} (_ : y ∈ (chartAt (ComplexModel n) x).source)
    (_ : chartAt (ComplexModel n) x y ∈ Φ.source) :
    y ∈ (univ : Set M) ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n n :=
  ⟨fun _ i hi => absurd hi (not_le.mpr i.2), fun _ => mem_univ y⟩

variable (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
  (hΦx : Φ.toFun (chartAt (ComplexModel n) x x) = 0)

include hΦsrc in
/-- At a point `z` of the flat domain, the derivatives of order `< μ` of `f ∘ φ` vanish at `ψ z` when
`f ∈ 𝔪_z^μ`. -/
theorem iterDeriv_flatten_univ_eq_zero {z : M} (hz : z ∈ flatDomain Φ) {f : M → ℂ} {μ : ℕ}
    (hf : (idealPow (pointIdeal n z) μ).mem z f) (L : List (ComplexModel n)) (hL : L.length < μ) :
    iterDeriv L (flatten Φ n f) (flatMap Φ z) = 0 :=
  iterDeriv_flatten_flatMap_eq_zero (N := univ) hΦsrc flat_univ hz (mem_univ z)
    (vanishesToOrderOn_of_mem hf) L hL

variable {C : Set M} {k : ℕ}
  (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Φ.source →
    (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))

include hΦsrc hΦx hflat in
/-- **Taylor criterion for `𝓘_C^μ`**: if the derivatives of order `< μ` of `f ∘ φ` vanish on `ℂᵏ × 0` near `0`, then
`f ∈ 𝓘_C^μ` at the centre. -/
theorem mem_idealPow_vanishingIdeal_of_iterDeriv {f : M → ℂ} (hf : HolomorphicAt n f x) {μ : ℕ}
    (hvan : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ complexCoordinatePlane n k →
      ∀ L : List (ComplexModel n), L.length < μ → iterDeriv L (flatten Φ n f) w = 0) :
    (idealPow (vanishingIdeal (n := n) C) μ).mem x f := by
  have hq : (0 : ComplexModel n) ∈ complexCoordinatePlane n k := fun _ _ => rfl
  have hF : InNormalPow k 0 μ (flatten Φ n f) :=
    inNormalPow_of_iterDeriv_eq_zero μ hq (eventually_differentiableAt_flatten hΦsrc hΦx n hf) hvan
  have hψx : flatMap Φ x = 0 := hΦx
  have hψ : ∀ᶠ p in 𝓝 x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (flatMap Φ) p := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with p hp
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Φ.toFun
        (chartAt (ComplexModel n) x p) :=
      (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hp.2)).mdifferentiableAt
    exact h1.comp p (mdifferentiableAt_chart hp.1)
  have hψI : ∀ i : Fin n, k ≤ i.1 → (vanishingIdeal (n := n) C).mem x (fun p => flatMap Φ p i) :=
    fun i hi => flatCoord_mem_vanishingIdeal Φ hflat hi (mem_flatDomain_self Φ)
  refine mem_idealPow_of_inNormalPow hψx hψ hψI μ hF ?_
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with p hp
  rw [flatten_univ, flatInv_flatMap hp]

end FlatUniv

/-- **The Hadamard bridge, local form for one germ**: if `C` is a submanifold at `x` and `f ∈ 𝔪_z^μ` at the points
`z ∈ C` near `x`, then `f ∈ 𝓘_C^μ` at `x`. -/
theorem mem_idealPow_vanishingIdeal_of_eventually {C : Set M} {x : M} {k : ℕ}
    (hC : RegularAtDim (n := n) C x k) {f : M → ℂ} (hf : HolomorphicAt n f x) {μ : ℕ}
    (hsub : ∀ᶠ z in 𝓝 x, z ∈ C → (idealPow (pointIdeal n z) μ).mem z f) :
    (idealPow (vanishingIdeal (n := n) C) μ).mem x f := by
  obtain ⟨-, -, Φ, hΦsrc, hΦx, hflat⟩ := hC
  refine mem_idealPow_vanishingIdeal_of_iterDeriv hΦsrc hΦx hflat hf ?_
  have hT : Tendsto (flatInv Φ) (𝓝 0) (𝓝 x) := by
    have h := (continuousAt_flatInv (zero_mem_target hΦx) hΦsrc).tendsto
    rwa [flatInv_zero hΦx] at h
  filter_upwards [Φ.isOpen_target.mem_nhds (zero_mem_target hΦx), hT.eventually hsub]
    with w hw hwf hwk L hL
  have h := iterDeriv_flatten_univ_eq_zero hΦsrc (flatInv_mem_flatDomain hw hΦsrc)
    (hwf (flatInv_mem hΦsrc hflat hw hwk)) L hL
  rwa [flatMap_flatInv hw hΦsrc] at h

/-! ### Divisibility near a point and the exponent -/

/-- A function holomorphic on an open set is holomorphic at each of its points. -/
theorem holomorphicAt_of_mdifferentiableOn_open {U : Set M} (hUo : IsOpen U) {g : M → ℂ}
    (hg : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g U) {y : M} (hy : y ∈ U) : HolomorphicAt n g y :=
  eventually_of_mem (hUo.mem_nhds hy) fun w hw => (hg w hw).mdifferentiableAt (hUo.mem_nhds hw)

section Exponent

variable {𝔞 : GermIdeal n M} {H : Set M}

/-- **Identity principle along a submanifold, for one germ**: let `C` be a submanifold at `x` and `f` holomorphic at
`x`. If the points `y ∈ C` near which `f ∈ 𝔪_z^e` at every `z ∈ C` accumulate at `x`, then `f ∈ 𝓘_C^e` at `x`. -/
theorem mem_idealPow_vanishingIdeal_of_frequently {C : Set M} {x : M} {k : ℕ}
    (hC : RegularAtDim (n := n) C x k) {f : M → ℂ} (hf : HolomorphicAt n f x) {e : ℕ}
    (h : ∃ᶠ y in 𝓝 x, y ∈ C ∧ ∀ᶠ z in 𝓝 y, z ∈ C → (idealPow (pointIdeal n z) e).mem z f) :
    (idealPow (vanishingIdeal (n := n) C) e).mem x f := by
  obtain ⟨-, -, Φ, hΦsrc, hΦx, hflat⟩ := hC
  refine mem_idealPow_vanishingIdeal_of_iterDeriv hΦsrc hΦx hflat hf ?_
  set F := flatten Φ n f
  set P := planeRetract (n := n) k
  -- a ball `B` around `0` inside the target on which `F` is holomorphic
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((eventually_differentiableAt_flatten hΦsrc hΦx n hf).and
      (Φ.isOpen_target.mem_nhds (zero_mem_target hΦx)))
  set B := Metric.ball (0 : ComplexModel n) r
  have hFB : DifferentiableOn ℂ F B := fun w hw => (hball w hw).1.differentiableWithinAt
  -- a point `y ∈ C` near `x` where the vanishing holds, with `ψ y ∈ B`
  have hψT : Tendsto (flatMap Φ) (𝓝 x) (𝓝 0) := by
    have h1 : ContinuousAt (flatMap Φ) x :=
      ((Φ.toFun_holomorphic.differentiableAt
        (Φ.isOpen_source.mem_nhds Φ.center_mem_source)).continuousAt).comp
        ((chartAt (ComplexModel n) x).continuousAt (mem_chart_source _ x))
    have h2 : flatMap Φ x = 0 := hΦx
    rw [ContinuousAt, h2] at h1
    exact h1
  have hD' : ∀ᶠ y in 𝓝 x, y ∈ flatDomain Φ := (isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)
  have hB' : ∀ᶠ y in 𝓝 x, flatMap Φ y ∈ Metric.ball (0 : ComplexModel n) r :=
    hψT.eventually (Metric.ball_mem_nhds 0 hr)
  obtain ⟨y, ⟨hyC, hyd⟩, hyD, hyB⟩ := (h.and_eventually (hD'.and hB')).exists
  set z₀ := flatMap Φ y
  have hz₀k : z₀ ∈ complexCoordinatePlane n k := (mem_iff_flatMap_mem hflat hyD).mp hyC
  have hPz₀ : P z₀ = z₀ := planeRetract_of_mem hz₀k
  have hz₀T : z₀ ∈ Φ.target := flatMap_mem_target hyD
  have hPT : Tendsto P (𝓝 z₀) (𝓝 z₀) := by
    have := P.continuous.tendsto z₀
    rwa [hPz₀] at this
  have hφT : Tendsto (fun u => flatInv Φ (P u)) (𝓝 z₀) (𝓝 y) := by
    have h1 := (continuousAt_flatInv hz₀T hΦsrc).tendsto
    rw [flatInv_flatMap hyD] at h1
    exact h1.comp hPT
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hr) fun w hwB hwk L hL => ?_
  -- `G = D ∘ P` with `D` the derivative along `L`
  have hD : DifferentiableOn ℂ (iterDeriv L F) B := differentiableOn_iterDeriv hFB Metric.isOpen_ball L
  set Q := P ⁻¹' B
  have hQo : IsOpen Q := Metric.isOpen_ball.preimage P.continuous
  have hG : AnalyticOnNhd ℂ (fun u => iterDeriv L F (P u)) Q :=
    analyticOnNhd_of_differentiableOn hQo (hD.comp P.differentiableOn fun _ hu => hu)
  have hQc : IsPreconnected Q := by
    have hlin : IsLinearMap ℝ P := ⟨P.map_add, fun c u => P.map_smul_of_tower c u⟩
    exact ((convex_ball (0 : ComplexModel n) r).is_linear_preimage hlin).isPreconnected
  have hz₀Q : z₀ ∈ Q := by
    change P z₀ ∈ B
    rw [hPz₀]
    exact hyB
  -- `G` vanishes near `z₀`
  have hG0 : (fun u => iterDeriv L F (P u)) =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hPT.eventually (Φ.isOpen_target.mem_nhds hz₀T), hφT.eventually hyd] with u hu hφd
    have hsm := hφd (flatInv_mem hΦsrc hflat hu (planeRetract_mem k u))
    have h0 := iterDeriv_flatten_univ_eq_zero hΦsrc (flatInv_mem_flatDomain hu hΦsrc) hsm L hL
    rw [flatMap_flatInv hu hΦsrc] at h0
    exact h0
  have hEq := hG.eqOn_zero_of_preconnected_of_eventuallyEq_zero hQc hz₀Q hG0
  have hPw : P w = w := planeRetract_of_mem hwk
  have hwQ : w ∈ Q := by
    change P w ∈ B
    rw [hPw]
    exact hwB
  have := hEq hwQ
  simp only [Pi.zero_apply, hPw] at this
  exact this

end Exponent

end

end Hironaka.DivisorExponent
