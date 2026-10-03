/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupSNCTransform
import Hironaka.MarkedIdeal.CoefficientIdeal
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.HolomorphicTaylorTail
import Hironaka.MarkedIdeal.HomogenizedEquivalence
import Hironaka.MarkedIdeal.HomogenizedIdeal
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The glueing lemma along a submanifold (one stage)

Sources: Włodarczyk 2005, Lemmas `le:homo0` / `le:homo` (the Glueing Lemma); Włodarczyk 2009 (GGT 2008), Lemma
5.5.3; applied on the submanifold `N` of a marked ideal `(M, N, E, 𝔞, μ)` with the derivative ideals `𝓓_N` along `N`
and the homogenized ideal `𝓗_N(𝔞)` of `HomogenizedIdealAlong`.

The analytic glueing lemma for `N = M` compares two tangent directions `u`, `v` through a coordinate change `φ` that
replaces the coordinate `u` by `v`. Along `N` the coordinates must also flatten `N`:

* **Flat charts.** For a flat chart `Θ` of `N` at `x` (a local biholomorphism `Θ` of `ℂⁿ` near `e x` with `N = (Θ ∘
  e)⁻¹(ℂᵏ × 0)` near `x`), the coordinate field `∂/∂Θ_l` (`l < k`) is `GiraudAlong.flatField Θ eₗ`, tangent to `N`;
  hence for `F` with `F ∘ Θ ∘ e ∈ 𝔞_x`, `(∂ₗʲ F) ∘ Θ ∘ e ∈ 𝓓_N^j(𝔞)_x` (`iterDeriv_comp_flatMap_mem`).
* **The coordinate change of a flat chart** (`flatChange`, an instance of `HomogenizedIdeal.CoordinateChange` with
  `W = Θ ∘ e`): `φ(p) = (Θ ∘ e)⁻¹(Θ(e p) + h(p) eᵢ)`.  For `h ∈ T_N(𝔞)_x` with `h(x) = 0` and a tangential index `i < k`
  the **glueing inclusion along `N`** holds: `f ∘ φ ∈ 𝓗_N(𝔞)_x` for `f ∈ 𝔞_x` (`comp_mem_homogenizedIdealAlong`, the convergent
  Taylor tail of `f ∘ (Θ ∘ e)⁻¹` in the direction `eᵢ`), and then `φ^*𝓗_N(𝔞) ⊆ 𝓗_N(𝔞)` at `x`
  (`comp_mem_homogenizedIdealAlong_of_mem`, via `𝓗_N(𝓓_N^i 𝔞, μ - i) · T_N(𝔞)^i ⊆ 𝓗_N(𝔞, μ)` and `𝓗_N(T, 1) = T`).
* **Coordinates adapted to `N` and to a tangent direction** (`alongCoords`): for a flat chart `ψ = Φ ∘ e` of `N`, a vector
  `w ∈ ℂᵏ × 0` and an index `i` with `wᵢ ≠ 0`, `W = P_w ∘ ψ + u eᵢ` (`P_w` the linear projection killing `w` and the
  `i`-th coordinate) keeps the normal coordinates `ψ_r` (`r ≥ k`) and has `u` as `i`-th coordinate; it is a new flat chart of
  `N` at `x` when `d(u ∘ ψ⁻¹)(0) w ≠ 0` (`exists_flatChart_alongCoords`).  For two tangent directions `u`, `v` along `N` a
  common `w` exists (both restricted differentials are nonzero on `ℂᵏ × 0`).

Not here: the statements along multiple test blow-ups (step (4d), after the transforms along `N`, item (2) of
`hir:along-calculus`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HomogenizedGlueingAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.DerivativeIdeal Hironaka.DerivativeIdealAlong Hironaka.GiraudAlong Hironaka.DerivativeIdealAlongCoherent Hironaka.TangentDirectionAlong Hironaka.IdealWeightPowers Hironaka.HomogenizedEquivalence Hironaka.HomogenizedIdealAlong Hironaka.HolomorphicTaylorTail Hironaka.BlowupFlatCoordinates Hironaka.HadamardBridgeAlong Hironaka.RelativePrincipalizationSpan

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### Compositions of derivative ideals along `N` -/

section Iterate

/-- `𝓓_N^j(𝓓_N^i 𝔞) = 𝓓_N^{i+j} 𝔞`. -/
theorem iterDerivIdealAlong_iterDerivIdealAlong (N : Set M) (𝔞 : GermIdeal n M) (i : ℕ) :
    ∀ j, iterDerivIdealAlong N (iterDerivIdealAlong N 𝔞 i) j = iterDerivIdealAlong N 𝔞 (i + j)
  | 0 => rfl
  | j + 1 => by
    show derivIdealAlong N (iterDerivIdealAlong N (iterDerivIdealAlong N 𝔞 i) j) =
      derivIdealAlong N (iterDerivIdealAlong N 𝔞 (i + j))
    rw [iterDerivIdealAlong_iterDerivIdealAlong N 𝔞 i j]

/-- The tangent ideal of `(𝓓_N^i 𝔞, μ - i)` is that of `(𝔞, μ)` (`i < μ`). -/
theorem tangentIdealAlong_iterDerivIdealAlong (N : Set M) (𝔞 : GermIdeal n M) {μ i : ℕ} (hi : i < μ) :
    tangentIdealAlong N (iterDerivIdealAlong N 𝔞 i) (μ - i) = tangentIdealAlong N 𝔞 μ := by
  unfold tangentIdealAlong
  rw [iterDerivIdealAlong_iterDerivIdealAlong]
  congr 1
  omega

/-- **`𝓗_N(𝔟, 1) = 𝔟`** for a coherent `𝔟` (Włodarczyk's Lemma 5.5.1 (1) along `N`). -/
theorem homogenizedIdealAlong_one {N : Set M} {𝔟 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) :
    homogenizedIdealAlong N 𝔟 1 = 𝔟 := by
  refine Eq.trans ?_ (HomogenizedIdeal.homogenizedIdeal_one h𝔟)
  rw [homogenizedIdeal_eq_homSum]
  unfold homogenizedIdealAlong homSum
  exact CoefficientIdeal.finSumIdeal_congr fun i hi => by
    obtain rfl : i = 0 := by omega
    rfl

end Iterate

/-! ### Flat charts: tangential coordinate derivatives -/

section FlatChart

variable {x : M} {Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}
  (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) x).target) {N : Set M} {k : ℕ}
  (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Θ.source →
    (y ∈ N ↔ Θ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))

include hΘsrc in
/-- `(G ∘ ψ) ∘ ψ⁻¹ = G` near `ψ p` (`ψ = Θ ∘ e` the flat coordinates). -/
theorem comp_flatMap_flatInv_eventuallyEq (G : ComplexModel n → ℂ) {p : M} (hp : p ∈ flatDomain Θ) :
    (G ∘ flatMap Θ) ∘ flatInv Θ =ᶠ[𝓝 (flatMap Θ p)] G := by
  filter_upwards [Θ.isOpen_target.mem_nhds (flatMap_mem_target hp)] with z hz
  simp only [Function.comp_apply, flatMap_flatInv hz hΘsrc]

include hΘsrc in
/-- **The derivative along the coordinate field `∂/∂ψ_v`** of `G ∘ ψ` is `(∂_v G) ∘ ψ`. -/
theorem fieldDeriv_flatField_comp {G : ComplexModel n → ℂ} {p : M} (hp : p ∈ flatDomain Θ)
    (hG : HolomorphicAt n (G ∘ flatMap Θ) p) (v : ComplexModel n) :
    fieldDeriv (complexChartAt (n := n) x) (flatField Θ v) (G ∘ flatMap Θ) p = fderiv ℂ G (flatMap Θ p) v := by
  rw [fieldDeriv_flatField hp hG v, (comp_flatMap_flatInv_eventuallyEq hΘsrc G hp).fderiv_eq]

include hΘsrc hflat in
/-- **Iterated tangential coordinate derivatives lie in the iterated derivative ideals along `N`**: for a flat chart
`ψ = Θ ∘ e` of `N` at `x`, a tangential index `l < k` and `F` with `F ∘ ψ ∈ 𝔞_x`, `(∂ₗʲ F) ∘ ψ ∈ 𝓓_N^j(𝔞)_x`. -/
theorem iterDeriv_comp_flatMap_mem {𝔞 : GermIdeal n M} (h𝔞 : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y)
    {l : Fin n} (hl : l.1 < k) {F : ComplexModel n → ℂ} (hFW : 𝔞.mem x (F ∘ flatMap Θ)) :
    ∀ j : ℕ, (iterDerivIdealAlong N 𝔞 j).mem x
      (iterDeriv (List.replicate j (EuclideanSpace.single l (1 : ℂ))) F ∘ flatMap Θ)
  | 0 => hFW
  | j + 1 => by
    set v : ComplexModel n := EuclideanSpace.single l 1 with hv
    have hprev := iterDeriv_comp_flatMap_mem h𝔞 hl hFW j
    have hGW : HolomorphicAt n (iterDeriv (List.replicate j v) F ∘ flatMap Θ) x :=
      holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 j x _ hprev
    have hx0 : x ∈ flatDomain Θ := mem_flatDomain_self Θ
    have hξ : IsTangentField N (complexChartAt (n := n) x) (flatField Θ v) x :=
      isTangentField_flatField hΘsrc hflat (single_mem_complexCoordinatePlane hl) hx0
    have hgen : IsInSpanAt (n := n) (DerivGenAlong N (iterDerivIdealAlong N 𝔞 j) x) x
        (fieldDeriv (complexChartAt (n := n) x) (flatField Θ v) (iterDeriv (List.replicate j v) F ∘ flatMap Θ)) :=
      InvertibleIdealQuotient.isInSpanAt_self (Or.inr (Or.inr ⟨_, _, _, hξ, hprev, rfl⟩))
        (holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt hGW)
    show IsInSpanAt (n := n) (DerivGenAlong N (iterDerivIdealAlong N 𝔞 j) x) x _
    refine DerivativeIdeal.isInSpanAt_congr hgen ?_
    filter_upwards [(isOpen_flatDomain Θ).mem_nhds hx0, hGW.eventually_nhds] with p hp hGp
    rw [fieldDeriv_flatField_comp hΘsrc hp hGp v]
    rfl

/-- The flat coordinates are continuous on the flat domain. -/
theorem continuousAt_flatMap {p : M} (hp : p ∈ flatDomain Θ) : ContinuousAt (flatMap Θ) p :=
  ((Θ.toFun_holomorphic _ hp.2).differentiableAt (Θ.isOpen_source.mem_nhds hp.2)).continuousAt.comp
    ((chartAt (ComplexModel n) x).continuousAt hp.1)

include hΘsrc in
/-- In the chart, the flat coordinates are `Θ`. -/
theorem flatMap_comp_symm_eventuallyEq {ζ : ComplexModel n} (hζ : ζ ∈ Θ.source) :
    (flatMap Θ ∘ (chartAt (ComplexModel n) x).symm) =ᶠ[𝓝 ζ] Θ.toFun := by
  filter_upwards [(chartAt (ComplexModel n) x).open_target.mem_nhds (hΘsrc hζ)] with z hz
  change Θ.toFun ((chartAt (ComplexModel n) x) ((chartAt (ComplexModel n) x).symm z)) = Θ.toFun z
  rw [(chartAt (ComplexModel n) x).right_inv hz]

/-- The differential of a local holomorphic equivalence at its centre is injective. -/
theorem injective_fderiv_toFun :
    Function.Injective (fderiv ℂ Θ.toFun (chartAt (ComplexModel n) x x)) := by
  have hcs : chartAt (ComplexModel n) x x ∈ Θ.source := Θ.center_mem_source
  have hΘd : HasFDerivAt Θ.toFun (fderiv ℂ Θ.toFun (chartAt (ComplexModel n) x x)) (chartAt (ComplexModel n) x x) :=
    (Θ.toFun_holomorphic.differentiableAt (Θ.isOpen_source.mem_nhds hcs)).hasFDerivAt
  have hinvd : HasFDerivAt Θ.invFun (fderiv ℂ Θ.invFun (Θ.toFun (chartAt (ComplexModel n) x x)))
      (Θ.toFun (chartAt (ComplexModel n) x x)) :=
    (Θ.invFun_holomorphic.differentiableAt (Θ.isOpen_target.mem_nhds (Θ.mapsTo_toFun hcs))).hasFDerivAt
  have hid : (Θ.invFun ∘ Θ.toFun) =ᶠ[𝓝 (chartAt (ComplexModel n) x x)] id := by
    filter_upwards [Θ.isOpen_source.mem_nhds hcs] with ζ hζ
    exact Θ.left_inv ζ hζ
  have hcomp := (hinvd.comp (chartAt (ComplexModel n) x x) hΘd).congr_of_eventuallyEq hid.symm
  have hid' := hcomp.unique (hasFDerivAt_id (chartAt (ComplexModel n) x x))
  intro a b hab
  have h1 := congrArg (fun L : ComplexModel n →L[ℂ] ComplexModel n => L a) hid'
  have h2 := congrArg (fun L : ComplexModel n →L[ℂ] ComplexModel n => L b) hid'
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 h2
  rw [← h1, ← h2, hab]

variable (Θ) in
/-- **The coordinate change of a flat chart**: `φ(p) = ψ⁻¹(ψ(p) + h(p) eᵢ)` for the flat coordinates `ψ = Θ ∘ e`, as a
`HomogenizedIdeal.CoordinateChange` (with `W = ψ` and `Ψ = Θ⁻¹`). -/
def flatChange (h : M → ℂ) (hh : HolomorphicAt n h x) (h0 : h x = 0) (i : Fin n) :
    HomogenizedIdeal.CoordinateChange (n := n) x where
  W := flatMap Θ
  N := Θ.source
  isOpen := Θ.isOpen_source
  mem := Θ.center_mem_source
  differentiableOn := fun ζ hζ =>
    (((Θ.toFun_holomorphic ζ hζ).differentiableAt (Θ.isOpen_source.mem_nhds hζ)).congr_of_eventuallyEq
      (flatMap_comp_symm_eventuallyEq hΘsrc hζ)).differentiableWithinAt
  injective := by
    show Function.Injective (fderiv ℂ (flatMap Θ ∘ (chartAt (ComplexModel n) x).symm) (chartAt (ComplexModel n) x x))
    rw [(flatMap_comp_symm_eventuallyEq hΘsrc Θ.center_mem_source).fderiv_eq]
    exact injective_fderiv_toFun
  Ψ := Θ.invFun
  differentiableAt := by
    filter_upwards [Θ.isOpen_target.mem_nhds (flatMap_mem_target (mem_flatDomain_self Θ))] with w hw
    exact (Θ.invFun_holomorphic w hw).differentiableAt (Θ.isOpen_target.mem_nhds hw)
  left_inv := by
    filter_upwards [(isOpen_flatDomain Θ).mem_nhds (mem_flatDomain_self Θ)] with p hp
    exact Θ.left_inv _ hp.2
  h := h
  holomorphicAt := hh
  h_zero := h0
  i := i

theorem flatChange_coordMap (h : M → ℂ) (hh : HolomorphicAt n h x) (h0 : h x = 0) (i : Fin n) (p : M) :
    (flatChange Θ hΘsrc h hh h0 i).coordMap p =
      flatInv Θ (flatMap Θ p + h p • EuclideanSpace.single i 1) := rfl

end FlatChart

/-! ### The glueing inclusion along `N` -/

section Inclusion

variable {x : M} {Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}
  (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) x).target) {N : Set M} {k : ℕ}
  (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Θ.source →
    (y ∈ N ↔ Θ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))

include hΘsrc hflat in
/-- **The glueing inclusion along `N`** (the analytic core of Włodarczyk's `le:homo0` (1) on `N`): let `ψ = Θ ∘ e` be a flat
chart of `N` at `x`, `h ∈ T_N(𝔞)_x = 𝓓_N^{μ-1}(𝔞)_x` with `h(x) = 0`, `i < k` a tangential index, and
`φ(p) = ψ⁻¹(ψ(p) + h(p) eᵢ)`.  Then `f ∘ φ ∈ 𝓗_N(𝔞)_x` for every `f ∈ 𝔞_x`.  Proof: the convergent Taylor tail of
`F = f ∘ ψ⁻¹` in the direction `eᵢ`, with `(∂ᵢʲ F) ∘ ψ ∈ 𝓓_N^j(𝔞)_x` (`iterDeriv_comp_flatMap_mem`). -/
theorem comp_mem_homogenizedIdealAlong {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hμ : 1 ≤ μ)
    {h : M → ℂ} (hh : (tangentIdealAlong N 𝔞 μ).mem x h) (hh0 : h x = 0) {i : Fin n} (hi : i.1 < k)
    {f : M → ℂ} (hf : 𝔞.mem x f) :
    (homogenizedIdealAlong N 𝔞 μ).mem x
      (fun p => f (flatInv Θ (flatMap Θ p + h p • EuclideanSpace.single i 1))) := by
  classical
  set e := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hx0 : x ∈ flatDomain Θ := mem_flatDomain_self Θ
  have hhol : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hfh : HolomorphicAt n f x := hhol x f hf
  have hhh : HolomorphicAt n h x := holomorphicAt_of_mem_iterDerivIdealAlong hhol (μ - 1) x h hh
  set v : ComplexModel n := EuclideanSpace.single i 1 with hv
  set W : M → ComplexModel n := flatMap Θ with hW
  set F : ComplexModel n → ℂ := f ∘ flatInv Θ with hFdef
  have hWc : ContinuousAt W x := continuousAt_flatMap hx0
  -- `F` is holomorphic near `W x`
  have hF : ∀ᶠ w in 𝓝 (W x), DifferentiableAt ℂ F w := by
    have hT : Tendsto (flatInv Θ) (𝓝 (W x)) (𝓝 x) := by
      have := (continuousAt_flatInv (flatMap_mem_target hx0) hΘsrc).tendsto
      rwa [flatInv_flatMap hx0] at this
    filter_upwards [Θ.isOpen_target.mem_nhds (flatMap_mem_target hx0), hT.eventually hfh.eventually_nhds]
      with w hw hfw
    exact differentiableAt_comp_flatInv hw hΘsrc hfw
  -- `F ∘ W = f` near `x`
  have hFW : 𝔞.mem x (F ∘ W) := by
    refine HomogenizedIdeal.mem_congr h𝔞 hf ?_
    filter_upwards [(isOpen_flatDomain Θ).mem_nhds hx0] with p hp
    simp only [hFdef, hW, Function.comp_apply, flatInv_flatMap hp]
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
    have hWd : ∀ᶠ ζ in 𝓝 (e.val x), DifferentiableAt ℂ (W ∘ e.val.symm) ζ := by
      filter_upwards [Θ.isOpen_source.mem_nhds Θ.center_mem_source] with ζ hζ
      exact ((Θ.toFun_holomorphic ζ hζ).differentiableAt (Θ.isOpen_source.mem_nhds hζ)).congr_of_eventuallyEq
        (flatMap_comp_symm_eventuallyEq hΘsrc hζ)
    have hinnerd : ∀ᶠ ζ in 𝓝 (e.val x), DifferentiableAt ℂ inner ζ := by
      filter_upwards [hWd, hhe] with ζ h1 h2
      exact h1.prodMk h2
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
  have hA : ∀ j, (iterDerivIdealAlong N 𝔞 j).mem x (iterDeriv (List.replicate j v) F ∘ W) :=
    iterDeriv_comp_flatMap_mem hΘsrc hflat hhol hi hFW
  have hAh : ∀ j, HolomorphicAt n (iterDeriv (List.replicate j v) F ∘ W) x := fun j =>
    holomorphicAt_of_mem_iterDerivIdealAlong hhol j x _ (hA j)
  set S : (M → ℂ) → Prop := fun s => ∃ j, j < μ ∧
    ((iterDerivIdealAlong N 𝔞 j).mul (idealPow (tangentIdealAlong N 𝔞 μ) j)).mem x s with hS
  have hgen_j : ∀ j ∈ Finset.range μ, S (fun p => (iterDeriv (List.replicate j v) F ∘ W) p * h p ^ j) :=
    fun j hj => ⟨j, Finset.mem_range.mp hj, HomogenizedIdeal.mul_mem_mul (hA j)
      (HomogenizedIdeal.pow_mem_idealPow hh hhh j) ((hAh j).mul (BlowupDerivativeIdeal.holomorphicAt_pow hhh j))⟩
  have hgen_tail : S (fun p => h p * h p ^ (μ - 1)) :=
    ⟨μ - 1, by omega, HomogenizedIdeal.mul_mem_mul hh (HomogenizedIdeal.pow_mem_idealPow hh hhh (μ - 1))
      (hhh.mul (BlowupDerivativeIdeal.holomorphicAt_pow hhh (μ - 1)))⟩
  have hspan : IsInSpanAt (n := n) S x (fun p =>
      ∑ j ∈ Finset.range μ, (j.factorial : ℂ)⁻¹ * ((iterDeriv (List.replicate j v) F ∘ W) p * h p ^ j) +
        G (W p, h p) * (h p * h p ^ (μ - 1))) := by
    refine RelativePrincipalizationSpan.IsInSpanAt.add
      (RelativePrincipalizationSpan.IsInSpanAt.sum _ fun j hj => ?_) ?_
    · exact isInSpanAt_of_eq_mul (hgen_j j hj)
        ((holomorphicAt_const _).mul ((hAh j).mul (BlowupDerivativeIdeal.holomorphicAt_pow hhh j)))
        (holomorphicAt_const _) (Eventually.of_forall fun p => rfl)
    · exact isInSpanAt_of_eq_mul hgen_tail
        (hGγ.mul (hhh.mul (BlowupDerivativeIdeal.holomorphicAt_pow hhh (μ - 1)))) hGγ
        (Eventually.of_forall fun p => rfl)
  show IsInSpanAt (n := n) S x _
  refine DerivativeIdeal.isInSpanAt_congr hspan ?_
  filter_upwards [hexp] with p hp
  have hp' : f (flatInv Θ (W p + h p • v)) =
      ∑ j ∈ Finset.range μ, (j.factorial : ℂ)⁻¹ * iterDeriv (List.replicate j v) F (W p) * h p ^ j +
        h p ^ μ * G (W p, h p) := hp
  have hpow : h p ^ μ = h p * h p ^ (μ - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hp', hpow]
  simp only [Function.comp_apply]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by ring
  · ring

end Inclusion

/-! ### Products with powers of the tangent ideal along `N` -/

section Product

variable {N : Set M} {𝔞 : GermIdeal n M}

/-- **`𝓗_N(𝓓_N^i 𝔞, μ - i) · T_N(𝔞)^i ⊆ 𝓗_N(𝔞, μ)`** (germs at `x`, `i < μ`). -/
theorem mul_mem_homogenizedIdealAlong (h𝔞 : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y) {x : M} {μ i : ℕ}
    (hi : i < μ) {a b : M → ℂ}
    (ha : (homogenizedIdealAlong N (iterDerivIdealAlong N 𝔞 i) (μ - i)).mem x a)
    (hb : (idealPow (tangentIdealAlong N 𝔞 μ) i).mem x b) :
    (homogenizedIdealAlong N 𝔞 μ).mem x (fun p => a p * b p) := by
  set S : (M → ℂ) → Prop := fun s => ∃ j, j < μ ∧
    ((iterDerivIdealAlong N 𝔞 j).mul (idealPow (tangentIdealAlong N 𝔞 μ) j)).mem x s with hS
  have hThol : ∀ y g, (tangentIdealAlong N 𝔞 μ).mem y g → HolomorphicAt n g y :=
    holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 (μ - 1)
  have hbh : HolomorphicAt n b x := holomorphicAt_of_mem_idealPow hb
  have hTT := tangentIdealAlong_iterDerivIdealAlong N 𝔞 hi
  obtain ⟨hah, K, s, c, hs, hc, hsum⟩ := (show IsInSpanAt (n := n) (fun s => ∃ j, j < μ - i ∧
    ((iterDerivIdealAlong N (iterDerivIdealAlong N 𝔞 i) j).mul
      (idealPow (tangentIdealAlong N (iterDerivIdealAlong N 𝔞 i) (μ - i)) j)).mem x s) x a from ha)
  -- each generator `s k ∈ 𝓓_N^j(𝓓_N^i 𝔞) · T^j` times `b ∈ T^i` lies in `𝓗_N(𝔞)`
  have hstep : ∀ k, IsInSpanAt (n := n) S x (fun p => s k p * b p) := by
    intro k
    obtain ⟨j, hj, hsk⟩ := hs k
    rw [hTT] at hsk
    obtain ⟨-, K', t, d', ht, hd', htsum⟩ := (show IsInSpanAt (n := n) (fun t => ∃ a' b',
      (iterDerivIdealAlong N (iterDerivIdealAlong N 𝔞 i) j).mem x a' ∧
      (idealPow (tangentIdealAlong N 𝔞 μ) j).mem x b' ∧ t = a' * b') x (s k) from hsk)
    have hgen : ∀ l, IsInSpanAt (n := n) S x (fun p => d' l p * (t l p * b p)) := by
      intro l
      obtain ⟨a', b', ha', hb', hteq⟩ := ht l
      rw [iterDerivIdealAlong_iterDerivIdealAlong] at ha'
      have ha'h : HolomorphicAt n a' x := holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 (i + j) x a' ha'
      have hb'h : HolomorphicAt n b' x := holomorphicAt_of_mem_idealPow hb'
      have hbb : (idealPow (tangentIdealAlong N 𝔞 μ) (i + j)).mem x (fun p => b' p * b p) := by
        have := mul_mem_idealPow_add hThol hb' hb
        rwa [Nat.add_comm j i] at this
      have hg : S (fun p => a' p * (b' p * b p)) :=
        ⟨i + j, by omega, HomogenizedIdeal.mul_mem_mul ha' hbb (ha'h.mul (hb'h.mul hbh))⟩
      refine isInSpanAt_of_eq_mul hg ((hd' l).mul ((ha'h.mul hb'h).mul hbh |>.congr
        (Eventually.of_forall fun p => by simp only [hteq, Pi.mul_apply]))) (hd' l)
        (Eventually.of_forall fun p => ?_)
      simp only [hteq, Pi.mul_apply]; ring
    refine DerivativeIdeal.isInSpanAt_congr
      (RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun l _ => hgen l) ?_
    filter_upwards [htsum] with p hp
    simp only [hp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  show IsInSpanAt (n := n) S x _
  refine DerivativeIdeal.isInSpanAt_congr (RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ
    fun k _ => RelativePrincipalizationSpan.IsInSpanAt.mul_left (hc k) (hstep k)) ?_
  filter_upwards [hsum] with p hp
  simp only [hp, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

end Product

/-! ### The coordinate change of a flat chart preserves `𝓗_N` -/

section Invariance

variable {x : M} {Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}
  (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) x).target) {N : Set M} {k : ℕ}
  (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Θ.source →
    (y ∈ N ↔ Θ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))
  {h : M → ℂ} (hhol : HolomorphicAt n h x) (h0 : h x = 0) {i : Fin n}

include hflat in
/-- **`T_N(𝔞)^j` is preserved by the coordinate change** (`φ^*(T_N, 1) ⊆ 𝓗_N(T_N, 1) = (T_N, 1)`), for
`h ∈ T_N(𝔞)_x` and a tangential index `i < k` (`𝔞` coherent, `N` a closed submanifold). -/
theorem comp_mem_idealPow_tangentIdealAlong {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N)
    {μ : ℕ} (hi : i.1 < k) (hh : (tangentIdealAlong N 𝔞 μ).mem x h) :
    ∀ j {b : M → ℂ}, (idealPow (tangentIdealAlong N 𝔞 μ) j).mem x b →
      (idealPow (tangentIdealAlong N 𝔞 μ) j).mem x (fun p => b ((flatChange Θ hΘsrc h hhol h0 i).coordMap p))
  | 0, b, hb => (flatChange Θ hΘsrc h hhol h0 i).holomorphicAt_comp hb
  | j + 1, b, hb => by
    set d := flatChange Θ hΘsrc h hhol h0 i with hd
    have hT : (tangentIdealAlong N 𝔞 μ).IsCoherent := isCoherent_tangentIdealAlong h𝔞 hN μ
    have hThol : ∀ y g, (tangentIdealAlong N 𝔞 μ).mem y g → HolomorphicAt n g y := fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hT hg
    have hT1 : (tangentIdealAlong N (tangentIdealAlong N 𝔞 μ) 1).mem x h := hh
    rw [idealPow_succ] at hb ⊢
    show IsInSpanAt (n := n) (fun s => ∃ a b, (idealPow (tangentIdealAlong N 𝔞 μ) j).mem x a ∧
      (tangentIdealAlong N 𝔞 μ).mem x b ∧ s = a * b) x _
    refine d.comp_isInSpanAt (S := fun s => ∃ a b, (idealPow (tangentIdealAlong N 𝔞 μ) j).mem x a ∧
      (tangentIdealAlong N 𝔞 μ).mem x b ∧ s = a * b) hb ?_
    rintro s ⟨a, t, ha, ht, rfl⟩
    have ha' := comp_mem_idealPow_tangentIdealAlong h𝔞 hN hi hh j ha
    have ht' : (tangentIdealAlong N 𝔞 μ).mem x (fun p => t (d.coordMap p)) := by
      have := comp_mem_homogenizedIdealAlong hΘsrc hflat hT le_rfl hT1 h0 hi ht
      rwa [homogenizedIdealAlong_one hT] at this
    exact HomogenizedIdeal.mul_mem_mul ha' ht' ((holomorphicAt_of_mem_idealPow ha').mul (hThol x _ ht'))

include hflat in
/-- **The coordinate change of a flat chart preserves the homogenized ideal along `N` at `x`** (Włodarczyk, Lemma `le:homo0`
(1) along `N`, inclusion `φ^*𝓗_N(𝔞) ⊆ 𝓗_N(𝔞)`): for `h ∈ T_N(𝔞)_x` with `h(x) = 0` and a tangential index `i < k`,
`f ∘ φ ∈ 𝓗_N(𝔞)_x` for every `f ∈ 𝓗_N(𝔞)_x` (`𝔞` coherent, `N` a closed submanifold). -/
theorem comp_mem_homogenizedIdealAlong_of_mem {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N)
    {μ : ℕ} (hi : i.1 < k) (hh : (tangentIdealAlong N 𝔞 μ).mem x h) {f : M → ℂ}
    (hf : (homogenizedIdealAlong N 𝔞 μ).mem x f) :
    (homogenizedIdealAlong N 𝔞 μ).mem x (fun p => f ((flatChange Θ hΘsrc h hhol h0 i).coordMap p)) := by
  set d := flatChange Θ hΘsrc h hhol h0 i with hd
  have hhol𝔞 : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  set S : (M → ℂ) → Prop := fun s => ∃ j, j < μ ∧
    ((iterDerivIdealAlong N 𝔞 j).mul (idealPow (tangentIdealAlong N 𝔞 μ) j)).mem x s with hS
  show IsInSpanAt (n := n) S x _
  refine d.comp_isInSpanAt (S := S) hf ?_
  rintro s ⟨j, hj, hs⟩
  refine d.comp_isInSpanAt (S := fun t => ∃ a b, (iterDerivIdealAlong N 𝔞 j).mem x a ∧
    (idealPow (tangentIdealAlong N 𝔞 μ) j).mem x b ∧ t = a * b) hs ?_
  rintro t ⟨a, b, ha, hb, rfl⟩
  have hh' : (tangentIdealAlong N (iterDerivIdealAlong N 𝔞 j) (μ - j)).mem x h := by
    rw [tangentIdealAlong_iterDerivIdealAlong N 𝔞 hj]; exact hh
  have ha' := comp_mem_homogenizedIdealAlong hΘsrc hflat (isCoherent_iterDerivIdealAlong h𝔞 hN j) (by omega)
    hh' h0 hi ha
  have hb' := comp_mem_idealPow_tangentIdealAlong hΘsrc hflat hhol h0 h𝔞 hN hi hh j hb
  exact mul_mem_homogenizedIdealAlong hhol𝔞 hj ha' hb'

end Invariance

/-! ### Coordinates adapted to `N` and to a tangent direction -/

section Adapted

variable {x : M} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)} {k : ℕ}

variable (Φ) in
/-- **Coordinates adapted to `N` and to `u`**: `W(p) = P_w(ψ p) + u(p) eᵢ` for the flat coordinates `ψ = Φ ∘ e` of `N`,
where `P_w` (`HomogenizedGlueing.killMap w i`) kills `w` and the `i`-th coordinate. -/
def alongCoords (w : ComplexModel n) (i : Fin n) (u : M → ℂ) (p : M) : ComplexModel n :=
  HomogenizedGlueing.killMap w i (flatMap Φ p) + u p • EuclideanSpace.single i 1

/-- The `i`-th adapted coordinate is `u`. -/
theorem alongCoords_apply_self {w : ComplexModel n} {i : Fin n} (hwi : w i ≠ 0) (u : M → ℂ) (p : M) :
    alongCoords Φ w i u p i = u p := by
  simp [alongCoords, HomogenizedGlueing.killMap_apply_self hwi]

/-- For `w ∈ ℂᵏ × 0` and `i < k`, the normal adapted coordinates are the normal flat coordinates. -/
theorem alongCoords_apply_of_le {w : ComplexModel n} (hw : w ∈ complexCoordinatePlane n k) {i : Fin n}
    (hi : i.1 < k) (u : M → ℂ) (p : M) {r : Fin n} (hr : k ≤ r.1) : alongCoords Φ w i u p r = flatMap Φ p r := by
  have hri : r ≠ i := fun h => by subst h; omega
  simp [alongCoords, HomogenizedGlueing.killMap_apply, hw r hr, hri]

/-- **The adapted coordinates flatten `N` like the flat coordinates**: `W(p) ∈ ℂᵏ × 0 ↔ ψ(p) ∈ ℂᵏ × 0`. -/
theorem alongCoords_mem_plane_iff {w : ComplexModel n} (hw : w ∈ complexCoordinatePlane n k) {i : Fin n}
    (hi : i.1 < k) (u : M → ℂ) (p : M) :
    alongCoords Φ w i u p ∈ complexCoordinatePlane n k ↔ flatMap Φ p ∈ complexCoordinatePlane n k := by
  constructor
  · intro h r hr
    rw [← alongCoords_apply_of_le hw hi u p hr]
    exact h r hr
  · intro h r hr
    rw [alongCoords_apply_of_le hw hi u p hr]
    exact h r hr

/-- The adapted coordinates for `u` and for `v` differ only in the `i`-th coordinate. -/
theorem alongCoords_sub (w : ComplexModel n) (i : Fin n) (u v : M → ℂ) (p : M) :
    alongCoords Φ w i v p = alongCoords Φ w i u p + (v p - u p) • EuclideanSpace.single i 1 := by
  simp only [alongCoords, sub_smul]
  abel

/-- The adapted coordinates are holomorphic wherever `u` is, on the flat domain. -/
theorem mdifferentiableAt_alongCoords (w : ComplexModel n) (i : Fin n) {u : M → ℂ} {y : M}
    (hy : y ∈ flatDomain Φ) (hu : HolomorphicAt n u y) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (alongCoords Φ w i u) y := by
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (flatMap Φ) y := by
    have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Φ.toFun
        (chartAt (ComplexModel n) x y) :=
      (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hy.2)).mdifferentiableAt
    exact h2.comp y (mdifferentiableAt_chart hy.1)
  have h3 := (HomogenizedGlueing.killMap w i).differentiableAt.mdifferentiableAt.comp y h1
  have hu' : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) u y := hu.self_of_nhds
  exact h3.add (MDifferentiableAt.smul hu' mdifferentiableAt_const)

/-- `P_w + ℓ ⊗ eᵢ` is injective when `wᵢ ≠ 0` and `ℓ w ≠ 0`. -/
theorem injective_killMap_add {w : ComplexModel n} {i : Fin n} (hwi : w i ≠ 0) {ℓ : ComplexModel n →L[ℂ] ℂ}
    (hℓ : ℓ w ≠ 0) :
    Function.Injective (HomogenizedGlueing.killMap w i + ℓ.smulRight (EuclideanSpace.single i (1 : ℂ))) := by
  rw [injective_iff_map_eq_zero]
  intro ξ hL
  have hLapply : (HomogenizedGlueing.killMap w i + ℓ.smulRight (EuclideanSpace.single i (1 : ℂ))) ξ =
      HomogenizedGlueing.killMap w i ξ + ℓ ξ • EuclideanSpace.single i (1 : ℂ) := by simp
  rw [hLapply] at hL
  have hk := congrArg (fun z : ComplexModel n => z i) hL
  simp [HomogenizedGlueing.killMap_apply_self hwi] at hk
  rw [hk, zero_smul, add_zero] at hL
  have hξw := HomogenizedGlueing.eq_smul_of_killMap_eq_zero hL
  have hc : (w i)⁻¹ * ξ i = 0 := by
    have h0 : ℓ ξ = ((w i)⁻¹ * ξ i) * ℓ w := by
      conv_lhs => rw [hξw]
      rw [map_smul, smul_eq_mul]
    rw [hk] at h0
    exact (mul_eq_zero.mp h0.symm).resolve_right hℓ
  rw [hc, zero_smul] at hξw
  exact hξw

variable (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target) {N : Set M}
  (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Φ.source →
    (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))

include hΦsrc in
/-- **The adapted coordinates are local coordinates at `x`** when the restricted differential of `u` is nonzero on `w`:
`d(u ∘ ψ⁻¹)(ψ x) w ≠ 0` and `wᵢ ≠ 0`. -/
theorem injective_fderiv_alongCoords {w : ComplexModel n} {i : Fin n} (hwi : w i ≠ 0) {u : M → ℂ}
    (hu : HolomorphicAt n u x) (hℓ : fderiv ℂ (u ∘ flatInv Φ) (flatMap Φ x) w ≠ 0) :
    Function.Injective (fderiv ℂ (fun ζ => alongCoords Φ w i u ((chartAt (ComplexModel n) x).symm ζ))
      (chartAt (ComplexModel n) x x)) := by
  have hx0 : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hcs : chartAt (ComplexModel n) x x ∈ Φ.source := Φ.center_mem_source
  have hud : DifferentiableAt ℂ (u ∘ flatInv Φ) (flatMap Φ x) :=
    differentiableAt_comp_flatInv (flatMap_mem_target hx0) hΦsrc (by rw [flatInv_flatMap hx0]; exact hu)
  have hloc : (fun ζ => alongCoords Φ w i u ((chartAt (ComplexModel n) x).symm ζ)) =ᶠ[𝓝 (chartAt (ComplexModel n) x x)]
      (fun z => HomogenizedGlueing.killMap w i z + (u ∘ flatInv Φ) z • EuclideanSpace.single i (1 : ℂ)) ∘
        Φ.toFun := by
    filter_upwards [(chartAt (ComplexModel n) x).open_target.mem_nhds
      ((chartAt (ComplexModel n) x).map_source (mem_chart_source _ x)),
      Φ.isOpen_source.mem_nhds hcs] with ζ hζt hζs
    have h1 : flatMap Φ ((chartAt (ComplexModel n) x).symm ζ) = Φ.toFun ζ := by
      simp only [flatMap, (chartAt (ComplexModel n) x).right_inv hζt]
    have h2 : flatInv Φ (Φ.toFun ζ) = (chartAt (ComplexModel n) x).symm ζ := by
      simp only [flatInv, Φ.left_inv ζ hζs]
    simp only [alongCoords, Function.comp_apply, h1, h2]
  have hΦd : HasFDerivAt Φ.toFun (fderiv ℂ Φ.toFun (chartAt (ComplexModel n) x x))
      (chartAt (ComplexModel n) x x) :=
    (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hcs)).hasFDerivAt
  have hGd : HasFDerivAt (fun z => HomogenizedGlueing.killMap w i z + (u ∘ flatInv Φ) z • EuclideanSpace.single i (1 : ℂ))
      (HomogenizedGlueing.killMap w i +
        (fderiv ℂ (u ∘ flatInv Φ) (flatMap Φ x)).smulRight (EuclideanSpace.single i (1 : ℂ)))
      (Φ.toFun (chartAt (ComplexModel n) x x)) :=
    (HomogenizedGlueing.killMap w i).hasFDerivAt.add (hud.hasFDerivAt.smul_const _)
  have hD := (hGd.comp (chartAt (ComplexModel n) x x) hΦd).congr_of_eventuallyEq hloc
  rw [hD.fderiv]
  exact (injective_killMap_add hwi hℓ).comp injective_fderiv_toFun

include hΦsrc hflat in
/-- **The adapted coordinates form a flat chart of `N` at `x`**: for `w ∈ ℂᵏ × 0`, `i < k` with `wᵢ ≠ 0`, `u` holomorphic on
an open `U ∋ x` with `u(x) = 0` and `d(u ∘ ψ⁻¹)(0) w ≠ 0`, there is a local holomorphic equivalence `Θ` at `e x`, centred at
`0`, with `Θ ∘ e = W` on its domain, which flattens `N` onto `ℂᵏ × 0`. -/
theorem exists_flatChart_alongCoords (hΦx : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    {w : ComplexModel n} (hw : w ∈ complexCoordinatePlane n k) {i : Fin n} (hi : i.1 < k) (hwi : w i ≠ 0)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) {u : M → ℂ} (hu : ∀ y ∈ U, HolomorphicAt n u y) (hux : u x = 0)
    (hℓ : fderiv ℂ (u ∘ flatInv Φ) (flatMap Φ x) w ≠ 0) :
    ∃ Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x),
      Θ.source ⊆ (chartAt (ComplexModel n) x).target ∧ Θ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Θ.source →
        y ∈ U ∩ flatDomain Φ ∧ Θ.toFun (chartAt (ComplexModel n) x y) = alongCoords Φ w i u y) ∧
      (∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Θ.source →
        (y ∈ N ↔ Θ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k)) := by
  have hO : IsOpen (U ∩ flatDomain Φ) := hU.inter (isOpen_flatDomain Φ)
  have hxO : x ∈ U ∩ flatDomain Φ := ⟨hxU, mem_flatDomain_self Φ⟩
  have hWs : ∀ z ∈ U ∩ flatDomain Φ,
      ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (alongCoords Φ w i u) z := fun z hz =>
    contMDiffAt_of_eventually_mdifferentiableAt (eventually_of_mem (hO.mem_nhds hz) fun y hy =>
      mdifferentiableAt_alongCoords w i hy.2 (hu y hy.1))
  obtain ⟨Θ, hΘt, hΘ0, hΘ⟩ := BlowupSNCTransform.exists_recentred_coords hO hWs hxO
    (injective_fderiv_alongCoords hΦsrc hwi (hu x hxU) hℓ)
  have hWx : alongCoords Φ w i u x = 0 := by
    simp only [alongCoords, flatMap, hΦx, map_zero, hux, zero_smul, add_zero]
  refine ⟨Θ, hΘt, hΘ0, fun {y} hy hyΘ => ?_, fun {y} hy hyΘ => ?_⟩
  · obtain ⟨hyO, hΘy⟩ := hΘ hy hyΘ
    refine ⟨hyO, ?_⟩
    rw [show Θ.toFun (chartAt (ComplexModel n) x y) = alongCoords Φ w i u y - alongCoords Φ w i u x from hΘy,
      hWx, sub_zero]
  · obtain ⟨hyO, hΘy⟩ := hΘ hy hyΘ
    rw [show Θ.toFun (chartAt (ComplexModel n) x y) = alongCoords Φ w i u y - alongCoords Φ w i u x from hΘy,
      hWx, sub_zero, alongCoords_mem_plane_iff hw hi]
    exact mem_iff_flatMap_mem hflat hyO.2

include hΦsrc hflat in
/-- **A common tangential direction for two tangent directions along `N`**: if `u`, `v` (holomorphic at `x ∈ N`) have
derivatives along fields tangent to `N` nonvanishing at `x`, there are `w ∈ ℂᵏ × 0` and `i < k` with `wᵢ ≠ 0` on which both
restricted differentials `d(u ∘ ψ⁻¹)(ψ x)`, `d(v ∘ ψ⁻¹)(ψ x)` are nonzero. -/
theorem exists_common_direction (hxN : x ∈ N) {u v : M → ℂ} (hu : HolomorphicAt n u x) (hv : HolomorphicAt n v x)
    (hdu : ∃ (e : ComplexChart n M) (ξ : Fin n → M → ℂ), IsTangentField N e ξ x ∧ fieldDeriv e ξ u x ≠ 0)
    (hdv : ∃ (e : ComplexChart n M) (ξ : Fin n → M → ℂ), IsTangentField N e ξ x ∧ fieldDeriv e ξ v x ≠ 0) :
    ∃ (w : ComplexModel n) (i : Fin n), w ∈ complexCoordinatePlane n k ∧ i.1 < k ∧ w i ≠ 0 ∧
      fderiv ℂ (u ∘ flatInv Φ) (flatMap Φ x) w ≠ 0 ∧ fderiv ℂ (v ∘ flatInv Φ) (flatMap Φ x) w ≠ 0 := by
  have hx0 : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  obtain ⟨e, ξ, hξ, hne⟩ := hdu
  obtain ⟨e', ξ', hξ', hne'⟩ := hdv
  obtain ⟨j, hj, hju⟩ := exists_flatPartial_ne_zero hΦsrc hflat hx0 hxN hu hξ hne
  obtain ⟨j', hj', hjv⟩ := exists_flatPartial_ne_zero hΦsrc hflat hx0 hxN hv hξ' hne'
  set P := planeRetract (n := n) k with hP
  have hLu : (fderiv ℂ (u ∘ flatInv Φ) (flatMap Φ x)).comp P ≠ 0 := by
    intro h0
    apply hju
    rw [flatPartial_eq hx0 hu j]
    have := congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L (EuclideanSpace.single j 1)) h0
    simpa [hP, planeRetract_of_mem (single_mem_complexCoordinatePlane hj)] using this
  have hLv : (fderiv ℂ (v ∘ flatInv Φ) (flatMap Φ x)).comp P ≠ 0 := by
    intro h0
    apply hjv
    rw [flatPartial_eq hx0 hv j']
    have := congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L (EuclideanSpace.single j' 1)) h0
    simpa [hP, planeRetract_of_mem (single_mem_complexCoordinatePlane hj')] using this
  obtain ⟨w₀, hw₀u, hw₀v⟩ := HomogenizedGlueing.exists_apply_ne_zero_and hLu hLv
  have hw : P w₀ ∈ complexCoordinatePlane n k := planeRetract_mem k w₀
  obtain ⟨i, hi⟩ : ∃ i, P w₀ i ≠ 0 := by
    by_contra! h
    have hw0 : P w₀ = 0 := by
      ext r
      simpa using h r
    apply hw₀u
    rw [ContinuousLinearMap.comp_apply, hw0, map_zero]
  have hik : i.1 < k := by
    by_contra hik
    exact hi (hw i (not_lt.mp hik))
  exact ⟨P w₀, i, hw, hik, hi, hw₀u, hw₀v⟩

end Adapted

/-! ### Two flat charts differing in one tangential coordinate -/

section Pair

variable {x : M} {Θa Θb : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}
  (hΘat : Θa.source ⊆ (chartAt (ComplexModel n) x).target) (hΘbt : Θb.source ⊆ (chartAt (ComplexModel n) x).target)
  {N : Set M} {k : ℕ}
  (hflata : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Θa.source →
    (y ∈ N ↔ Θa.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))
  (hflatb : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Θb.source →
    (y ∈ N ↔ Θb.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))
  {a b : M → ℂ} {i : Fin n} (hab : HolomorphicAt n (fun p => b p - a p) x) (hab0 : (fun p => b p - a p) x = 0)
  (hba : HolomorphicAt n (fun p => a p - b p) x) (hba0 : (fun p => a p - b p) x = 0)

include hflata hflatb in
/-- **Two flat charts of `N` that differ in the `i`-th coordinate** (`ψ_b = ψ_a + (b - a) eᵢ`, `(ψ_a)ᵢ = a` near `x`, both
centred at `0`): the coordinate change `φ` of `ψ_a` with `h = b - a` and `φ'` of `ψ_b` with `h = a - b` satisfy, near `x`,
`a ∘ φ = b`, `φ' ∘ φ = id`, and `φ(p) ∈ N ↔ p ∈ N`. -/
theorem eventually_flatChange_pair (hΘa0 : Θa.toFun (chartAt (ComplexModel n) x x) = 0)
    (hΘb0 : Θb.toFun (chartAt (ComplexModel n) x x) = 0)
    (hrel : ∀ᶠ p in 𝓝 x, flatMap Θb p = flatMap Θa p + (b p - a p) • EuclideanSpace.single i 1 ∧
      flatMap Θa p i = a p) :
    ∀ᶠ p in 𝓝 x, a ((flatChange Θa hΘat _ hab hab0 i).coordMap p) = b p ∧
      (flatChange Θb hΘbt _ hba hba0 i).coordMap ((flatChange Θa hΘat _ hab hab0 i).coordMap p) = p ∧
      ((flatChange Θa hΘat _ hab hab0 i).coordMap p ∈ N ↔ p ∈ N) := by
  set d := flatChange Θa hΘat _ hab hab0 i with hd
  set d' := flatChange Θb hΘbt _ hba hba0 i with hd'
  have hx0a : x ∈ flatDomain Θa := mem_flatDomain_self Θa
  have hx0b : x ∈ flatDomain Θb := mem_flatDomain_self Θb
  have hdT : Tendsto d.coordMap (𝓝 x) (𝓝 x) := by
    have := d.continuousAt_coordMap
    rwa [ContinuousAt, d.coordMap_self] at this
  have hbT : ∀ᶠ p in 𝓝 x, flatMap Θb p ∈ Θa.target := by
    have h0 : flatMap Θb x ∈ Θa.target := by
      show Θb.toFun (chartAt (ComplexModel n) x x) ∈ Θa.target
      rw [hΘb0, ← hΘa0]
      exact Θa.mapsTo_toFun Θa.center_mem_source
    exact (continuousAt_flatMap hx0b).eventually (Θa.isOpen_target.mem_nhds h0)
  have hV : ∀ᶠ p in 𝓝 x, p ∈ flatDomain Θa ∧ p ∈ flatDomain Θb :=
    Filter.Eventually.and ((isOpen_flatDomain Θa).mem_nhds hx0a) ((isOpen_flatDomain Θb).mem_nhds hx0b)
  have hcoord : ∀ᶠ p in 𝓝 x, d.coordMap p = flatInv Θa (flatMap Θb p) := by
    filter_upwards [hrel] with p hp
    rw [hd, flatChange_coordMap, hp.1]
  filter_upwards [hcoord, hbT, hV, hrel, hdT.eventually hrel, hdT.eventually hV] with p hp hpT hpV hpr hqr hqV
  have hqa : flatMap Θa (d.coordMap p) = flatMap Θb p := by
    rw [hp]
    exact flatMap_flatInv hpT hΘat
  refine ⟨?_, ?_, ?_⟩
  · rw [← hqr.2, hqa, hpr.1]
    simp [hpr.2]
  · rw [hd', flatChange_coordMap]
    have hsum : flatMap Θb (d.coordMap p) + (a (d.coordMap p) - b (d.coordMap p)) • EuclideanSpace.single i (1 : ℂ) =
        flatMap Θa (d.coordMap p) := by
      rw [hqr.1, add_assoc, ← add_smul, show b (d.coordMap p) - a (d.coordMap p) + (a (d.coordMap p) -
        b (d.coordMap p)) = 0 by ring, zero_smul, add_zero]
    rw [hsum, hqa, flatInv_flatMap hpV.2]
  · rw [mem_iff_flatMap_mem hflata hqV.1, hqa, ← mem_iff_flatMap_mem hflatb hpV.2]

end Pair

/-- The flat chart of `RegularAtDim`, stated with `chartAt`. -/
theorem exists_flatChart_of_regularAtDim {N : Set M} {x : M} {k : ℕ} (h : RegularAtDim (n := n) N x k) :
    ∃ Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧ Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k) := by
  obtain ⟨-, -, Φ, h1, h2, h3⟩ := h
  exact ⟨Φ, h1, h2, h3⟩

/-! ### Pullbacks by mutually inverse coordinate changes -/

/-- **Equality of pullbacks near a fixed point**: if two coordinate changes `φ`, `φ'` at `x` are inverse near `x` and both
preserve the germs at `x` of a coherent ideal `𝔟`, then `φ^*𝔟 = 𝔟` at every point near `x`. -/
theorem eventually_pullback_iff_of_inverse {𝔟 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) {x : M}
    (d d' : HomogenizedIdeal.CoordinateChange (n := n) x)
    (hcomp : ∀ g, 𝔟.mem x g → 𝔟.mem x (g ∘ d.coordMap)) (hcomp' : ∀ g, 𝔟.mem x g → 𝔟.mem x (g ∘ d'.coordMap))
    (hinv : ∀ᶠ p in 𝓝 x, d'.coordMap (d.coordMap p) = p) :
    ∀ᶠ y in 𝓝 x, ∀ g, (GermIdeal.pullback (m := n) d.coordMap 𝔟).mem y g ↔ 𝔟.mem y g := by
  have h1 := HomogenizedGlueing.eventually_pullback_le h𝔟 d.coordMap_self
    (HomogenizedGlueing.eventually_mdifferentiableAt_coordMap d) hcomp
  have h2 := HomogenizedGlueing.eventually_pullback_le h𝔟 d'.coordMap_self
    (HomogenizedGlueing.eventually_mdifferentiableAt_coordMap d') hcomp'
  have hφc : Tendsto d.coordMap (𝓝 x) (𝓝 x) := by
    have := d.continuousAt_coordMap
    rwa [ContinuousAt, d.coordMap_self] at this
  filter_upwards [h1, hφc.eventually h2, hinv.eventually_nhds,
    hφc.eventually (HomogenizedGlueing.eventually_mdifferentiableAt_coordMap d').eventually_nhds]
    with y hy1 hy2 hyinv hψd g
  refine ⟨hy1 g, fun hg => ?_⟩
  have hgh : HolomorphicAt n g y := HomogenizedGlueing.holomorphicAt_of_mem h𝔟 hg
  have hψφ : d'.coordMap (d.coordMap y) = y := hyinv.self_of_nhds
  have hgψ : 𝔟.mem (d.coordMap y) (g ∘ d'.coordMap) := by
    refine hy2 _ (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr ?_)
    refine InvertibleIdealQuotient.isInSpanAt_self ⟨g, by rw [hψφ]; exact hg, rfl⟩ ?_
    exact HadamardBridge.holomorphicAt_comp_map hψd (by rw [hψφ]; exact hgh)
  refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
    (isInSpanAt_of_eq_mul ⟨g ∘ d'.coordMap, hgψ, rfl⟩ hgh (holomorphicAt_const 1) ?_)
  filter_upwards [hyinv] with p hp
  simp [hp]

end

end Hironaka.HomogenizedGlueingAlong
