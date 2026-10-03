/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.CoefficientIdealAlongRestrictionFull
import Hironaka.MarkedIdeal.MaximalContactAlongTower
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent
import Hironaka.MarkedIdeal.DerivativeIdealAlongEtale
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Reduction to a hypersurface of maximal contact inside a submanifold

Source: Włodarczyk 2005, Lemma `le:codim2` (with any `E`, and without its hypothesis on the codimension of the
support, which the proof does not use), applied to the marked ideal `(M, N, E, 𝔞, μ)` on a closed submanifold `N`
and a hypersurface of maximal contact `N ∩ V(u)` inside `N`.

* `isTangentDirectionAlong_pullback_val`: a tangent direction along `N` on an open `U` restricts to one along `ι⁻¹N` on all of
  `U` (`DerivativeIdealAlongEtale`: `ι^*𝓓_N^j = 𝓓_{ι⁻¹N}^j ι^*` and the transfer of tangent fields);
  `isTangentDirectionAlong_pullback`: the same for any local biholomorphism `φ` (on `φ⁻¹U`).
* `isClosedSubmanifold_contact_along`: for a tangent direction `u` along `N` on all of `X`, `N ∩ V(u)` is a closed submanifold.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ContactEquivalenceAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdealAlong DerivativeIdealAlongEtale DerivativeIdealAlongCoherent GiraudAlong TangentDirectionAlong BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction HomogenizedIdealAlong MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal CoefficientIdealAlongRestrictionFull MarkedIdealBiholomorphism
open HomogenizedGlueingTower (strictAlong)

noncomputable section

/-! ### Tangent directions along `N` on open sets -/

section Open

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  (U : Opens M) {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {u : M → ℂ}

/-- **A tangent direction along `N` on an open set `U` restricts to one along `ι⁻¹N` on all of `U`** (`ι` the inclusion of
`U`): its germs pull back into `ι^*𝓓_N^{μ-1}(𝔞) = 𝓓_{ι⁻¹N}^{μ-1}(ι^*𝔞)`, and a field tangent to `N` with `ξ(u) ≠ 0` transfers
to a field tangent to `ι⁻¹N` with the same derivative. -/
theorem isTangentDirectionAlong_pullback_val (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    (hu : IsTangentDirectionAlong N 𝔞 μ U u) :
    IsTangentDirectionAlong ((Subtype.val : U → M) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : U → M) 𝔞) μ
      univ (u ∘ Subtype.val) where
  isOpen := isOpen_univ
  mem y _ := by
    rw [← pullback_val_iterDerivIdealAlong U h𝔞 (μ - 1)]
    exact comp_mem_pullback (isLocalInverseAt_val (n := n) U y).mdiff (hu.mem y y.2)
      (holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 (μ - 1) y u (hu.mem y y.2))
  multiplicity_one y _ hy0 := by
    obtain ⟨e, ξ, hξ, hne⟩ := hu.multiplicity_one y y.2 hy0
    have h := isLocalInverseAt_val (n := n) U y
    have hy' : y ∈ (complexChartAt (n := n) y).val.source := mem_complexChartAt_source y
    have huhol : HolomorphicAt n u (y : M) :=
      holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 (μ - 1) y u (hu.mem y y.2)
    have hghol : HolomorphicAt n (u ∘ Subtype.val) y :=
      HadamardBridge.holomorphicAt_comp_map h.mdiff huhol
    refine ⟨complexChartAt (n := n) y, transferField Subtype.val (openInv U y) e (complexChartAt (n := n) y) ξ,
      isTangentField_transfer h hy' hξ, ?_⟩
    have hcongr := fieldDeriv_transfer h hy' hξ.mem_source ξ hghol
    rw [hcongr.self_of_nhds]
    have hloc : ((u ∘ Subtype.val) ∘ openInv U y) =ᶠ[𝓝 (y : M)] u := by
      filter_upwards [U.isOpen.mem_nhds y.2] with q hq
      have hq' : q ∈ U := hq
      simp [openInv, hq']
    show fieldDeriv e ξ ((u ∘ Subtype.val) ∘ openInv U y) (y : M) ≠ 0
    rw [(fieldDeriv_congr hξ.mem_source hloc).self_of_nhds]
    exact hne

/-- **Tangent directions along `N` pull back by local biholomorphisms** (étale invariance, for property (6) of the
invariants along `N`): for `φ : M' → M` with holomorphic local inverses at every point, a tangent direction `u` of
`(𝔞|_N, μ)` along `N` on `U` gives the tangent direction `u ∘ φ` of `(φ^*𝔞|_{φ⁻¹N}, μ)` along `φ⁻¹N` on `φ⁻¹U`. -/
theorem isTangentDirectionAlong_pullback {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
    [IsComplexManifold n M'] {φ : M' → M} (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {V : Set M} (hu : IsTangentDirectionAlong N 𝔞 μ V u) :
    IsTangentDirectionAlong (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) μ (φ ⁻¹' V) (u ∘ φ) where
  isOpen := by
    have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun y =>
      (hloc y).choose_spec.mdiff.self_of_nhds.continuousAt
    exact hu.isOpen.preimage hφc
  mem y hy := by
    obtain ⟨ψ, h⟩ := hloc y
    rw [← pullback_iterDerivIdealAlong hloc h𝔞 (μ - 1)]
    exact comp_mem_pullback h.mdiff (hu.mem (φ y) hy)
      (holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 (μ - 1) (φ y) u (hu.mem (φ y) hy))
  multiplicity_one y hy hy0 := by
    obtain ⟨ψ, h⟩ := hloc y
    obtain ⟨e, ξ, hξ, hne⟩ := hu.multiplicity_one (φ y) hy hy0
    have hy' : y ∈ (complexChartAt (n := n) y).val.source := mem_complexChartAt_source y
    have huhol : HolomorphicAt n u (φ y) :=
      holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 (μ - 1) (φ y) u (hu.mem (φ y) hy)
    have hghol : HolomorphicAt n (u ∘ φ) y := HadamardBridge.holomorphicAt_comp_map h.mdiff huhol
    refine ⟨complexChartAt (n := n) y, transferField φ ψ e (complexChartAt (n := n) y) ξ,
      isTangentField_transfer h hy' hξ, ?_⟩
    have hcongr := fieldDeriv_transfer h hy' hξ.mem_source ξ hghol
    rw [hcongr.self_of_nhds]
    have hloc' : ((u ∘ φ) ∘ ψ) =ᶠ[𝓝 (φ y)] u := by
      filter_upwards [h.right_inv] with q hq
      simp only [Function.comp_apply, hq]
    show fieldDeriv e ξ ((u ∘ φ) ∘ ψ) (φ y) ≠ 0
    rw [(fieldDeriv_congr hξ.mem_source hloc').self_of_nhds]
    exact hne

/-- A difference vanishing on `N` near a point of `N` has vanishing derivative there along a field tangent to `N`: the
derivatives of `f` and `g` along `ξ` agree at `y` when `f = g` on `N` near `y`. -/
theorem fieldDeriv_eq_of_eqOn_N {e : ComplexChart n M} {ξ : Fin n → M → ℂ} {y : M} (hξ : IsTangentField N e ξ y)
    (hyN : y ∈ N) {f g : M → ℂ} (hf : HolomorphicAt n f y) (hg : HolomorphicAt n g y)
    (hfg : ∀ᶠ z in 𝓝 y, z ∈ N → f z = g z) : fieldDeriv e ξ f y = fieldDeriv e ξ g y := by
  have hd : (vanishingIdeal (n := n) N).mem y (fun z => f z - g z) :=
    ⟨GiraudAlong.holomorphicAt_sub hf hg, hfg.mono fun z hz hzN => by show f z - g z = 0; rw [hz hzN, sub_self]⟩
  have h0 := (hξ.preserves _ hd).2.self_of_nhds hyN
  have hadd := (fieldDeriv_add_eventuallyEq (ξ := ξ) hξ.mem_source hg (GiraudAlong.holomorphicAt_sub hf hg)).self_of_nhds
  have hfun : (fun q => g q + (f q - g q)) = f := funext fun q => by ring
  rw [hfun] at hadd
  rw [hadd, h0, add_zero]

/-- **Restricted tangent directions along `N` are locally genuine** (the bridge from the tangent directions along `N_T`
produced along multiple test blow-ups, which are controlled only on `N_T`, to `IsTangentDirectionAlong`): let `w` be
holomorphic on an open `O`, at every point of `N ∩ O` equal on `N` to a combination of germs of `𝓓_N^{μ-1}(𝔞)`, and of
multiplicity one along `N` at its zeros on `N`.  Then near every `x ∈ N ∩ O` there are an open `U ∋ x`, `U ⊆ O`, and a
tangent direction `w̃` of `(𝔞|_N, μ)` along `N` on `U` that agrees with `w` on `N ∩ U` (`w̃ = ∑ aᵢ sᵢ` from the span relation
at `x`, `𝓓_N^{μ-1}(𝔞)` being coherent; off `N` the field of `x` keeps `ξ(w̃) ≠ 0` nearby). -/
theorem exists_isTangentDirectionAlong_of_isInSpanOnAt (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N)
    {O : Set M} (hO : IsOpen O) {w : M → ℂ} (hw : ∀ y ∈ O, HolomorphicAt n w y)
    (hwD : ∀ y ∈ O, y ∈ N → IsInSpanOnAt (n := n) N ((iterDerivIdealAlong N 𝔞 (μ - 1)).mem y) y w)
    (hw1 : ∀ y ∈ O, y ∈ N → w y = 0 → ∃ (e : ComplexChart n M) (ξ : Fin n → M → ℂ),
      IsTangentField N e ξ y ∧ fieldDeriv e ξ w y ≠ 0)
    {x : M} (hxO : x ∈ O) (hxN : x ∈ N) :
    ∃ U : Opens M, x ∈ U ∧ (U : Set M) ⊆ O ∧ ∃ w' : M → ℂ, IsTangentDirectionAlong N 𝔞 μ U w' ∧
      ∀ y ∈ U, y ∈ N → w' y = w y := by
  have hD : (iterDerivIdealAlong N 𝔞 (μ - 1)).IsCoherent := isCoherent_iterDerivIdealAlong h𝔞 hN (μ - 1)
  obtain ⟨K, s, a, hs, ha, hsum⟩ := hwD x hxO hxN
  set w' : M → ℂ := fun y => ∑ i, a i y * s i y with hw'def
  have hshol : ∀ i, HolomorphicAt n (s i) x := fun i => HomogenizedGlueing.holomorphicAt_of_mem hD (hs i)
  have hw'hol : HolomorphicAt n w' x := HolomorphicAt.sum _ fun i _ => (ha i).mul (hshol i)
  -- membership of `w'` near `x`
  have hmem : ∀ᶠ y in 𝓝 x, (iterDerivIdealAlong N 𝔞 (μ - 1)).mem y w' := by
    filter_upwards [eventually_all.2 fun i => HomogenizedGlueing.eventually_mem hD (hs i),
      eventually_all.2 fun i => DerivativeIdeal.HolomorphicAt.eventually_holomorphicAt (ha i), DerivativeIdeal.HolomorphicAt.eventually_holomorphicAt hw'hol] with y hsy hay hw'y
    exact GermIdealTotalTransform.mem_of_isInSpanAt_mem hD ⟨hw'y, K, s, a, hsy, hay, Eventually.of_forall fun _ => rfl⟩
  -- agreement on `N`
  have hagree : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, z ∈ N → w' z = w z :=
    hsum.eventually_nhds.mono fun y hy => hy.mono fun z hz hzN => (hz hzN).symm
  -- multiplicity one at the zeros of `w'` near `x`
  have hmult : ∀ᶠ y in 𝓝 x, w' y = 0 → ∃ (e : ComplexChart n M) (ξ : Fin n → M → ℂ),
      IsTangentField N e ξ y ∧ fieldDeriv e ξ w' y ≠ 0 := by
    -- at the points of `N`: the field given by `hw1`
    have honN : ∀ᶠ y in 𝓝 x, y ∈ N → w' y = 0 → ∃ (e : ComplexChart n M) (ξ : Fin n → M → ℂ),
        IsTangentField N e ξ y ∧ fieldDeriv e ξ w' y ≠ 0 := by
      filter_upwards [hO.mem_nhds hxO, hagree, DerivativeIdeal.HolomorphicAt.eventually_holomorphicAt hw'hol] with y hyO hy hw'y hyN hy0
      have hwy : w y = 0 := by rw [← hy.self_of_nhds hyN]; exact hy0
      obtain ⟨e, ξ, hξ, hne⟩ := hw1 y hyO hyN hwy
      exact ⟨e, ξ, hξ, by rw [fieldDeriv_eq_of_eqOn_N hξ hyN hw'y (hw y hyO) hy]; exact hne⟩
    by_cases hx0 : w x = 0
    · -- the field of `x` keeps `ξ(w') ≠ 0` near `x`, and is tangent to `N` at the points off `N`
      obtain ⟨e₀, ξ₀, hξ₀, hne₀⟩ := hw1 x hxO hxN hx0
      have hF : fieldDeriv e₀ ξ₀ w' x ≠ 0 := by
        rw [fieldDeriv_eq_of_eqOn_N hξ₀ hxN hw'hol (hw x hxO) hagree.self_of_nhds]; exact hne₀
      have hFhol : HolomorphicAt n (fieldDeriv e₀ ξ₀ w') x :=
        holomorphicAt_fieldDeriv hξ₀.mem_source hξ₀.holomorphicAt hw'hol
      filter_upwards [honN, hFhol.self_of_nhds.continuousAt.eventually_ne hF,
        e₀.val.open_source.mem_nhds hξ₀.mem_source,
        eventually_all.2 fun m => DerivativeIdeal.HolomorphicAt.eventually_holomorphicAt (hξ₀.holomorphicAt m),
        DerivativeIdeal.HolomorphicAt.eventually_holomorphicAt hw'hol] with y hyN' hFy hys hξy hw'y hy0
      by_cases hyN : y ∈ N
      · exact hyN' hyN hy0
      · refine ⟨e₀, ξ₀, ⟨hys, hξy, fun g hg => ⟨holomorphicAt_fieldDeriv hys hξy hg.1, ?_⟩⟩, hFy⟩
        filter_upwards [hN.1.isOpen_compl.mem_nhds hyN] with z hz hzN
        exact absurd hzN hz
    · -- `w'` does not vanish near `x`
      have hx0' : w' x ≠ 0 := by rw [hagree.self_of_nhds.self_of_nhds hxN]; exact hx0
      filter_upwards [hw'hol.self_of_nhds.continuousAt.eventually_ne hx0'] with y hy hy0
      exact absurd hy0 hy
  obtain ⟨U, hUsub, hUo, hxU⟩ := mem_nhds_iff.mp
    ((hO.eventually_mem hxO).and (hmem.and (hmult.and hsum)))
  refine ⟨⟨U, hUo⟩, hxU, fun y hy => (hUsub hy).1, w', ⟨hUo, fun y hy => (hUsub hy).2.1,
    fun y hy hy0 => (hUsub hy).2.2.1 hy0⟩, fun y hy hyN => ((hUsub hy).2.2.2 hyN).symm⟩

end Open

/-! ### The reduction on all of `X` and on open sets -/

section Contact

variable {n : ℕ} {X : CMfd.{u} n}

/-- **`N ∩ V(u)` is a closed submanifold** for a tangent direction `u` along the closed submanifold `N` on all of `X`
(regular of dimension one less than `N` at each of its points, `IsTangentDirectionAlong.regularAtDim_contact`). -/
theorem isClosedSubmanifold_contact_along {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔪.N 𝔪.ideal 𝔪.d univ u) :
    IsClosedSubmanifold n (𝔪.N ∩ {x | u x = 0} ∩ univ) := by
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞
  have hcont : Continuous u := continuous_iff_continuousAt.mpr fun x =>
    (holomorphicAt_of_mem_iterDerivIdealAlong hhol (𝔪.d - 1) x u (hu.mem x (mem_univ x))).self_of_nhds.continuousAt
  refine ⟨(hN.1.inter (isClosed_eq hcont continuous_const)).inter isClosed_univ, fun x hx => ?_⟩
  obtain ⟨k, -, hk⟩ := hu.regularAtDim_contact hhol hN hx
  exact ⟨k - 1, hk⟩

end Contact

end

end Hironaka.ContactEquivalenceAlong
