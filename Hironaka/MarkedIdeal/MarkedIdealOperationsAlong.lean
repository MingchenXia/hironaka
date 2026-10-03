/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.OrderMultiplicativity
import Hironaka.Invariant.OrderTaylor
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictLeCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.MarkedIdeal.RestrictLe
import Hironaka.Coherence.VanishingIdealCoherent
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Sums and products of marked ideals on a submanifold under admissible blowups

Source: Włodarczyk 2005 §2.9, Lemma `le:operations` (sums `(𝓘, μ) + (𝓙, ν) = (𝓘^ν + 𝓙^μ, μν)` and products `(𝓘𝓙, μ +
ν)` of marked ideals and their multiple test blow-ups), in Bierstone--Milman's formalism `(M, N, E, 𝓘, d)` with `𝓘 ⊆
𝒪_N` (BM08, Definitions 2.1--2.2). For `N = M` this is `MarkedIdealOperationsTransform`.

For `N ≠ M` the ideal of a marked ideal is an ambient representative of an ideal of `𝒪_N`; only its restriction to
`N` matters.  So the statements hold up to **restricted equivalence** (`MarkedIdeal.RestrictEquiv`: same `N`, `E`,
mark, and `Res_N 𝔞 = Res_N 𝔟`), which has the same cosupport, the same admissible centres and the SAME transform
(`RestrictEquiv.geoTransform_eq`).

## Main results

* `exists_localRetraction`: a holomorphic retraction onto a submanifold near each of its regular points (flattening
  coordinates followed by the linear retraction `HadamardBridgeAlong.planeRetract`);
* `vanishesToOrderOn_of_pow`, `cosupport_idealPow_mul_eq_along`, `cosupport_sumIdeal_idealPow_along`: `ord_N(g^ν) =
  ν ord_N(g)` in the form `cosupp(𝔞^ν|_N, μν) = cosupp(𝔞|_N, μ)`, hence
  `cosupp((𝔞, μ) + (𝔟, ν)) = cosupp(𝔞, μ) ∩ cosupp(𝔟, ν)` along any submanifold (`N = M`:
  `OrderMultiplicativity`);
* restricted calculus: `IsInSpanOnAt.mul`, `restrictLe_mul`, `restrictLe_idealPow`, `restrictLe_sumIdeal`,
  `restrictOn_eq_of_restrictLe`, `cosupport_subset_of_restrictLe`;
* `RestrictEquiv`, `RestrictEquiv.cosupp_eq`, `RestrictEquiv.isAdmissibleCentre_iff`, `RestrictEquiv.geoTransform_eq`;
* one admissible blowup: `geoTransform_add_restrictEquiv` (the transform of a sum is restricted-equivalent to the
  sum of the transforms) and `geoTransform_mul_restrictEquiv` (the same for products);
* along towers (Włodarczyk `le:operations` (1)--(2) for marked ideals on a closed submanifold `N`, same `E`):
  `geoTransformAlong_add_along` (the multiple test blow-ups of `𝔪₁ + 𝔪₂` are exactly the simultaneous ones, and
  along them `(𝔪₁ + 𝔪₂)_T ≃ (𝔪₁)_T + (𝔪₂)_T`), `geoTransformAlong_mul_along`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MarkedIdealOperationsAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.IdealWeightPowers Hironaka.HadamardBridge Hironaka.HadamardBridgeAlong Hironaka.IdealOrderArithmetic

noncomputable section

/-! ### A local retraction onto a submanifold -/

section Retraction

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A holomorphic retraction onto a submanifold near a regular point**: if `N` is regular of dimension `k` at
`x`, there is a map `r`, holomorphic near `x`, with `r x = x`, values in `N` near `x`, and `r = id` on `N` near
`x`. -/
theorem exists_localRetraction {N : Set M} {x : M} {k : ℕ} (hN : RegularAtDim (n := n) N x k) :
    ∃ r : M → M, r x = x ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) r y) ∧
      (∀ᶠ y in 𝓝 x, r y ∈ N) ∧ (∀ᶠ y in 𝓝 x, y ∈ N → r y = y) := by
  obtain ⟨-, -, Φ, hΦsrc, hΦ0, hflat⟩ := hN
  set e := chartAt (ComplexModel n) x with he
  set P := planeRetract (n := n) k with hP
  set ψ : M → ComplexModel n := fun y => Φ.toFun (e y) with hψ
  have hx : x ∈ BlowupFlatCoordinates.flatDomain Φ := BlowupFlatCoordinates.mem_flatDomain_self Φ
  have hψx : ψ x = 0 := hΦ0
  have hψc : ContinuousAt ψ x :=
    ((Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hx.2)).continuousAt).comp
      (e.continuousAt hx.1)
  have hT : ∀ᶠ y in 𝓝 x, P (ψ y) ∈ Φ.target := by
    have h0 : P (ψ x) ∈ Φ.target := by
      rw [hψx, planeRetract_zero, ← hψx]
      exact Φ.mapsTo_toFun hx.2
    exact (P.continuous.continuousAt.comp hψc).preimage_mem_nhds (Φ.isOpen_target.mem_nhds h0)
  refine ⟨fun y => e.symm (Φ.invFun (P (ψ y))), ?_, ?_, ?_, ?_⟩
  · show e.symm (Φ.invFun (P (ψ x))) = x
    rw [hψx, planeRetract_zero, ← hψx]
    exact BlowupFlatCoordinates.flatInverse_flat Φ hx
  · filter_upwards [hT, (BlowupFlatCoordinates.isOpen_flatDomain Φ).mem_nhds hx] with y hyT hy
    have hψd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ y :=
      (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hy.2)).mdifferentiableAt.comp y
        (BlowupFlatCoordinates.mdifferentiableAt_chart (y₀ := x) hy.1)
    have hφd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
        (fun w => e.symm (Φ.invFun w)) (P (ψ y)) :=
      (BlowupFlatCoordinates.mdifferentiableAt_chart_symm (y₀ := x) (hΦsrc (Φ.mapsTo_invFun hyT))).comp _
        (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hyT)).mdifferentiableAt
    have hcomp := hφd.comp y (P.differentiableAt.mdifferentiableAt.comp y hψd)
    exact hcomp
  · filter_upwards [hT] with y hyT
    obtain ⟨hmem, hΦw⟩ := BlowupFlatCoordinates.flatInverse_mem Φ hyT hΦsrc
    refine (hflat hmem.1 hmem.2).mpr ?_
    change Φ.toFun (e (e.symm (Φ.invFun (P (ψ y))))) ∈ _
    rw [hΦw]
    exact planeRetract_mem k _
  · filter_upwards [(BlowupFlatCoordinates.isOpen_flatDomain Φ).mem_nhds hx] with y hy hyN
    have hψN : ψ y ∈ complexCoordinatePlane n k := (hflat hy.1 hy.2).mp hyN
    show e.symm (Φ.invFun (P (ψ y))) = y
    rw [planeRetract_of_mem hψN]
    exact BlowupFlatCoordinates.flatInverse_flat Φ hy

/-! ### Orders of powers along a submanifold -/

/-- **`ord_N(g^ν) ≥ νμ ⟹ ord_N(g) ≥ μ`** at a regular point of `N` (`ν ≥ 1`, `g` holomorphic). -/
theorem vanishesToOrderOn_of_pow {N : Set M} {x : M} {k : ℕ} (hN : RegularAtDim (n := n) N x k)
    {g : M → ℂ} (hg : HolomorphicAt n g x) {ν μ : ℕ} (hν : 1 ≤ ν)
    (h : VanishesToOrderOn n N x (ν * μ) (fun p => g p ^ ν)) : VanishesToOrderOn n N x μ g := by
  obtain ⟨r, hrx, hrd, hrN, hrid⟩ := exists_localRetraction hN
  obtain ⟨h, hh, hgh⟩ := h
  have hrT : Tendsto r (𝓝 x) (𝓝 x) := by
    have := hrd.self_of_nhds.continuousAt.tendsto
    rwa [hrx] at this
  have hĝ : HolomorphicAt n (g ∘ r) x := holomorphicAt_comp_map hrd (by rw [hrx]; exact hg)
  have hh' : (idealPow (pointIdeal n (r x)) (ν * μ)).mem (r x) h := by rw [hrx]; exact hh
  have hhr := comp_mem_idealPow_pointIdeal hrd (ν * μ) hh'
  have heq : (fun p => (g ∘ r) p ^ ν) =ᶠ[𝓝 x] h ∘ r := by
    filter_upwards [hrN, hrT.eventually hgh] with p hp1 hp2
    exact hp2 hp1
  have hpow : (idealPow (pointIdeal n x) (ν * μ)).mem x (fun p => (g ∘ r) p ^ ν) :=
    OrderTaylor.mem_idealPow_congr hhr heq.symm
  refine ⟨g ∘ r, OrderMultiplicativity.mem_idealPow_of_pow_mem hĝ hν hpow, ?_⟩
  filter_upwards [hrid] with p hp hpN
  simp [hp hpN]

/-- **`cosupp(𝔞^ν|_N, μν) = cosupp(𝔞|_N, μ)`** along a submanifold (`ν ≥ 1`, ideal of holomorphic germs). -/
theorem cosupport_idealPow_mul_eq_along {N : Set M} (hN : ∀ x ∈ N, ∃ k, RegularAtDim (n := n) N x k)
    {𝔞 : GermIdeal n M} (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {ν : ℕ} (hν : 1 ≤ ν) (μ : ℕ) :
    cosupport n N (idealPow 𝔞 ν) (μ * ν) = cosupport n N 𝔞 μ := by
  refine Subset.antisymm ?_ (cosupport_subset_cosupport_idealPow μ ν)
  rintro x ⟨hxN, hx⟩
  refine ⟨hxN, fun g hg => ?_⟩
  obtain ⟨k, hk⟩ := hN x hxN
  have hpow := hx _ (OrderMultiplicativity.pow_mem_idealPow hg (h𝔞 x g hg) ν)
  rw [Nat.mul_comm] at hpow
  exact vanishesToOrderOn_of_pow hk (h𝔞 x g hg) hν hpow

/-- **The cosupport of a sum of marked ideals along a submanifold** (marks `≥ 1`). -/
theorem cosupport_sumIdeal_idealPow_along {N : Set M} (hN : ∀ x ∈ N, ∃ k, RegularAtDim (n := n) N x k)
    {𝔞 𝔟 : GermIdeal n M} (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x) {μ ν : ℕ} (hμ : 1 ≤ μ) (hν : 1 ≤ ν) :
    cosupport n N (RestrictedIdealExtension.sumIdeal (idealPow 𝔞 ν) (idealPow 𝔟 μ)) (μ * ν) =
      cosupport n N 𝔞 μ ∩ cosupport n N 𝔟 ν := by
  rw [cosupport_sumIdeal (fun x g hg => holomorphicAt_of_mem_idealPow hg)
      (fun x g hg => holomorphicAt_of_mem_idealPow hg),
    cosupport_idealPow_mul_eq_along hN h𝔞 hν μ, Nat.mul_comm, cosupport_idealPow_mul_eq_along hN h𝔟 hμ ν]

end Retraction

/-! ### Restricted calculus -/

section Restricted

open RestrictedIdealWeight RestrictedIdealExtension RelativePrincipalizationSpan InvertibleIdealQuotient

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {W : Set M}

/-- **Restricted spans multiply**: if `a` (resp. `b`) agrees on `W` near `x` with a combination of germs of
`S` (resp. `T`), then `a b` agrees on `W` near `x` with a combination of products. -/
theorem IsInSpanOnAt.mul {S T : (M → ℂ) → Prop} {x : M} {a b : M → ℂ}
    (ha : IsInSpanOnAt (n := n) W S x a) (hb : IsInSpanOnAt (n := n) W T x b) :
    IsInSpanOnAt (n := n) W (fun t => ∃ s s', S s ∧ T s' ∧ t = s * s') x (a * b) := by
  obtain ⟨K, s, c, hs, hc, hsum⟩ := ha
  refine RelativePrincipalizationSpan.IsInSpanOnAt.trans (S := fun t => ∃ i, t = s i * b) ?_
    ⟨K, fun i => s i * b, c, fun i => ⟨i, rfl⟩, hc, ?_⟩
  · rintro t ⟨i, rfl⟩
    obtain ⟨L, s', c', hs', hc', hsum'⟩ := hb
    refine ⟨L, fun j => s i * s' j, c', fun j => ⟨s i, s' j, hs i, hs' j, rfl⟩, hc', ?_⟩
    filter_upwards [hsum'] with y hy hyW
    simp only [Pi.mul_apply]
    rw [hy hyW, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · filter_upwards [hsum] with y hy hyW
    simp only [Pi.mul_apply]
    rw [hy hyW, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **Restricted inclusions multiply.** -/
theorem restrictLe_mul {𝔞 𝔟 𝔞' 𝔟' : GermIdeal n M} (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x)
    (h𝔟' : ∀ x g, 𝔟'.mem x g → HolomorphicAt n g x) (h : RestrictLe W 𝔞 𝔟) (h' : RestrictLe W 𝔞' 𝔟') :
    RestrictLe W (𝔞.mul 𝔞') (𝔟.mul 𝔟') := by
  intro x hx g hg
  refine RelativePrincipalizationSpan.IsInSpanOnAt.trans ?_
    (IsInSpanAt.restrict (InvertibleIdealQuotient.mem_mul_iff.mp hg))
  rintro t ⟨a, a', ha, ha', rfl⟩
  refine RelativePrincipalizationSpan.IsInSpanOnAt.mono ?_ (IsInSpanOnAt.mul (h x hx a ha) (h' x hx a' ha'))
  rintro _ ⟨b, b', hb, hb', rfl⟩
  exact IdealOrderArithmetic.mul_mem_mul hb hb' ((h𝔟 x b hb).mul (h𝔟' x b' hb'))

/-- **Restricted inclusions pass to powers.** -/
theorem restrictLe_idealPow {𝔞 𝔟 : GermIdeal n M} (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x)
    (h : RestrictLe W 𝔞 𝔟) : ∀ k : ℕ, RestrictLe W (idealPow 𝔞 k) (idealPow 𝔟 k)
  | 0 => fun _ _ _ hg => IsInSpanAt.restrict (isInSpanAt_self (S := (unitIdeal n M).mem _) hg hg)
  | k + 1 => restrictLe_mul (fun _ _ hg => holomorphicAt_of_mem_idealPow hg) h𝔟 (restrictLe_idealPow h𝔟 h k) h

/-- **Restricted inclusions add.** -/
theorem restrictLe_sumIdeal {𝔞 𝔟 𝔠 𝔡 : GermIdeal n M} (h𝔠 : ∀ x g, 𝔠.mem x g → HolomorphicAt n g x)
    (h𝔡 : ∀ x g, 𝔡.mem x g → HolomorphicAt n g x) (h₁ : RestrictLe W 𝔞 𝔠) (h₂ : RestrictLe W 𝔟 𝔡) :
    RestrictLe W (sumIdeal 𝔞 𝔟) (sumIdeal 𝔠 𝔡) := by
  intro x hx g hg
  refine RelativePrincipalizationSpan.IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict (mem_sumIdeal_iff.mp hg))
  rintro s (hs | hs)
  · exact RelativePrincipalizationSpan.IsInSpanOnAt.mono (fun t ht => le_sumIdeal_left' h𝔠 x t ht)
      (h₁ x hx s hs)
  · exact RelativePrincipalizationSpan.IsInSpanOnAt.mono (fun t ht => le_sumIdeal_right' h𝔡 x t ht)
      (h₂ x hx s hs)

/-- A restricted inclusion on `W` holds on every subset of `W`. -/
theorem restrictLe_mono {W' : Set M} (hW : W' ⊆ W) {𝔞 𝔟 : GermIdeal n M} (h : RestrictLe W 𝔞 𝔟) :
    RestrictLe W' 𝔞 𝔟 := by
  intro x hx g hg
  obtain ⟨K, s, a, hs, ha, hsum⟩ := h x (hW hx) g hg
  exact ⟨K, s, a, hs, ha, hsum.mono fun y hy hyW => hy (hW hyW)⟩

/-- Off a closed set `W` every germ is a restricted combination (the empty one). -/
theorem isInSpanOnAt_of_notMem (hW : IsClosed W) {S : (M → ℂ) → Prop} {x : M} (hx : x ∉ W)
    (g : M → ℂ) : IsInSpanOnAt (n := n) W S x g := by
  refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
  filter_upwards [hW.isOpen_compl.mem_nhds hx] with y hy hyW
  exact absurd hyW hy

/-- **Restricted equality gives equal extensions** along a closed set. -/
theorem restrictOn_eq_of_restrictLe (hW : IsClosed W) {𝔞 𝔟 : GermIdeal n M} (h₁ : RestrictLe W 𝔞 𝔟)
    (h₂ : RestrictLe W 𝔟 𝔞) : restrictOn n W 𝔞 = restrictOn n W 𝔟 := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ?_)
  refine and_congr Iff.rfl ?_
  by_cases hx : x ∈ W
  · exact ⟨fun h => RelativePrincipalizationSpan.IsInSpanOnAt.trans (fun s hs => h₁ x hx s hs) h,
      fun h => RelativePrincipalizationSpan.IsInSpanOnAt.trans (fun s hs => h₂ x hx s hs) h⟩
  · exact ⟨fun _ => isInSpanOnAt_of_notMem hW hx g, fun _ => isInSpanOnAt_of_notMem hW hx g⟩

/-- **The cosupport only sees the restriction to `N`**: `Res_N 𝔞 ⊆ Res_N 𝔟` gives
`cosupp(𝔟|_N, d) ⊆ cosupp(𝔞|_N, d)`. -/
theorem cosupport_subset_of_restrictLe {N : Set M} {𝔞 𝔟 : GermIdeal n M} (h : RestrictLe N 𝔞 𝔟) (d : ℕ) :
    cosupport n N 𝔟 d ⊆ cosupport n N 𝔞 d := by
  rintro x ⟨hxN, hx⟩
  refine ⟨hxN, fun g hg => ?_⟩
  obtain ⟨K, s, c, hs, hc, hsum⟩ := h x hxN g hg
  obtain ⟨k, hk, hsk⟩ := vanishesToOrderOn_sum_mul hc fun i => hx (s i) (hs i)
  refine ⟨k, hk, ?_⟩
  filter_upwards [hsum, hsk] with y hy hy' hyN
  rw [hy hyN, hy' hyN]

end Restricted

/-! ### Restricted equivalence of marked ideals -/

namespace MarkedIdeal

open RestrictedIdealWeight RestrictedIdealExtension RestrictedIdealQuotient MarkedIdeals MarkedIdeals.MarkedIdeal BlowupStrictSubmanifold

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Restricted equivalence**: same `N`, `E` and mark, and ideals with the same restriction to `N`
(`Res_N 𝔞 = Res_N 𝔟`).  Only the restriction of the ideal to `N` is part of the data of `(M, N, E, 𝓘, d)`. -/
structure RestrictEquiv (𝔪 𝔫 : MarkedIdeal n M) : Prop where
  N_eq : 𝔪.N = 𝔫.N
  E_eq : 𝔪.E = 𝔫.E
  d_eq : 𝔪.d = 𝔫.d
  le : RestrictLe 𝔪.N 𝔪.ideal 𝔫.ideal
  ge : RestrictLe 𝔪.N 𝔫.ideal 𝔪.ideal

/-- Restricted equivalence is reflexive (coherent ideal). -/
theorem RestrictEquiv.refl {𝔪 : MarkedIdeal n M} (h : 𝔪.ideal.IsCoherent) : RestrictEquiv 𝔪 𝔪 :=
  ⟨rfl, rfl, rfl, RestrictLeCalculus.restrictLe_refl h, RestrictLeCalculus.restrictLe_refl h⟩

/-- **Restricted-equivalent marked ideals have the same cosupport.** -/
theorem RestrictEquiv.cosupp_eq {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫) : 𝔪.cosupp = 𝔫.cosupp := by
  unfold MarkedIdeals.MarkedIdeal.cosupp
  rw [← h.N_eq, ← h.d_eq]
  exact Subset.antisymm (cosupport_subset_of_restrictLe h.ge _) (cosupport_subset_of_restrictLe h.le _)

/-- **Restricted-equivalent marked ideals have the same admissible centres.** -/
theorem RestrictEquiv.isAdmissibleCentre_iff {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫) {C : Set M} :
    𝔪.IsAdmissibleCentre C ↔ 𝔫.IsAdmissibleCentre C := by
  unfold MarkedIdeals.MarkedIdeal.IsAdmissibleCentre
  rw [h.cosupp_eq, h.E_eq]

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **Restricted-equivalent marked ideals have the SAME transform** (closed `N`, coherent ideals): the transform
only sees the restriction of `π^*𝔞` to the strict transform `N' ⊆ π⁻¹N`. -/
theorem RestrictEquiv.geoTransform_eq {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) {C : Set M} {π : M' → M}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) :
    𝔪.geoTransform C π = 𝔫.geoTransform C π := by
  have hsub : geoStrictTransform π C 𝔪.N ⊆ π ⁻¹' 𝔪.N := geoStrictTransform_subset_preimage hπ.continuous hN
  have hWV : ∀ y ∈ geoStrictTransform π C 𝔪.N, π y ∈ 𝔪.N := fun y hy => hsub hy
  have h₁ := RestrictLeCalculus.restrictLe_pullback hπ hWV h𝔫 h.le
  have h₂ := RestrictLeCalculus.restrictLe_pullback hπ hWV h𝔪 h.ge
  have hres : restrictOn n (geoStrictTransform π C 𝔪.N) (GermIdeal.pullback (m := n) π 𝔪.ideal) =
      restrictOn n (geoStrictTransform π C 𝔪.N) (GermIdeal.pullback (m := n) π 𝔫.ideal) :=
    restrictOn_eq_of_restrictLe isClosed_closure h₁ h₂
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ ?_
  · rw [geoTransform_N, geoTransform_N, h.N_eq]
  · rw [geoTransform_E, geoTransform_E, h.E_eq]
  · rw [geoTransform_ideal, geoTransform_ideal, ← h.N_eq, ← h.d_eq]
    show InvertibleIdealQuotient.colon (restrictOn n (geoStrictTransform π C 𝔪.N)
      (GermIdeal.pullback (m := n) π 𝔪.ideal)) _ = InvertibleIdealQuotient.colon
      (restrictOn n (geoStrictTransform π C 𝔪.N) (GermIdeal.pullback (m := n) π 𝔫.ideal)) _
    rw [hres]
  · exact h.d_eq

/-! ### One admissible blowup -/

open GermIdealPullbackCalculus

/-- Two marked ideals on the same closed submanifold `N`, with the same `E` and coherent ideals. -/
structure IsSubmanifoldPair (𝔪₁ 𝔪₂ : MarkedIdeal n M) : Prop where
  N_eq : 𝔪₁.N = 𝔪₂.N
  E_eq : 𝔪₁.E = 𝔪₂.E
  isClosedSubmanifold : IsClosedSubmanifold n 𝔪₁.N
  coh₁ : 𝔪₁.ideal.IsCoherent
  coh₂ : 𝔪₂.ideal.IsCoherent

/-- Members of a coherent ideal are holomorphic. -/
theorem hol_of_isCoherent {𝔠 : GermIdeal n M'} (h : 𝔠.IsCoherent) :
    ∀ x g, 𝔠.mem x g → HolomorphicAt n g x :=
  fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h hg

/-- **The defining equation of the transform, along `N'`**: `Res_{N'} π^*𝔞 = Res_{N'} ((π^*𝓘_C)^d · 𝔞')` for an
admissible centre (`N` a closed submanifold, `𝔞` coherent). -/
theorem restrictLe_pullback_geoTransform {𝔪 : MarkedIdeal n M} (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) {C : Set M} (hC : 𝔪.IsAdmissibleCentre C) {π : M' → M}
    (hπ : IsBlowupAlong n C π) :
    RestrictLe (𝔪.geoTransform C π).N (GermIdeal.pullback (m := n) π 𝔪.ideal)
        ((idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 𝔪.d).mul
          (𝔪.geoTransform C π).ideal) ∧
      RestrictLe (𝔪.geoTransform C π).N
        ((idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 𝔪.d).mul
          (𝔪.geoTransform C π).ideal) (GermIdeal.pullback (m := n) π 𝔪.ideal) := by
  have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have hW : IsClosedSubmanifold n (geoStrictTransform π C 𝔪.N) :=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hC.subset_N
  have hπa := isCoherent_pullback hπ.contMDiff h𝔞
  have hle : RestrictLe (geoStrictTransform π C 𝔪.N) (GermIdeal.pullback (m := n) π 𝔪.ideal)
      (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 𝔪.d) := by
    have h1 := HadamardBridgeAlong.restrictLe_idealPow_vanishingIdeal_of_subset_cosupport h𝔞 hN hC.1
      hC.subset_N hC.2.1
    have h2 := RestrictLeCalculus.restrictLe_pullback hπ.contMDiff (W := geoStrictTransform π C 𝔪.N)
      (fun y hy => geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hy)
      (isCoherent_idealPow hIC _) h1
    rwa [BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff hIC] at h2
  exact ⟨restrictLe_mul_colon hπa (isInvertibleAlong_geoStrictTransform hπ 𝔪.N 𝔪.d) hle,
    restrictLe_mul_colon' hπa (VanishingIdealCoherent.isCoherent_vanishingIdeal hW)⟩

/-- **A centre admissible for both summands is admissible for the sum** (any `N`). -/
theorem IsAdmissibleCentre.add {𝔪₁ 𝔪₂ : MarkedIdeal n M} (h : IsSubmanifoldPair 𝔪₁ 𝔪₂) {C : Set M}
    (hC₁ : 𝔪₁.IsAdmissibleCentre C) (hC₂ : 𝔪₂.IsAdmissibleCentre C) :
    (MarkedIdealOperationsTransform.MarkedIdeal.add 𝔪₁ 𝔪₂).IsAdmissibleCentre C := by
  refine ⟨hC₁.1, fun x hx => ?_, hC₁.2.2⟩
  show x ∈ cosupport n 𝔪₁.N (sumIdeal (idealPow 𝔪₁.ideal 𝔪₂.d) (idealPow 𝔪₂.ideal 𝔪₁.d)) (𝔪₁.d * 𝔪₂.d)
  rw [cosupport_sumIdeal (fun _ _ hg => holomorphicAt_of_mem_idealPow hg)
    (fun _ _ hg => holomorphicAt_of_mem_idealPow hg)]
  refine ⟨cosupport_subset_cosupport_idealPow _ _ (hC₁.2.1 hx), ?_⟩
  have h2 : x ∈ cosupport n 𝔪₁.N 𝔪₂.ideal 𝔪₂.d := by
    have := hC₂.2.1 hx
    rwa [MarkedIdeals.MarkedIdeal.cosupp, ← h.N_eq] at this
  have := cosupport_subset_cosupport_idealPow (N := 𝔪₁.N) (𝔞 := 𝔪₂.ideal) 𝔪₂.d 𝔪₁.d h2
  rwa [Nat.mul_comm] at this

/-- **One step of `le:operations` (1) along `N`**: the transform of a sum is restricted-equivalent to the sum of
the transforms. -/
theorem geoTransform_add_restrictEquiv {𝔪₁ 𝔪₂ : MarkedIdeal n M} (h : IsSubmanifoldPair 𝔪₁ 𝔪₂) {C : Set M}
    {π : M' → M} (hπ : IsBlowupAlong n C π) (hC₁ : 𝔪₁.IsAdmissibleCentre C)
    (hC₂ : 𝔪₂.IsAdmissibleCentre C) :
    RestrictEquiv ((MarkedIdealOperationsTransform.MarkedIdeal.add 𝔪₁ 𝔪₂).geoTransform C π)
      (MarkedIdealOperationsTransform.MarkedIdeal.add (𝔪₁.geoTransform C π) (𝔪₂.geoTransform C π)) := by
  set 𝔰 := MarkedIdealOperationsTransform.MarkedIdeal.add 𝔪₁ 𝔪₂ with h𝔰
  have hN := h.isClosedSubmanifold
  have hN₂ : IsClosedSubmanifold n 𝔪₂.N := h.N_eq ▸ hN
  have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have h𝔩 : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).IsCoherent :=
    isCoherent_pullback hπ.contMDiff hIC
  set 𝔩 := GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C) with h𝔩def
  set μ := 𝔪₁.d
  set ν := 𝔪₂.d
  have h𝔰coh : 𝔰.ideal.IsCoherent :=
    isCoherent_sumIdeal (isCoherent_idealPow h.coh₁ _) (isCoherent_idealPow h.coh₂ _)
  have hC𝔰 : 𝔰.IsAdmissibleCentre C := IsAdmissibleCentre.add h hC₁ hC₂
  have h𝔞' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN h.coh₁ hC₁ hπ
  have h𝔟' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN₂ h.coh₂ hC₂ hπ
  have h𝔰' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (𝔪 := 𝔰) hN h𝔰coh hC𝔰 hπ
  obtain ⟨a1, a2⟩ := restrictLe_pullback_geoTransform hN h.coh₁ hC₁ hπ
  obtain ⟨b1, b2⟩ := restrictLe_pullback_geoTransform hN₂ h.coh₂ hC₂ hπ
  obtain ⟨s1, s2⟩ := restrictLe_pullback_geoTransform (𝔪 := 𝔰) hN h𝔰coh hC𝔰 hπ
  have hW₂ : (𝔪₂.geoTransform C π).N = (𝔪₁.geoTransform C π).N := by
    rw [geoTransform_N, geoTransform_N, h.N_eq]
  rw [hW₂] at b1 b2
  set W := (𝔪₁.geoTransform C π).N with hWdef
  set 𝔞' := (𝔪₁.geoTransform C π).ideal
  set 𝔟' := (𝔪₂.geoTransform C π).ideal
  set 𝔰' := (𝔰.geoTransform C π).ideal
  set L := idealPow 𝔩 (μ * ν) with hL
  set X := sumIdeal (idealPow 𝔞' ν) (idealPow 𝔟' μ) with hX
  have hLcoh : L.IsCoherent := isCoherent_idealPow h𝔩 _
  have hXcoh : X.IsCoherent := isCoherent_sumIdeal (isCoherent_idealPow h𝔞' _) (isCoherent_idealPow h𝔟' _)
  have e1 : GermIdeal.pullback (m := n) π 𝔰.ideal =
      sumIdeal (idealPow (GermIdeal.pullback (m := n) π 𝔪₁.ideal) ν)
        (idealPow (GermIdeal.pullback (m := n) π 𝔪₂.ideal) μ) := by
    show GermIdeal.pullback (m := n) π (sumIdeal (idealPow 𝔪₁.ideal ν) (idealPow 𝔪₂.ideal μ)) = _
    rw [MarkedIdealOperationsTransform.pullback_sumIdeal hπ.contMDiff
        (fun _ _ hg => holomorphicAt_of_mem_idealPow hg) (fun _ _ hg => holomorphicAt_of_mem_idealPow hg),
      BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff h.coh₁,
      BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff h.coh₂]
  have e2 : sumIdeal (idealPow ((idealPow 𝔩 μ).mul 𝔞') ν) (idealPow ((idealPow 𝔩 ν).mul 𝔟') μ) =
      X.mul L := by
    rw [BlowupControlledTransform.idealPow_mul (isCoherent_idealPow h𝔩 _) h𝔞',
      BlowupControlledTransform.idealPow_mul (isCoherent_idealPow h𝔩 _) h𝔟',
      MarkedIdealOperationsTransform.idealPow_idealPow h𝔩, MarkedIdealOperationsTransform.idealPow_idealPow h𝔩,
      Nat.mul_comm ν μ, ← MarkedIdealOperationsTransform.mul_sumIdeal (hol_of_isCoherent hLcoh)
        (fun _ _ hg => holomorphicAt_of_mem_idealPow hg) (fun _ _ hg => holomorphicAt_of_mem_idealPow hg),
      RestrictLeCalculus.mul_comm']
  have hpow₁ : ∀ x g, (idealPow ((idealPow 𝔩 μ).mul 𝔞') ν).mem x g → HolomorphicAt n g x :=
    fun _ _ hg => holomorphicAt_of_mem_idealPow hg
  have hpow₂ : ∀ x g, (idealPow ((idealPow 𝔩 ν).mul 𝔟') μ).mem x g → HolomorphicAt n g x :=
    fun _ _ hg => holomorphicAt_of_mem_idealPow hg
  have hpa : ∀ x g, (idealPow (GermIdeal.pullback (m := n) π 𝔪₁.ideal) ν).mem x g → HolomorphicAt n g x :=
    fun _ _ hg => holomorphicAt_of_mem_idealPow hg
  have hpb : ∀ x g, (idealPow (GermIdeal.pullback (m := n) π 𝔪₂.ideal) μ).mem x g → HolomorphicAt n g x :=
    fun _ _ hg => holomorphicAt_of_mem_idealPow hg
  have fwd : RestrictLe W (𝔰'.mul L) (X.mul L) := by
    rw [RestrictLeCalculus.mul_comm' 𝔰' L, ← e2]
    refine RestrictLeCalculus.RestrictLe.trans s2 ?_
    rw [e1]
    exact restrictLe_sumIdeal hpow₁ hpow₂
      (restrictLe_idealPow (hol_of_isCoherent (IdealWeightPowers.isCoherent_mul (isCoherent_idealPow h𝔩 _) h𝔞'))
        a1 ν)
      (restrictLe_idealPow (hol_of_isCoherent (IdealWeightPowers.isCoherent_mul (isCoherent_idealPow h𝔩 _) h𝔟'))
        b1 μ)
  have bwd : RestrictLe W (X.mul L) (𝔰'.mul L) := by
    rw [RestrictLeCalculus.mul_comm' 𝔰' L, ← e2]
    refine RestrictLeCalculus.RestrictLe.trans ?_ s1
    rw [e1]
    exact restrictLe_sumIdeal hpa hpb
      (restrictLe_idealPow (hol_of_isCoherent (isCoherent_pullback hπ.contMDiff h.coh₁)) a2 ν)
      (restrictLe_idealPow (hol_of_isCoherent (isCoherent_pullback hπ.contMDiff h.coh₂)) b2 μ)
  have hinv : RestrictedIdealQuotient.IsInvertibleAlong n W L :=
    isInvertibleAlong_geoStrictTransform hπ 𝔪₁.N (μ * ν)
  exact ⟨rfl, rfl, rfl, RestrictLeCalculus.restrictLe_of_restrictLe_mul_mul h𝔰' hXcoh hinv fwd,
    RestrictLeCalculus.restrictLe_of_restrictLe_mul_mul hXcoh h𝔰' hinv bwd⟩

/-- **One step of `le:operations` (2) along `N`**: the transform of a product is restricted-equivalent to the
product of the transforms. -/
theorem geoTransform_mul_restrictEquiv {𝔪₁ 𝔪₂ : MarkedIdeal n M} (h : IsSubmanifoldPair 𝔪₁ 𝔪₂) {C : Set M}
    {π : M' → M} (hπ : IsBlowupAlong n C π) (hC₁ : 𝔪₁.IsAdmissibleCentre C)
    (hC₂ : 𝔪₂.IsAdmissibleCentre C) :
    RestrictEquiv ((MarkedIdealOperationsTransform.MarkedIdeal.mul 𝔪₁ 𝔪₂).geoTransform C π)
      (MarkedIdealOperationsTransform.MarkedIdeal.mul (𝔪₁.geoTransform C π) (𝔪₂.geoTransform C π)) := by
  set 𝔭 := MarkedIdealOperationsTransform.MarkedIdeal.mul 𝔪₁ 𝔪₂ with h𝔭
  have hN := h.isClosedSubmanifold
  have hN₂ : IsClosedSubmanifold n 𝔪₂.N := h.N_eq ▸ hN
  have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have h𝔩 : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).IsCoherent :=
    isCoherent_pullback hπ.contMDiff hIC
  set 𝔩 := GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C) with h𝔩def
  set μ := 𝔪₁.d
  set ν := 𝔪₂.d
  have h𝔭coh : 𝔭.ideal.IsCoherent := IdealWeightPowers.isCoherent_mul h.coh₁ h.coh₂
  have hC𝔭 : 𝔭.IsAdmissibleCentre C :=
    MarkedIdealOperationsTransform.MarkedIdeal.IsAdmissibleCentre.mul h.N_eq hC₁ hC₂
  have h𝔞' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN h.coh₁ hC₁ hπ
  have h𝔟' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN₂ h.coh₂ hC₂ hπ
  have h𝔭' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (𝔪 := 𝔭) hN h𝔭coh hC𝔭 hπ
  obtain ⟨a1, a2⟩ := restrictLe_pullback_geoTransform hN h.coh₁ hC₁ hπ
  obtain ⟨b1, b2⟩ := restrictLe_pullback_geoTransform hN₂ h.coh₂ hC₂ hπ
  obtain ⟨p1, p2⟩ := restrictLe_pullback_geoTransform (𝔪 := 𝔭) hN h𝔭coh hC𝔭 hπ
  have hW₂ : (𝔪₂.geoTransform C π).N = (𝔪₁.geoTransform C π).N := by
    rw [geoTransform_N, geoTransform_N, h.N_eq]
  rw [hW₂] at b1 b2
  set W := (𝔪₁.geoTransform C π).N with hWdef
  set 𝔞' := (𝔪₁.geoTransform C π).ideal
  set 𝔟' := (𝔪₂.geoTransform C π).ideal
  set 𝔭' := (𝔭.geoTransform C π).ideal
  set L := idealPow 𝔩 (μ + ν) with hL
  set Y := 𝔞'.mul 𝔟' with hY
  have hYcoh : Y.IsCoherent := IdealWeightPowers.isCoherent_mul h𝔞' h𝔟'
  have e1 : GermIdeal.pullback (m := n) π 𝔭.ideal =
      (GermIdeal.pullback (m := n) π 𝔪₁.ideal).mul (GermIdeal.pullback (m := n) π 𝔪₂.ideal) :=
    GermIdealTotalTransform.pullback_mul hπ.contMDiff h.coh₁ h.coh₂
  have e2 : ((idealPow 𝔩 μ).mul 𝔞').mul ((idealPow 𝔩 ν).mul 𝔟') = Y.mul L := by
    rw [BlowupControlledTransform.mul_mul_mul_comm (isCoherent_idealPow h𝔩 _) h𝔞' (isCoherent_idealPow h𝔩 _)
      h𝔟', ← RestrictLeCalculus.idealPow_add h𝔩, RestrictLeCalculus.mul_comm']
  have fwd : RestrictLe W (𝔭'.mul L) (Y.mul L) := by
    rw [RestrictLeCalculus.mul_comm' 𝔭' L, ← e2]
    refine RestrictLeCalculus.RestrictLe.trans p2 ?_
    rw [e1]
    exact restrictLe_mul
      (hol_of_isCoherent (IdealWeightPowers.isCoherent_mul (isCoherent_idealPow h𝔩 _) h𝔞'))
      (hol_of_isCoherent (IdealWeightPowers.isCoherent_mul (isCoherent_idealPow h𝔩 _) h𝔟')) a1 b1
  have bwd : RestrictLe W (Y.mul L) (𝔭'.mul L) := by
    rw [RestrictLeCalculus.mul_comm' 𝔭' L, ← e2]
    refine RestrictLeCalculus.RestrictLe.trans ?_ p1
    rw [e1]
    exact restrictLe_mul (hol_of_isCoherent (isCoherent_pullback hπ.contMDiff h.coh₁))
      (hol_of_isCoherent (isCoherent_pullback hπ.contMDiff h.coh₂)) a2 b2
  have hinv : RestrictedIdealQuotient.IsInvertibleAlong n W L :=
    isInvertibleAlong_geoStrictTransform hπ 𝔪₁.N (μ + ν)
  exact ⟨rfl, rfl, rfl, RestrictLeCalculus.restrictLe_of_restrictLe_mul_mul h𝔭' hYcoh hinv fwd,
    RestrictLeCalculus.restrictLe_of_restrictLe_mul_mul hYcoh h𝔭' hinv bwd⟩

/-- **The cosupport of a sum along `N`** (marks `≥ 1`): `cosupp(𝔪₁ + 𝔪₂) = cosupp 𝔪₁ ∩ cosupp 𝔪₂`. -/
theorem cosupp_add_along {𝔪₁ 𝔪₂ : MarkedIdeal n M} (h : IsSubmanifoldPair 𝔪₁ 𝔪₂) (hd₁ : 1 ≤ 𝔪₁.d)
    (hd₂ : 1 ≤ 𝔪₂.d) :
    (MarkedIdealOperationsTransform.MarkedIdeal.add 𝔪₁ 𝔪₂).cosupp = 𝔪₁.cosupp ∩ 𝔪₂.cosupp := by
  show cosupport n 𝔪₁.N (sumIdeal (idealPow 𝔪₁.ideal 𝔪₂.d) (idealPow 𝔪₂.ideal 𝔪₁.d)) (𝔪₁.d * 𝔪₂.d) =
    cosupport n 𝔪₁.N 𝔪₁.ideal 𝔪₁.d ∩ cosupport n 𝔪₂.N 𝔪₂.ideal 𝔪₂.d
  rw [← h.N_eq]
  exact cosupport_sumIdeal_idealPow_along h.isClosedSubmanifold.2 (hol_of_isCoherent h.coh₁)
    (hol_of_isCoherent h.coh₂) hd₁ hd₂

/-- **A centre is admissible for a sum iff it is admissible for both summands** (along `N`, marks `≥ 1`). -/
theorem isAdmissibleCentre_add_iff_along {𝔪₁ 𝔪₂ : MarkedIdeal n M} (h : IsSubmanifoldPair 𝔪₁ 𝔪₂)
    (hd₁ : 1 ≤ 𝔪₁.d) (hd₂ : 1 ≤ 𝔪₂.d) {C : Set M} :
    (MarkedIdealOperationsTransform.MarkedIdeal.add 𝔪₁ 𝔪₂).IsAdmissibleCentre C ↔
      𝔪₁.IsAdmissibleCentre C ∧ 𝔪₂.IsAdmissibleCentre C := by
  simp only [IsAdmissibleCentre, cosupp_add_along h hd₁ hd₂, subset_inter_iff]
  show _ ∧ _ ∧ NormalCrossings.HasNormalCrossings n C 𝔪₁.E ↔ _
  rw [← h.E_eq]
  tauto

/-- One admissible step keeps a pair on a closed submanifold such a pair. -/
theorem IsSubmanifoldPair.geoTransform {𝔪₁ 𝔪₂ : MarkedIdeal n M} (h : IsSubmanifoldPair 𝔪₁ 𝔪₂) {C : Set M}
    {π : M' → M} (hπ : IsBlowupAlong n C π) (hC₁ : 𝔪₁.IsAdmissibleCentre C)
    (hC₂ : 𝔪₂.IsAdmissibleCentre C) : IsSubmanifoldPair (𝔪₁.geoTransform C π) (𝔪₂.geoTransform C π) where
  N_eq := by rw [geoTransform_N, geoTransform_N, h.N_eq]
  E_eq := by rw [geoTransform_E, geoTransform_E, h.E_eq]
  isClosedSubmanifold := isClosedSubmanifold_geoTransform_N h.isClosedSubmanifold hC₁ hπ
  coh₁ := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre h.isClosedSubmanifold h.coh₁
    hC₁ hπ
  coh₂ := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre
    (h.N_eq ▸ h.isClosedSubmanifold) h.coh₂ hC₂ hπ

/-! ### Along towers -/

section Tower

open BlowupTowers

variable {X : CMfd.{u} n}

/-- **Włodarczyk `le:operations` (1) along a closed submanifold `N`** (same `E`, marks `≥ 1`): the multiple test
blow-ups of `𝔪₁ + 𝔪₂` are exactly the simultaneous multiple test blow-ups of `𝔪₁` and `𝔪₂`, and along them
`(𝔪₁ + 𝔪₂)_T` is restricted-equivalent to `(𝔪₁)_T + (𝔪₂)_T` (the stages stay pairs on closed submanifolds and the
transforms of the sum have coherent ideals). -/
theorem geoTransformAlong_add_along (𝔪₁ 𝔪₂ : MarkedIdeal n X) (h : IsSubmanifoldPair 𝔪₁ 𝔪₂)
    (hd₁ : 1 ≤ 𝔪₁.d) (hd₂ : 1 ≤ 𝔪₂.d) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      (IsGeoTestTower (MarkedIdealOperationsTransform.MarkedIdeal.add 𝔪₁ 𝔪₂) T ↔
        IsGeoTestTower 𝔪₁ T ∧ IsGeoTestTower 𝔪₂ T) ∧
      (IsGeoTestTower 𝔪₁ T → IsGeoTestTower 𝔪₂ T →
        RestrictEquiv (geoTransformAlong (MarkedIdealOperationsTransform.MarkedIdeal.add 𝔪₁ 𝔪₂) T)
          (MarkedIdealOperationsTransform.MarkedIdeal.add (geoTransformAlong 𝔪₁ T) (geoTransformAlong 𝔪₂ T)) ∧
        IsSubmanifoldPair (geoTransformAlong 𝔪₁ T) (geoTransformAlong 𝔪₂ T) ∧
        (geoTransformAlong (MarkedIdealOperationsTransform.MarkedIdeal.add 𝔪₁ 𝔪₂) T).ideal.IsCoherent)
  | _, .refl => ⟨by simp [IsGeoTestTower], fun _ _ =>
      ⟨RestrictEquiv.refl (isCoherent_sumIdeal (isCoherent_idealPow h.coh₁ _) (isCoherent_idealPow h.coh₂ _)),
        h, isCoherent_sumIdeal (isCoherent_idealPow h.coh₁ _) (isCoherent_idealPow h.coh₂ _)⟩⟩
  | _, .step T C π hπ => by
      obtain ⟨ihT, ihE⟩ := geoTransformAlong_add_along 𝔪₁ 𝔪₂ h hd₁ hd₂ T
      have hd₁T : 1 ≤ (geoTransformAlong 𝔪₁ T).d := by rw [d_geoTransformAlong]; exact hd₁
      have hd₂T : 1 ≤ (geoTransformAlong 𝔪₂ T).d := by rw [d_geoTransformAlong]; exact hd₂
      refine ⟨?_, fun h₁ h₂ => ?_⟩
      · simp only [isGeoTestTower_step_iff]
        constructor
        · rintro ⟨hT, hC⟩
          obtain ⟨hT₁, hT₂⟩ := ihT.mp hT
          obtain ⟨heq, hpair, -⟩ := ihE hT₁ hT₂
          rw [heq.isAdmissibleCentre_iff, isAdmissibleCentre_add_iff_along hpair hd₁T hd₂T] at hC
          exact ⟨⟨hT₁, hC.1⟩, hT₂, hC.2⟩
        · rintro ⟨⟨hT₁, hC₁⟩, hT₂, hC₂⟩
          obtain ⟨heq, hpair, -⟩ := ihE hT₁ hT₂
          refine ⟨ihT.mpr ⟨hT₁, hT₂⟩, ?_⟩
          rw [heq.isAdmissibleCentre_iff, isAdmissibleCentre_add_iff_along hpair hd₁T hd₂T]
          exact ⟨hC₁, hC₂⟩
      · obtain ⟨hT₁, hC₁⟩ := (isGeoTestTower_step_iff 𝔪₁ T C π hπ).mp h₁
        obtain ⟨hT₂, hC₂⟩ := (isGeoTestTower_step_iff 𝔪₂ T C π hπ).mp h₂
        obtain ⟨heq, hpair, hcoh𝔰⟩ := ihE hT₁ hT₂
        have hcohA : (MarkedIdealOperationsTransform.MarkedIdeal.add (geoTransformAlong 𝔪₁ T)
            (geoTransformAlong 𝔪₂ T)).ideal.IsCoherent :=
          isCoherent_sumIdeal (isCoherent_idealPow hpair.coh₁ _) (isCoherent_idealPow hpair.coh₂ _)
        have hNs : IsClosed (geoTransformAlong (MarkedIdealOperationsTransform.MarkedIdeal.add 𝔪₁ 𝔪₂) T).N := by
          rw [heq.N_eq]
          exact hpair.isClosedSubmanifold.1
        have hstep := heq.geoTransform_eq hNs hcoh𝔰 hcohA hπ.contMDiff (C := C)
        have hCA := IsAdmissibleCentre.add hpair hC₁ hC₂
        refine ⟨?_, hpair.geoTransform hπ hC₁ hC₂, ?_⟩
        · rw [geoTransformAlong_step, hstep]
          exact geoTransform_add_restrictEquiv hpair hπ hC₁ hC₂
        · rw [geoTransformAlong_step, hstep]
          exact HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre
            hpair.isClosedSubmanifold hcohA hCA hπ

/-- **Włodarczyk `le:operations` (2) along a closed submanifold `N`** (same `E`): a simultaneous multiple test
blow-up of `𝔪₁` and `𝔪₂` is one of `𝔪₁ · 𝔪₂`, and along it `(𝔪₁ · 𝔪₂)_T` is restricted-equivalent to
`(𝔪₁)_T · (𝔪₂)_T`. -/
theorem geoTransformAlong_mul_along (𝔪₁ 𝔪₂ : MarkedIdeal n X) (h : IsSubmanifoldPair 𝔪₁ 𝔪₂) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪₁ T → IsGeoTestTower 𝔪₂ T →
      IsGeoTestTower (MarkedIdealOperationsTransform.MarkedIdeal.mul 𝔪₁ 𝔪₂) T ∧
      RestrictEquiv (geoTransformAlong (MarkedIdealOperationsTransform.MarkedIdeal.mul 𝔪₁ 𝔪₂) T)
        (MarkedIdealOperationsTransform.MarkedIdeal.mul (geoTransformAlong 𝔪₁ T) (geoTransformAlong 𝔪₂ T)) ∧
      IsSubmanifoldPair (geoTransformAlong 𝔪₁ T) (geoTransformAlong 𝔪₂ T) ∧
      (geoTransformAlong (MarkedIdealOperationsTransform.MarkedIdeal.mul 𝔪₁ 𝔪₂) T).ideal.IsCoherent
  | _, .refl, _, _ => ⟨trivial, RestrictEquiv.refl (IdealWeightPowers.isCoherent_mul h.coh₁ h.coh₂), h,
      IdealWeightPowers.isCoherent_mul h.coh₁ h.coh₂⟩
  | _, .step T C π hπ, h₁, h₂ => by
      obtain ⟨hT₁, hC₁⟩ := (isGeoTestTower_step_iff 𝔪₁ T C π hπ).mp h₁
      obtain ⟨hT₂, hC₂⟩ := (isGeoTestTower_step_iff 𝔪₂ T C π hπ).mp h₂
      obtain ⟨hT, heq, hpair, hcoh𝔭⟩ := geoTransformAlong_mul_along 𝔪₁ 𝔪₂ h T hT₁ hT₂
      have hcohM : (MarkedIdealOperationsTransform.MarkedIdeal.mul (geoTransformAlong 𝔪₁ T)
          (geoTransformAlong 𝔪₂ T)).ideal.IsCoherent := IdealWeightPowers.isCoherent_mul hpair.coh₁ hpair.coh₂
      have hNs : IsClosed (geoTransformAlong (MarkedIdealOperationsTransform.MarkedIdeal.mul 𝔪₁ 𝔪₂) T).N := by
        rw [heq.N_eq]
        exact hpair.isClosedSubmanifold.1
      have hstep := heq.geoTransform_eq hNs hcoh𝔭 hcohM hπ.contMDiff (C := C)
      have hCM := MarkedIdealOperationsTransform.MarkedIdeal.IsAdmissibleCentre.mul hpair.N_eq hC₁ hC₂
      refine ⟨(isGeoTestTower_step_iff _ T C π hπ).mpr ⟨hT, heq.isAdmissibleCentre_iff.mpr hCM⟩, ?_,
        hpair.geoTransform hπ hC₁ hC₂, ?_⟩
      · rw [geoTransformAlong_step, hstep]
        exact geoTransform_mul_restrictEquiv hpair hπ hC₁ hC₂
      · rw [geoTransformAlong_step, hstep]
        exact HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre
          hpair.isClosedSubmanifold hcohM hCM hπ

end Tower

end MarkedIdeal

end

end Hironaka.MarkedIdealOperationsAlong
