/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.CodimOneCentre
import Hironaka.Blowup.ExceptionalPushforwardAlong
import Hironaka.Invariant.MemberPullback
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.BlowupSNCTransform
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Blowup.LiftedOpenModel
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NestedFlattening
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.RestrictLe
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Blowing up a centre of codimension one in `N` inside the support along `N`

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), §2.7, Lemma `le:codim1` (Villamayor): "After the blow-up `σ` at
such a component `C ⊆ supp(𝓘, μ)` the induced support `supp(𝓘', μ)` does not intersect the exceptional divisor of
`σ`", applied to the marked ideals `(M, N, E, 𝔞, d)` of the induction, whose support lies in `N`; Włodarczyk 2009
(`wlodarczyk09-analytic-resolution`), Step 1ba.

Pointwise form (`notMem_cosupp_geoTransform_of_codim_one_along`): let `(M, N, E, 𝔞, d)` have `N` a
closed submanifold, `𝔞` coherent, `d ≥ 1`, let `π` be the blowup along `C ⊆ cosupp(𝔞|_N, d)`, and
let `z` lie over `x = π z ∈ C`, where `C` is regular of dimension `k` and `N` of dimension `k + 1`
(`C` has codimension one in `N` at `x`) and `ord_x(𝔞|_N) ≤ d` (`x ∉ cosupp(𝔞|_N, d + 1)`).  Then
`z` is not in the cosupport of the transform `(M', N', E', 𝔞', d)`.

Proof.  Nested flattening coordinates `Φ` at `x` (`NestedFlattening.exists_nested_flattening`):
`C = ℂ^k × 0`, `N = ℂ^{k+1} × 0`; put `u = Φ_k`.  By Hadamard's lemma in these coordinates
(`BlowupFlatCoordinates.exists_eq_sum_flatCoord`) every germ of `𝓘_C` at a point of `N` near `x`
is, on `N`, a multiple of `u` (the coordinates `Φ_i`, `i ≥ k + 1`, vanish on `N`); with the Hadamard
bridge along `N` (`HadamardBridgeAlong.restrictLe_idealPow_vanishingIdeal_of_subset_cosupport`,
`Res_N 𝔞 ⊆ Res_N 𝓘_C^d`) and powers of restricted inclusions
(`MarkedIdealOperationsAlong.restrictLe_idealPow`), an element `f ∈ 𝔞_x` of order exactly `d` along
`N` is `f = c · u^d` on `N` near `x`, with `c(x) ≠ 0`.  In a monomial chart `W` of the blowup around
`z ∈ N'`, the chart index `j ≥ k` satisfies `j < k + 1` (`z ∈ N'`,
`BlowupSNCTransform.mem_geoStrictTransform_iff_of_chart`), so `j = k` and `u ∘ π = W_j`, which
generates `𝒪(-D)` near `z` (`BlowupStrictIdeal.exceptionalDivisor_mem_iff_of_chart`).  Hence
`f ∘ π = (c ∘ π) · W_j^d` on `N'` near `z`, and `c ∘ π` lies in
`𝔞' = (Res_{N'} π^*𝔞 : 𝒪(-dD))` at `z`; it does not vanish at `z`, so `z ∉ cosupp(𝔞'|_{N'}, d)`.

For a marked ideal of maximal order along `N` (`HomogenizedIdealAlong.IsMaximalOrderAlong`: `ord(𝔞|_N) ≤ d`
everywhere) and a centre of codimension one in `N` at each of its points, the cosupport of the transform misses the
exceptional divisor.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CodimOneCentreAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupStrictSubmanifold BlowupStrictIdeal BlowupExceptionalDivisor BlowupDerivativeIdeal BlowupSNCTransform NormalCrossings RelativePrincipalizationSpan MarkedIdeals IdealWeightPowers CodimOneCentre RestrictedIdealWeight RestrictedIdealExtension InvertibleIdealQuotient MemberPullback HomogenizedIdealAlong

noncomputable section

variable {n : ℕ}

section Local

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Restricted span membership passes to a smaller set. -/
theorem isInSpanOnAt_subset {W W' : Set X} (hWW' : W' ⊆ W) {S : (X → ℂ) → Prop} {x : X}
    {g : X → ℂ} (hg : IsInSpanOnAt (n := n) W S x g) : IsInSpanOnAt (n := n) W' S x g := by
  obtain ⟨K, s, a, hs, ha, hsum⟩ := hg
  exact ⟨K, s, a, hs, ha, hsum.mono fun y hy hyW' => hy (hWW' hyW')⟩

/-- Vanishing to order `q` along `N` passes to germs that agree with it on `N` near the point. -/
theorem VanishesToOrderOn.congr_on {N : Set X} {x : X} {q : ℕ} {f g : X → ℂ}
    (hf : VanishesToOrderOn n N x q f) (hfg : ∀ᶠ y in 𝓝 x, y ∈ N → f y = g y) :
    VanishesToOrderOn n N x q g := by
  obtain ⟨h, hh, hfh⟩ := hf
  exact ⟨h, hh, by filter_upwards [hfh, hfg] with y h1 h2 hy; rw [← h2 hy, h1 hy]⟩

/-- **An element of order `d` along `N` in `(u^d)|_N` has a unit cofactor**: if `f = c · u^d` on
`N` near `x ∈ N` with `u(x) = 0` and `f` not of order `≥ d + 1` along `N` at `x`, then
`c(x) ≠ 0`. -/
theorem apply_ne_zero_of_not_vanishesToOrderOn_on {N : Set X} {x : X} (hxN : x ∈ N)
    {u c f : X → ℂ} (hu : HolomorphicAt n u x) (hux : u x = 0) (hc : HolomorphicAt n c x) {d : ℕ}
    (hfc : ∀ᶠ y in 𝓝 x, y ∈ N → f y = c y * u y ^ d)
    (hfo : ¬ VanishesToOrderOn n N x (d + 1) f) : c x ≠ 0 := by
  intro hc0
  apply hfo
  have h1 : VanishesToOrderOn n N x 1 c := (vanishesToOrderOn_one_iff hxN hc).mpr hc0
  have h2 := h1.mul (vanishesToOrderOn_pow hxN hu hux d)
  rw [Nat.add_comm] at h2
  exact VanishesToOrderOn.congr_on h2 (hfc.mono fun y hy hyN => (hy hyN).symm)

/-- **On `N`, the ideal of a hypersurface `C` of `N` is generated by one flat coordinate.**  If
`Φ` flattens `C` onto `ℂ^k × 0` and `N` onto `ℂ^{k+1} × 0` near `x`, then near every point `y` of
`N` in the flattening domain, every germ of `𝓘_C` at `y` agrees on `N` with a multiple of
`Φ_k`. -/
theorem isInSpanOnAt_flatCoord_of_mem_vanishingIdeal {C N : Set X} {x : X} {k : ℕ}
    (hkn : k < n) (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦt : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))
    (hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n (k + 1)))
    {y : X} (hy : y ∈ flatDomain Φ) {g : X → ℂ} (hg : (vanishingIdeal (n := n) C).mem y g) :
    IsInSpanOnAt (n := n) N (· = flatCoord Φ ⟨k, hkn⟩) y g := by
  obtain ⟨b, hb0, hbhol, hbeq⟩ := exists_eq_sum_flatCoord Φ hΦt hflatC hy hg
  refine ⟨1, fun _ => flatCoord Φ ⟨k, hkn⟩, fun _ => b ⟨k, hkn⟩, fun _ => rfl,
    fun _ => hbhol _, ?_⟩
  filter_upwards [hbeq, (isOpen_flatDomain Φ).mem_nhds hy] with p hp hpV hpN
  rw [hp, Finset.sum_eq_single (⟨k, hkn⟩ : Fin n)]
  · simp
  · intro i _ hi
    by_cases hik : i.1 < k
    · rw [hb0 i hik]; simp
    · have hik' : k + 1 ≤ i.1 := by
        have : i.1 ≠ k := fun h => hi (Fin.ext h)
        omega
      have hN := (hflatN hpV.1 hpV.2).mp hpN
      rw [show flatCoord Φ i p = Φ.toFun (chartAt (ComplexModel n) x p) i from rfl, hN i hik']
      simp
  · simp

end Local

section Blowup

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

open MarkedIdeal in
/-- **`le:codim1` inside `N`, pointwise.**  Let `(M, N, E, 𝔞, d)` have `N` a closed submanifold, `𝔞`
coherent, `d ≥ 1`, and let the centre `C` of the blowup `π` lie in its cosupport.  If at `x = π z`
the centre is regular of dimension `k` and `N` of dimension `k + 1` (codimension one in `N`), and
`ord_x(𝔞|_N) ≤ d`, then `z` is not in the cosupport of the transform. -/
theorem notMem_cosupp_geoTransform_of_codim_one_along (hπ : IsBlowupAlong n C π)
    {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) (hsub : C ⊆ 𝔪.cosupp) {z : Y} (hzC : π z ∈ C) {k : ℕ}
    (hCk : RegularAtDim (n := n) C (π z) k) (hNk : RegularAtDim (n := n) 𝔪.N (π z) (k + 1))
    (hord : π z ∉ cosupport n 𝔪.N 𝔪.ideal (𝔪.d + 1)) :
    z ∉ (𝔪.geoTransform C π).cosupp := by
  classical
  have hCN : C ⊆ 𝔪.N := hsub.trans 𝔪.cosupp_subset_N
  have hxN : π z ∈ 𝔪.N := hCN hzC
  have hkn : k < n := by obtain ⟨h, -⟩ := hNk; omega
  set t : Fin n := ⟨k, hkn⟩ with ht_def
  -- nested flattening coordinates at `x = π z`
  obtain ⟨Φ, hΦt, hΦ0, hflat⟩ := NestedFlattening.exists_nested_flattening (Nat.le_succ k) hCk hNk hCN
  have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n k) :=
    fun hy hyΦ => (hflat hy hyΦ).1
  have hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ 𝔪.N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n (k + 1)) :=
    fun hy hyΦ => (hflat hy hyΦ).2
  have hx' : π z ∈ flatDomain Φ := mem_flatDomain_self Φ
  set u : X → ℂ := flatCoord Φ t with hu_def
  have huhol : ∀ y ∈ flatDomain Φ, HolomorphicAt n u y := fun y hy => holomorphicAt_flatCoord Φ t hy
  have hux : u (π z) = 0 := by
    show Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) t = 0
    rw [show chartAt (ComplexModel n) (π z) (π z) = (complexChartAt (n := n) (π z)).val (π z) from rfl,
      hΦ0]
    rfl
  -- the hyperplane `H = {Φ_k = 0}` and its ideal, generated by `u`
  set H : Set X := {p | Φ.toFun (chartAt (ComplexModel n) (π z) p) t = 0} with hH_def
  have hgenH : ∀ y ∈ flatDomain Φ, ∀ g, (vanishingIdeal (n := n) H).mem y g ↔
      IsInSpanAt (n := n) (· = u) y g := fun y hy g =>
    vanishingIdeal_mem_iff_flatCoord Φ (A := H) (t := t) (fun _ _ => Iff.rfl) hy g
  -- `Res_{N ∩ V} 𝓘_C ⊆ Res_{N ∩ V} 𝓘_H`, `V` the flattening domain
  have hCH : RestrictLe (𝔪.N ∩ flatDomain Φ) (vanishingIdeal (n := n) C)
      (vanishingIdeal (n := n) H) := by
    intro y hy g hg
    have h1 := isInSpanOnAt_flatCoord_of_mem_vanishingIdeal hkn Φ hΦt hflatC hflatN hy.2 hg
    refine isInSpanOnAt_subset inter_subset_left (IsInSpanOnAt.mono (fun s hs => ?_) h1)
    rw [hs]
    exact (hgenH y hy.2 _).mpr (isInSpanAt_self rfl (huhol y hy.2))
  have hCHd := MarkedIdealOperationsAlong.restrictLe_idealPow
    (fun y g hg => (hg : (vanishingIdeal (n := n) H).mem y g).1) hCH 𝔪.d
  -- an element of `𝔞` of order exactly `d` along `N` at `x`
  obtain ⟨f, hf, hfo⟩ : ∃ f, 𝔪.ideal.mem (π z) f ∧ ¬ VanishesToOrderOn n 𝔪.N (π z) (𝔪.d + 1) f := by
    by_contra hall
    push Not at hall
    exact hord ⟨hxN, fun f hf => hall f hf⟩
  have hfhol : HolomorphicAt n f (π z) :=
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hf
  -- the Hadamard bridge along `N`, then `𝓘_C^d ⊆ (u^d)` on `N`: `f = c · u^d` on `N`
  have h1 := HadamardBridgeAlong.restrictLe_idealPow_vanishingIdeal_of_subset_cosupport h𝔞 hN hπ.1
    hCN hsub (π z) hxN f hf
  have h2 : IsInSpanOnAt (n := n) (𝔪.N ∩ flatDomain Φ) (· = fun p => u p ^ 𝔪.d) (π z) f := by
    refine IsInSpanOnAt.trans (fun s hs => ?_) (isInSpanOnAt_subset inter_subset_left h1)
    refine IsInSpanOnAt.trans (fun s' hs' => IsInSpanAt.restrict ?_) (hCHd (π z) ⟨hxN, hx'⟩ s hs)
    exact (idealPow_mem_iff_of_generator huhol hgenH 𝔪.d (π z) hx' s').mp hs'
  obtain ⟨K, s, a, hs, ha, hsum⟩ := h2
  set c : X → ℂ := fun p => ∑ i, a i p with hc_def
  have hc : HolomorphicAt n c (π z) := HolomorphicAt.sum _ fun i _ => ha i
  have hfc : ∀ᶠ p in 𝓝 (π z), p ∈ 𝔪.N → f p = c p * u p ^ 𝔪.d := by
    filter_upwards [hsum, (isOpen_flatDomain Φ).mem_nhds hx'] with p hp hpV hpN
    rw [hp ⟨hpN, hpV⟩, hc_def, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hs i]
  have hcx : c (π z) ≠ 0 :=
    apply_ne_zero_of_not_vanishesToOrderOn_on hxN (huhol _ hx') hux hc hfc hfo
  -- the transform: assume `z` in its cosupport, so `z ∈ N'`
  rintro ⟨hzN, hzord⟩
  change z ∈ geoStrictTransform π C 𝔪.N at hzN
  -- a monomial chart around `z`; as `z ∈ N'`, its index is `k`
  have hflatN' : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ 𝔪.N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈
          coordSubspace (Finset.univ.filter fun i : Fin n => k + 1 ≤ i.1)) :=
    fun hy hyΦ => by rw [coordSubspace_eq_complexCoordinatePlane]; exact hflatN hy hyΦ
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
    exists_monomialLocalInverse hπ hΦt hflatC hx'
  have hNz := (mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatN' hj hO hWs hWeq hℓ hzO).mp
    hzN
  have hjt : j = t := by
    have hj' : j.1 < k + 1 := by
      by_contra hle
      exact hNz.1 (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega)
    exact Fin.ext (by simp only [ht_def]; omega)
  -- `u ∘ π = W_j` on the chart
  have huW : ∀ y ∈ O, u (π y) = W y j := fun y hy => by
    show Φ.toFun (chartAt (ComplexModel n) (π z) (π y)) t = W y j
    rw [← (hWeq y hy).2, monomial_apply, hjt]
    simp
  have hπat : ∀ᶠ y' in 𝓝 z, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π y' :=
    Eventually.of_forall fun y' => hπ.contMDiff y'
  have hWj : ∀ y ∈ O, HolomorphicAt n (fun w => W w j) y := fun y hy => holomorphicAt_coord hO hWs j hy
  -- `𝒪(-D)` is generated by `W_j` on the chart, hence `𝒪(-dD)` by `W_j^d`
  have hgenD : ∀ y ∈ O, ∀ g, (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).mem y g ↔
      IsInSpanAt (n := n) (· = fun w => W w j) y g := fun y hy g => by
    rw [← exceptionalDivisor_ideal hπ, exceptionalDivisor_mem_iff_of_chart hπ hΦt hflatC hj hO hWs
      hWeq hy g, isInSpanAt_range_one_iff]
  -- `c ∘ π` lies in the transformed ideal at `z`
  have hcπ : HolomorphicAt n (fun y => c (π y)) z := hc.comp_contMDiff hπat
  have hmem : (𝔪.geoTransform C π).ideal.mem z (fun y => c (π y)) := by
    refine ⟨hcπ, fun l hl => ?_⟩
    obtain ⟨hlhol, b, hb, hlb⟩ := isInSpanAt_eq_iff.mp
      ((idealPow_mem_iff_of_generator hWj hgenD 𝔪.d z hzO l).mp hl)
    refine ⟨hlhol.mul hcπ, 1, fun _ => fun y => f (π y), fun _ => b, fun _ => ?_, fun _ => hb, ?_⟩
    · have hfπ : HolomorphicAt n (f ∘ π) z := hfhol.comp_contMDiff hπat
      exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul ⟨f, hf, rfl⟩ hfπ
        (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm))
    · have hπc : ContinuousAt π z := hπ.contMDiff.continuous.continuousAt
      filter_upwards [hlb, hO.mem_nhds hzO, hπc.eventually hfc] with y hy1 hyO hy3 hyN
      have hyN' : π y ∈ 𝔪.N :=
        geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hyN
      simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
      rw [hy1, hy3 hyN', huW y hyO]
      ring
  -- but it does not vanish at `z`
  have h3 := (vanishesToOrderOn_one_iff hzN hcπ).mp ((hzord _ hmem).mono hd)
  exact hcx h3

end Blowup

end

end Hironaka.CodimOneCentreAlong
