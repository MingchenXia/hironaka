/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.NormalDerivativeAlong
import Hironaka.MarkedIdeal.CoefficientIdealAlongRestrictionTower
import Hironaka.MarkedIdeal.CoefficientRestrictionTower
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupFibreDirection
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupFunctionTransform
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CoefficientIdeal
import Hironaka.MarkedIdeal.CoefficientIdealAlongRestriction
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Blowup.GlueingTrivialAction
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.HolomorphicTaylorTail
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.HomogenizedIdealAlongTower
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Blowup.LiftedOpenModel
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.MarkedIdeal.NormalDerivativeChart
import Hironaka.MarkedIdeal.NormalDerivativeMonomial
import Hironaka.MarkedIdeal.NormalTaylorOrder
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.MarkedIdeal.RestrictLe
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The restricted coefficient ideal along a submanifold, along multiple test blow-ups: the full statement

The along-`N` form of `CoefficientRestrictionTower` (`N = M`).

For `𝔪 = (X, N, E, 𝔞, μ)` with `N` a closed submanifold, `𝔞` coherent, `μ ≥ 1`, a closed submanifold `S ⊆ N` and a multiple
test blow-up `T` of `𝔪` with centres in the strict transforms of `S`:

* **The invariant** (`GoodAtAlong`): at `p ∈ S_T` there are a flat chart for `S_T` (plane `ℂ^{k_S} × 0`) in which `N_T` is the
  plane `ℂ^{k_N} × 0`, and generators of `𝔞_T` along `N_T` at `p` whose derivatives `∂^L` in the directions `[k_S, k_N)`
  (normal to `S_T`, tangent to `N_T`), `|L| < μ`, restrict on `S_T` into `[𝓓_N^{|L|} 𝔪]_T`.
* `GoodAtAlong.orderGE`: at a good point where each `[𝓓_N^i 𝔪]_T` has order `≥ μ - i` along `S_T`, `𝔞_T` has order `≥ μ`
  along `N_T` (`NormalDerivativeAlong.FlatChart.vanishesToOrderOn_of_nd`).
* `goodAtAlong_tower`: every point of `S_T` is good (`goodAtAlong_refl`; off the centre the generators pull back,
  `goodAtAlong_step_of_notMem`; over the centre the new generators are `h'` with `g ∘ π = W_j^μ h'` on `N'`, and
  `W_j^μ ∂^L h' = W_j^{|L|} (∂^L g) ∘ π` on `N'`, `goodAtAlong_step_of_mem`).
* **`cosupp_coeffAlong_withN_tower_subset`** (`le:S` (2), the inclusion `⊇` of the source, along `N`):
  `supp[𝓒_N(𝔪)|_S]_T ⊆ supp(𝔪_T)`; with `CoefficientIdealAlongRestrictionTower.coeffAlong_restrict_tower`,
  `cosupp_coeffAlong_withN_tower`: `supp[𝓒_N(𝔪)|_S]_T = supp(𝔪_T) ∩ S_T`.
* **`coeffAlong_restrict_tower_iff`** (`le:S` in full along `N`): a tower is a multiple test blow-up of `𝓒_N(𝔪)|_S` iff it is
  one of `𝔪` with centres in the strict transforms of `S`, and then the cosupports correspond as above.

One-blowup tools for the transform along `N'` (`(M', N', E', 𝔞', d)` with `𝔞'` the colon along `N'`): the pullback lies in the
transform (`mem_geoTransform_of_mem_pullback`); off the centre the transform is the pullback on `N'`
(`isInSpanOnAt_pullback_of_mem_geoTransform_of_notMem`); over the centre, for a local equation `l` of the exceptional
divisor, `l^d 𝔞' ⊆ π^*𝔞` on `N'` (`isInSpanOnAt_pow_mul_of_mem_geoTransform`) and every `g ∈ 𝔞` has `g ∘ π = l^d h'` on
`N'` with `h' ∈ 𝔞'` (`exists_mem_geoTransform_eq_pow_mul`, from the Hadamard bridge along `N`).
-/

open Set Filter Metric
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CoefficientIdealAlongRestrictionFull

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder IdealWeightPowers BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal CoefficientIdeal CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdealAlongRestrictionTower NormalTaylorOrder NormalDerivativeChart NormalDerivativeMonomial NormalDerivativeAlong BlowupStrictSubmanifold BlowupFunctionTransform RelativePrincipalizationSpan
open HomogenizedGlueingTower (strictAlong strictAlong_step)

noncomputable section

/-! ### One blowup: the transform along `N'` against the pullback -/

section OneBlowup

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set Y} {π : Z → Y}

/-- **The pullback lies in the transform along `N'`**: `π^*𝔞 ⊆ 𝔞'` (the colon of `π^*𝔞` contains `π^*𝔞`). -/
theorem mem_geoTransform_of_mem_pullback (𝔫 : MarkedIdeal n Y) {z : Z} {G : Z → ℂ}
    (hG : (GermIdeal.pullback (m := n) π 𝔫.ideal).mem z G) : (𝔫.geoTransform C π).ideal.mem z G := by
  have hGhol : HolomorphicAt n G z := (GermIdeal.mem_pullback_iff.mp hG).1
  rw [geoTransform_ideal]
  refine ⟨hGhol, fun t ht => ?_⟩
  have hthol : HolomorphicAt n t z := GermIdealOrder.holomorphicAt_of_mem_idealPow ht
  refine ⟨hthol.mul hGhol, 1, fun _ => G, fun _ => t, fun _ => hG, fun _ => hthol, ?_⟩
  exact Eventually.of_forall fun y _ => by simp

/-- **Off the centre the transform along `N'` is the pullback on `N'`**: for `π z ∉ C`, every germ of `𝔞'` at `z` is on `N'`
a combination of germs of `π^*𝔞` (the ideal of the centre pulls back to the unit ideal near `z`). -/
theorem isInSpanOnAt_pullback_of_mem_geoTransform_of_notMem (hπ : IsBlowupAlong n C π) (𝔫 : MarkedIdeal n Y)
    {z : Z} (hz : π z ∉ C) {f : Z → ℂ} (hf : (𝔫.geoTransform C π).ideal.mem z f) :
    IsInSpanOnAt (n := n) (𝔫.geoTransform C π).N ((GermIdeal.pullback (m := n) π 𝔫.ideal).mem z) z f := by
  have h1 := MarkedIdeals.MarkedIdeal.one_mem_idealPow (n := n)
    (MarkedIdeals.MarkedIdeal.one_mem_pullback_vanishingIdeal (n := n) (π := π) hz hπ.1.1) 𝔫.d
  rw [geoTransform_ideal] at hf
  obtain ⟨K, s, c, hs, hc, hsum⟩ := (hf.2 _ h1).2
  exact ⟨K, s, c, hs, hc, by filter_upwards [hsum] with y hy hyN; simpa using hy hyN⟩

/-- **Over the centre, `l^d 𝔞' ⊆ π^*𝔞` on `N'`** for a local equation `l` of the exceptional divisor. -/
theorem isInSpanOnAt_pow_mul_of_mem_geoTransform (hπ : IsBlowupAlong n C π) (𝔫 : MarkedIdeal n Y) {O : Set Z}
    {l : Z → ℂ} (hl : IsLocalEquation hπ O l) {z : Z} (hzO : z ∈ O) {f : Z → ℂ}
    (hf : (𝔫.geoTransform C π).ideal.mem z f) :
    IsInSpanOnAt (n := n) (𝔫.geoTransform C π).N ((GermIdeal.pullback (m := n) π 𝔫.ideal).mem z) z
      (fun y => l y ^ 𝔫.d * f y) := by
  rw [geoTransform_ideal] at hf
  exact (hf.2 _ (hl.pow_mem 𝔫.d hzO)).2

/-- **The transforms of germs over the centre, along `N'`**: for `𝔫 = (Y, N, E, 𝔞, d)` with `N` a closed submanifold and `𝔞`
coherent, an admissible centre `C`, a local equation `l` of the exceptional divisor on `O ∋ z` and `z ∈ N'`: every `g ∈ 𝔞_{π z}`
has `g ∘ π = l^d h'` on `N'` near `z` with `h' ∈ 𝔞'_z` holomorphic (`𝔞|_N ⊆ 𝓘_C^d|_N` by the Hadamard bridge along `N`). -/
theorem exists_mem_geoTransform_eq_pow_mul (hπ : IsBlowupAlong n C π) (𝔫 : MarkedIdeal n Y)
    (hN : IsClosedSubmanifold n 𝔫.N) (h𝔫 : 𝔫.ideal.IsCoherent) (hC : 𝔫.IsAdmissibleCentre C) {O : Set Z}
    {l : Z → ℂ} (hl : IsLocalEquation hπ O l) {z : Z} (hzO : z ∈ O) (hzN : z ∈ geoStrictTransform π C 𝔫.N)
    {g : Y → ℂ} (hg : 𝔫.ideal.mem (π z) g) :
    ∃ h' : Z → ℂ, HolomorphicAt n h' z ∧ (𝔫.geoTransform C π).ideal.mem z h' ∧
      ∀ᶠ y in 𝓝 z, y ∈ geoStrictTransform π C 𝔫.N → g (π y) = l y ^ 𝔫.d * h' y := by
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hπd : ∀ w, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
    fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
  have hpz : π z ∈ 𝔫.N := geoStrictTransform_subset_preimage hπc hN.1 hzN
  obtain ⟨K, s, a, hs, ha, hsum⟩ :=
    HadamardBridgeAlong.restrictLe_idealPow_vanishingIdeal_of_subset_cosupport h𝔫 hN hC.1 hC.subset_N hC.2.1
      (π z) hpz g hg
  choose s' hs'hol hs'eq using fun i => exists_eq_pow_mul hl hzO (hs i)
  have hhol : HolomorphicAt n (fun y => ∑ i, a i (π y) * s' i y) z :=
    HolomorphicAt.sum _ fun i _ =>
      (HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd) (ha i)).mul (hs'hol i)
  have heq : ∀ᶠ y in 𝓝 z, y ∈ geoStrictTransform π C 𝔫.N →
      g (π y) = l y ^ 𝔫.d * ∑ i, a i (π y) * s' i y := by
    filter_upwards [(hπc.tendsto z).eventually hsum, eventually_all.mpr hs'eq] with y h1 h2 hyN
    have hyN' : π y ∈ 𝔫.N := geoStrictTransform_subset_preimage hπc hN.1 hyN
    rw [h1 hyN', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2i : s i (π y) = l y ^ 𝔫.d * s' i y := h2 i
    rw [h2i]
    ring
  refine ⟨_, hhol, ?_, heq⟩
  rw [geoTransform_ideal]
  refine ⟨hhol, fun t ht => ?_⟩
  obtain ⟨hthol, b, hb, hbeq⟩ := isInSpanAt_eq_iff.mp ((hl.idealPow_mem_iff 𝔫.d z hzO t).mp ht)
  have hgπ : (GermIdeal.pullback (m := n) π 𝔫.ideal).mem z (g ∘ π) :=
    GermIdeal.mem_pullback_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self
      (S := fun t => ∃ a, 𝔫.ideal.mem (π z) a ∧ t = a ∘ π) ⟨g, hg, rfl⟩
      (HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd)
        (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔫 _ _ hg)))
  refine ⟨hthol.mul hhol, 1, fun _ => g ∘ π, fun _ => b, fun _ => hgπ, fun _ => hb, ?_⟩
  filter_upwards [hbeq, heq] with y h1 h2 hyN
  show t y * (∑ i, a i (π y) * s' i y) = ∑ _ : Fin 1, b y * (g ∘ π) y
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, h1, Function.comp_apply, h2 hyN]
  ring

/-- **Restricted spans pull back** along a holomorphic map, onto a set mapped into the old one. -/
theorem isInSpanOnAt_comp {π : Z → Y} (hπc : Continuous π)
    (hπd : ∀ w, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w) {A : Set Y} {A' : Set Z}
    (hA : A' ⊆ π ⁻¹' A) {S : (Y → ℂ) → Prop} {z : Z} {a : Y → ℂ} (ha : IsInSpanOnAt (n := n) A S (π z) a) :
    IsInSpanOnAt (n := n) A' (fun t => ∃ s, S s ∧ t = s ∘ π) z (a ∘ π) := by
  obtain ⟨K, s, c, hs, hc, hsum⟩ := ha
  refine ⟨K, fun i => s i ∘ π, fun i => c i ∘ π, fun i => ⟨s i, hs i, rfl⟩,
    fun i => HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd) (hc i), ?_⟩
  filter_upwards [(hπc.tendsto z).eventually hsum] with y hy hyA
  exact hy (hA hyA)

end OneBlowup

/-! ### The invariant -/

section Invariant

variable {n : ℕ} {X : CMfd.{u} n}

/-- **The coefficient invariant along `N`** at a point `p` of the strict transform `S_T`: a flat chart `c` for `S_T` at `p`
(plane `ℂ^{k_S} × 0`) in which `N_T` is the plane `ℂ^{k_N} × 0` (`k_S ≤ k_N ≤ n`), and generators `G` of `𝔞_T` along `N_T`
at `p` (germs of `𝔞_T` such that every germ of `𝔞_T` at `p` is on `N_T` a combination of them) such that for every
generator `g` and every list `L` of directions in `[k_S, k_N)` with `|L| < μ`, the derivative `∂^L g` restricts on `S_T` near
`p` into `[𝓓_N^{|L|} 𝔪]_T`. -/
def GoodAtAlong (𝔪 : MarkedIdeal n X) (S : Set X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (p : Y) : Prop :=
  ∃ (kS kN : ℕ) (_ : kS ≤ kN) (_ : kN ≤ n) (c : FlatChart n (strictAlong T S) p kS),
    (∀ {y : Y}, y ∈ (chartAt (ComplexModel n) p).source → chartAt (ComplexModel n) p y ∈ c.Φ.source →
      (y ∈ (geoTransformAlong 𝔪 T).N ↔
        c.Φ.toFun (chartAt (ComplexModel n) p y) ∈ complexCoordinatePlane n kN)) ∧
    ∃ G : (Y → ℂ) → Prop,
      (∀ g, G g → (geoTransformAlong 𝔪 T).ideal.mem p g) ∧
      (∀ f, (geoTransformAlong 𝔪 T).ideal.mem p f → IsInSpanOnAt (n := n) (geoTransformAlong 𝔪 T).N G p f) ∧
      ∀ g, G g → ∀ L : List (Fin n), NormalIdx kS L → (∀ l ∈ L, l.1 < kN) → L.length < 𝔪.d →
        IsInSpanOnAt (n := n) (strictAlong T S) ((geoTransformAlong (derivMarkedAlong 𝔪 L.length) T).ideal.mem p) p
          (c.nd L g)

/-- **The conclusion of the invariant**: at a good point `p ∈ S_T` where every `[𝓓_N^i 𝔪]_T` (`i < μ`) has order
`≥ μ - i` along `S_T`, the ideal `𝔞_T` has order `≥ μ` along `N_T` at `p`. -/
theorem GoodAtAlong.orderGE (𝔪 : MarkedIdeal n X) (S : Set X) {Y : CMfd.{u} n} {T : BlowupTower X Y} {p : Y}
    (hp : GoodAtAlong 𝔪 S T p) (hcoh : (geoTransformAlong 𝔪 T).ideal.IsCoherent)
    (hD : ∀ i < 𝔪.d, OrderGE n (strictAlong T S) (geoTransformAlong (derivMarkedAlong 𝔪 i) T).ideal p (𝔪.d - i)) :
    OrderGE n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal p 𝔪.d := by
  obtain ⟨kS, kN, hk, -, c, hcN, G, hGmem, hGgen, hGder⟩ := hp
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcoh
  have hNev : ∀ᶠ y in 𝓝 p, y ∈ (geoTransformAlong 𝔪 T).N → c.ψ y ∈ complexCoordinatePlane n kN := by
    filter_upwards [c.eventually_mem_flatDomain] with y hy hyN using (hcN hy.1 hy.2).mp hyN
  have hG : ∀ g, G g → VanishesToOrderOn n (geoTransformAlong 𝔪 T).N p 𝔪.d g := by
    intro g hg
    refine NormalDerivativeAlong.FlatChart.vanishesToOrderOn_of_nd c hk hNev (hhol p g (hGmem g hg)) fun L hL hLt hLlen => ?_
    exact CoefficientRestrictionTower.vanishesToOrderOn_of_isInSpanOnAt (hGder g hg L hL hLt hLlen) fun s hs =>
      hD L.length hLlen s hs
  intro f hf
  exact CoefficientRestrictionTower.vanishesToOrderOn_of_isInSpanOnAt (hGgen f hf) hG

/-- **Every point of `S` is good** for the empty tower: in a flat chart of `N` in which `S` is a plane, the derivatives
tangent to `N` of germs of `𝔞` lie in `𝓓_N^{|L|} 𝔞` (`NormalDerivativeAlong.FlatChart.nd_mem_iterDerivIdealAlong`). -/
theorem goodAtAlong_refl (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    {S : Set X} (hS : IsClosedSubmanifold n S) (hSN : S ⊆ 𝔪.N) {p : X} (hp : p ∈ S) :
    GoodAtAlong 𝔪 S (BlowupTower.refl : BlowupTower X X) p := by
  obtain ⟨kN, hkN⟩ := hN.2 p (hSN hp)
  obtain ⟨kS, hkS⟩ := hS.2 p hp
  have hk : kS ≤ kN := le_of_regularAtDim_subset hkS hkN hSN
  obtain ⟨c', hc'S, -⟩ := NormalDerivativeMonomial.FlatChart.exists_nested (FlatChart.ofRegularAtDim hkN) hk hkN.1 hkS hSN
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞
  let c : FlatChart n S p kS := ⟨c'.Φ, c'.src, c'.zero, hc'S⟩
  have hcN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) p).source → chartAt (ComplexModel n) p y ∈ c.Φ.source →
      (y ∈ 𝔪.N ↔ c.Φ.toFun (chartAt (ComplexModel n) p y) ∈ complexCoordinatePlane n kN) :=
    fun hy hyΦ => c'.flat hy hyΦ
  refine ⟨kS, kN, hk, hkN.1, c, hcN, 𝔪.ideal.mem p, fun g hg => hg, fun f hf => ?_,
    fun g hg L _ hLt _ => ?_⟩
  · exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hf (hhol p f hf))
  · have hmem := NormalDerivativeAlong.FlatChart.nd_mem_iterDerivIdealAlong c hcN h𝔞 hg L hLt
    exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hmem
      (CoefficientRestrictionTower.FlatChart.holomorphicAt_nd c (hhol p g hg) L))

end Invariant

/-! ### The step off the centre -/

section OffCentre

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- **The invariant along `N` off the centre**: if `π z ∉ C` and `π z` is good for `T`, then `z` is good for the tower
continued by the blowup `π` along `C` (the chart and the generators pull back; `π` is a local biholomorphism near `z`). -/
theorem goodAtAlong_step_of_notMem (𝔪 : MarkedIdeal n X) {S : Set X} (T : BlowupTower X Y) {C : Set Y} {π : Z → Y}
    (hπ : IsBlowupAlong n C π) (hNc : IsClosed (geoTransformAlong 𝔪 T).N)
    (hcohT : (geoTransformAlong 𝔪 T).ideal.IsCoherent)
    (hDcoh : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarkedAlong 𝔪 i) T).ideal.IsCoherent)
    (hSc : IsClosed (strictAlong T S)) {z : Z} (hzC : π z ∉ C) (hgood : GoodAtAlong 𝔪 S T (π z)) :
    GoodAtAlong 𝔪 S (.step T C π hπ) z := by
  obtain ⟨kS, kN, hk, hkn, c, hcN, G, hGmem, hGgen, hGder⟩ := hgood
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hπd : ∀ w, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
    fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
  set NT := (geoTransformAlong 𝔪 T).N with hNTdef
  have hN' : (geoTransformAlong 𝔪 (.step T C π hπ)).N = geoStrictTransform π C NT := rfl
  have hoff : ∀ᶠ y in 𝓝 z, π y ∉ C := (hπ.1.1.isOpen_compl.preimage hπc).mem_nhds hzC
  have hSev : ∀ᶠ y in 𝓝 z, (y ∈ strictAlong (.step T C π hπ) S ↔ π y ∈ strictAlong T S) := by
    filter_upwards [hoff] with y hy
    rw [strictAlong_step]
    exact mem_geoStrictTransform_iff_of_notMem hπc hSc hy
  have hNev : ∀ᶠ y in 𝓝 z, (y ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).N ↔ π y ∈ NT) := by
    filter_upwards [hoff] with y hy
    rw [hN']
    exact mem_geoStrictTransform_iff_of_notMem hπc hNc hy
  -- the new coordinates `W = ψ ∘ π`
  set W : Z → ComplexModel n := fun y => c.ψ (π y) with hWdef
  have hev : ∀ᶠ y in 𝓝 z, π y ∈ BlowupFlatCoordinates.flatDomain c.Φ ∧
      (y ∈ strictAlong (.step T C π hπ) S ↔ π y ∈ strictAlong T S) ∧
      (y ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).N ↔ π y ∈ NT) :=
    ((hπc.tendsto z).eventually c.eventually_mem_flatDomain).and (hSev.and hNev)
  obtain ⟨O, hOsub, hO, hzO⟩ := mem_nhds_iff.mp hev
  have hW : ∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W y := fun y hy =>
    (c.mdifferentiableAt_ψ (hOsub hy).1).comp y (hπd y)
  have hflat : ∀ y ∈ O, (y ∈ strictAlong (.step T C π hπ) S ↔ W y ∈ complexCoordinatePlane n kS) := fun y hy => by
    rw [(hOsub hy).2.1]; exact c.flat (hOsub hy).1.1 (hOsub hy).1.2
  have hinj : Function.Injective
      (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ)) (chartAt (ComplexModel n) z z)) := by
    set I := 𝓘(ℂ, ComplexModel n) with hI
    have hrange : range I = univ := by simp [hI]
    set e := chartAt (ComplexModel n) z with he
    set e' := chartAt (ComplexModel n) (π z) with he'
    set F : ComplexModel n → ComplexModel n := fun u => e' (π (e.symm u)) with hF
    have hmd : MDifferentiableAt I I π z := hπd z
    have hderiv : mfderiv I I π z = fderiv ℂ F (e z) := by
      rw [hmd.mfderiv, hrange, fderivWithin_univ]
      rfl
    have hFinj : Function.Injective (fderiv ℂ F (e z)) := by
      have hz : z ∉ BlowupSequences.exceptionalLocus n π :=
        fun h => hzC (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)
      simp only [exceptionalLocus, mem_ofPred_eq, not_not] at hz
      rw [hderiv] at hz
      exact hz.1
    have hzs : z ∈ e.source := mem_chart_source _ z
    have hFz : F (e z) = e' (π z) := by simp only [hF, e.left_inv hzs]
    have hloc : (fun ζ => W (e.symm ζ)) =ᶠ[𝓝 (e z)] fun ζ => c.Φ.toFun (F ζ) := by
      filter_upwards with ζ
      rfl
    have hFd : DifferentiableAt ℂ F (e z) := by
      have h := (contMDiffOn_iff.mp (hπ.contMDiff.contMDiffOn (s := univ))).2 z (π z)
      have hset : (e.target ∩ e.symm ⁻¹' (univ ∩ π ⁻¹' e'.source)) ∈ 𝓝 (e z) := by
        refine (e.continuousOn_symm.isOpen_inter_preimage e.open_target
          (isOpen_univ.inter (hπc.isOpen_preimage _ e'.open_source))).mem_nhds ?_
        exact ⟨e.map_source hzs, by rw [mem_preimage, e.left_inv hzs]; exact ⟨mem_univ _, mem_chart_source _ _⟩⟩
      refine ((h.differentiableOn (by simp)).mono ?_).differentiableAt hset
      intro u hu
      exact ⟨⟨mem_univ _, hu.1⟩, mem_univ _, hu.2.2, mem_univ _⟩
    have hΦd : DifferentiableAt ℂ c.Φ.toFun (F (e z)) := by
      rw [hFz]
      exact c.Φ.toFun_holomorphic.differentiableAt (c.Φ.isOpen_source.mem_nhds c.Φ.center_mem_source)
    have hcomp : HasFDerivAt (fun ζ => c.Φ.toFun (F ζ))
        ((fderiv ℂ c.Φ.toFun (F (e z))).comp (fderiv ℂ F (e z))) (e z) :=
      hΦd.hasFDerivAt.comp (e z) hFd.hasFDerivAt
    rw [hloc.fderiv_eq, hcomp.fderiv]
    refine (c.injective_fderiv_Φ ?_).comp hFinj
    rw [hFz]; exact c.Φ.center_mem_source
  obtain ⟨c', hc', hdom⟩ := FlatChart.exists_of_map' hO hzO hW c.ψ_self hinj hflat
  have hc'N : ∀ {y : Z}, y ∈ (chartAt (ComplexModel n) z).source → chartAt (ComplexModel n) z y ∈ c'.Φ.source →
      (y ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).N ↔
        c'.Φ.toFun (chartAt (ComplexModel n) z y) ∈ complexCoordinatePlane n kN) := by
    intro y hy hyΦ
    obtain ⟨hyO, hΦy⟩ := hdom hy hyΦ
    rw [hΦy, (hOsub hyO).2.2]
    exact hcN (hOsub hyO).1.1 (hOsub hyO).1.2
  -- `π ∘ c'.inv = c.inv` near `0`
  have hWinv : ∀ᶠ u in 𝓝 (0 : ComplexModel n), W (c'.inv u) = u := by
    filter_upwards [c'.eventually_ψ_inv, c'.tendsto_inv.eventually hc'] with u hu hu'
    rw [← hu']; exact hu
  have hπinv : ∀ᶠ u in 𝓝 (0 : ComplexModel n), π (c'.inv u) = c.inv u := by
    have ht : Tendsto (fun u => π (c'.inv u)) (𝓝 (0 : ComplexModel n)) (𝓝 (π z)) :=
      (hπc.tendsto z).comp c'.tendsto_inv
    filter_upwards [hWinv, ht.eventually c.eventually_inv_ψ] with u hu hu'
    rw [← hu', show c.ψ (π (c'.inv u)) = u from hu]
  have hnd : ∀ (g : Y → ℂ) (L : List (Fin n)), c'.nd L (g ∘ π) =ᶠ[𝓝 z] fun z' => c.nd L g (π z') := by
    intro g L
    have hgerm : (fun u => (g ∘ π) (c'.inv u)) =ᶠ[𝓝 (0 : ComplexModel n)] fun u => g (c.inv u) := by
      filter_upwards [hπinv] with u hu
      simp only [Function.comp_apply, hu]
    have hiter := iterDeriv_congr_of_eventuallyEq hgerm (L.map bv)
    filter_upwards [c'.tendsto_ψ.eventually hiter, hc'] with z' h1 h2
    simp only [FlatChart.nd]
    rw [h1, h2]
  have hpb : ∀ {𝔟 : GermIdeal n Y} {g : Y → ℂ}, 𝔟.mem (π z) g → HolomorphicAt n g (π z) →
      (GermIdeal.pullback (m := n) π 𝔟).mem z (g ∘ π) := fun {𝔟} {g} hg hghol =>
    InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ a, 𝔟.mem (π z) a ∧ s = a ∘ π) ⟨g, hg, rfl⟩
      (HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd) hghol)
  have hN'sub : (geoTransformAlong 𝔪 (.step T C π hπ)).N ⊆ π ⁻¹' NT := by
    rw [hN']; exact geoStrictTransform_subset_preimage hπc hNc
  refine ⟨kS, kN, hk, hkn, c', hc'N, fun h => ∃ g, G g ∧ h = g ∘ π, ?_, ?_, ?_⟩
  · rintro h ⟨g, hg, rfl⟩
    have hgm := hGmem g hg
    exact mem_geoTransform_of_mem_pullback _ (hpb hgm (hol_of_isCoherent hcohT _ _ hgm))
  · intro f hf
    have h1 := isInSpanOnAt_pullback_of_mem_geoTransform_of_notMem hπ (geoTransformAlong 𝔪 T) hzC hf
    refine IsInSpanOnAt.trans (fun t ht => ?_) h1
    refine IsInSpanOnAt.trans (fun s hs => ?_) (IsInSpanAt.restrict (GermIdeal.mem_pullback_iff.mp ht))
    obtain ⟨a, ha, rfl⟩ := hs
    exact IsInSpanOnAt.mono (fun t ⟨g, hg, ht⟩ => ⟨g, hg, ht⟩) (isInSpanOnAt_comp hπc hπd hN'sub (hGgen a ha))
  · rintro h ⟨g, hg, rfl⟩ L hL hLt hLlen
    obtain ⟨K, s, a, hs, ha, hsum⟩ := hGder g hg L hL hLt hLlen
    have hdL : L.length ≤ 𝔪.d := hLlen.le
    refine ⟨K, fun i => s i ∘ π, fun i => a i ∘ π, fun i => ?_, fun i =>
      HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd) (ha i), ?_⟩
    · exact mem_geoTransform_of_mem_pullback _ (hpb (hs i) (hol_of_isCoherent (hDcoh _ hdL) _ _ (hs i)))
    · filter_upwards [hnd g L, hSev, (hπc.tendsto z).eventually hsum] with z' h1 h2 h3 hz'
      rw [h1]
      exact h3 (h2.mp hz')

end OffCentre

/-! ### The step over the centre -/

section CentreStep

open BlowupFlatCoordinates BlowupMonomialCharts

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- **The invariant along `N` over the centre**: if `π z ∈ C`, `z ∈ S_{T'}` and `π z` is good for `T`, then `z` is good for
the tower continued by the blowup `π` along `C`.  The new coordinates are a monomial chart over nested product-form
coordinates for `C ⊆ S_T ⊆ N_T`, describing `S'` and `N'` at once; the new generators are the `h'` with `g ∘ π = W_j^μ h'`
on `N'` (`exists_mem_geoTransform_eq_pow_mul`), and `W_j^μ ∂^L h' = W_j^{|L|} (∂^L g) ∘ π` on `N'`
(`NormalDerivativeAlong.nd_monomial_identity_along`); `W_j^μ` is cancelled on `N'` and on `S'`. -/
theorem goodAtAlong_step_of_mem (𝔪 : MarkedIdeal n X) {S : Set X} (T : BlowupTower X Y) {C : Set Y} {π : Z → Y}
    (hπ : IsBlowupAlong n C π) (hNT : IsClosedSubmanifold n (geoTransformAlong 𝔪 T).N)
    (hcohT : (geoTransformAlong 𝔪 T).ideal.IsCoherent)
    (hDN : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarkedAlong 𝔪 i) T).N = (geoTransformAlong 𝔪 T).N)
    (hDcoh : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarkedAlong 𝔪 i) T).ideal.IsCoherent)
    (hCadm : (geoTransformAlong 𝔪 T).IsAdmissibleCentre C)
    (hDadm : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarkedAlong 𝔪 i) T).IsAdmissibleCentre C)
    (hSc : IsClosed (strictAlong T S)) (hSN : strictAlong T S ⊆ (geoTransformAlong 𝔪 T).N)
    (hCS : C ⊆ strictAlong T S) {z : Z}
    (hz : z ∈ strictAlong (.step T C π hπ) S) (hzC : π z ∈ C) (hgood : GoodAtAlong 𝔪 S T (π z)) :
    GoodAtAlong 𝔪 S (.step T C π hπ) z := by
  obtain ⟨kS, kN, hk, hkn, c, hcN, G, hGmem, hGgen, hGder⟩ := hgood
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hπd : ∀ w, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
    fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcohT
  set NT := (geoTransformAlong 𝔪 T).N with hNTdef
  have hN' : (geoTransformAlong 𝔪 (.step T C π hπ)).N = geoStrictTransform π C NT := rfl
  -- nested product-form coordinates for `C ⊆ S_T ⊆ N_T` at `π z`
  obtain ⟨kC, hkC⟩ := hπ.1.2 (π z) hzC
  have hSreg : RegularAtDim (n := n) (strictAlong T S) (π z) kS :=
    ⟨le_trans hk hkn, hCS hzC, c.Φ, c.src, c.zero, c.flat⟩
  have hkCk : kC ≤ kS := le_of_regularAtDim_subset hkC hSreg hCS
  obtain ⟨c'', hc''C, hc''N, hc''nd⟩ :=
    NormalDerivativeAlong.FlatChart.exists_nested_pair c hkCk (le_trans hk hkn) hk hkC hCS hcN
  -- one monomial chart for both strict transforms
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWmem, hWeq, hℓ, hiffS, hiffN⟩ :=
    exists_local_geoStrictTransform_pair hπ c''.src hc''C c''.flat hc''N (mem_flatDomain_self c''.Φ)
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := BlowupLocalSurjectivity.existsUnique_monomialLift hπ c''.src hc''C hj
  have hWeq' : ∀ z' ∈ O, c''.ψ (π z') = monomial kC j (W z') := fun z' hz' => (hWeq z' hz').2.symm
  obtain ⟨hjk, hWz⟩ := (hiffS z hzO).mp hz
  have hjN : j.1 < kN := lt_of_lt_of_le hjk hk
  have hWzN : W z ∈ complexCoordinatePlane n kN := plane_mono hk hWz
  have hCu : ∀ u ∈ O, (π u ∈ C ↔ W u j = 0) := fun u hu => by
    rw [hc''C (hWeq u hu).1.1 (hWeq u hu).1.2, ← (hWeq u hu).2, monomial_mem_plane_iff hj]
  -- the new flat chart `W - W z`
  have hW' : ∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (fun y => W y - W z) y :=
    fun y hy => ((hWs y hy).mdifferentiableAt (by simp)).sub mdifferentiableAt_const
  have hflat' : ∀ y ∈ O, (y ∈ strictAlong (.step T C π hπ) S ↔ W y - W z ∈ complexCoordinatePlane n kS) := by
    intro y hy
    rw [sub_mem_plane_iff hWz]
    exact (hiffS y hy).trans ⟨fun h => h.2, fun h => ⟨hjk, h⟩⟩
  have hflatN' : ∀ y ∈ O, (y ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).N ↔
      W y - W z ∈ complexCoordinatePlane n kN) := by
    intro y hy
    rw [sub_mem_plane_iff hWzN, hN']
    exact (hiffN y hy).trans ⟨fun h => h.2, fun h => ⟨hjN, h⟩⟩
  have hinj : Function.Injective
      (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ) - W z) (chartAt (ComplexModel n) z z)) := by
    set e := chartAt (ComplexModel n) z with he
    have hFd : DifferentiableAt ℂ (fun ζ => W (e.symm ζ)) (e z) := by
      have h1 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) (chart_mem_atlas (ComplexModel n) z)
        (e.map_source (mem_chart_source _ z))
      have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W (e.symm (e z)) := by
        rw [e.left_inv (mem_chart_source _ z)]; exact (hWs z hzO).mdifferentiableAt (by simp)
      exact mdifferentiableAt_iff_differentiableAt.mp (h2.comp _ h1)
    rw [fderiv_sub_const]
    refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
    by_contra hv0
    apply BlowupFibreDirection.fderiv_monomialInverse_ne_zero hO hWs hWmem hℓs (hℓ ℓ hℓs hℓπ) hzO hv0
    rw [hFd.fderiv_restrictScalars ℝ]
    exact hv
  obtain ⟨c', hc', hdom⟩ := FlatChart.exists_of_map' hO hzO hW' (sub_self _) hinj hflat'
  have hc'N : ∀ {y : Z}, y ∈ (chartAt (ComplexModel n) z).source → chartAt (ComplexModel n) z y ∈ c'.Φ.source →
      (y ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).N ↔
        c'.Φ.toFun (chartAt (ComplexModel n) z y) ∈ complexCoordinatePlane n kN) := by
    intro y hy hyΦ
    obtain ⟨hyO, hΦy⟩ := hdom hy hyΦ
    rw [hΦy]; exact hflatN' y hyO
  have hN'ev : ∀ᶠ y in 𝓝 z, (y ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).N ↔
      c'.ψ y ∈ complexCoordinatePlane n kN) := by
    filter_upwards [c'.eventually_mem_flatDomain] with y hy using hc'N hy.1 hy.2
  -- the local equation `W_j` of the exceptional divisor
  have hl : IsLocalEquation hπ O (fun p => W p j) :=
    GlueingTrivialAction.isLocalEquation_monomial hπ c''.src hc''C hj hO hWs hWeq
  -- `W_j` vanishes on no relatively open subset of a strict transform
  have hnon : ∀ (A : Set Y) (μ : ℕ), ∀ V : Set Z, IsOpen V → V ⊆ O → (V ∩ geoStrictTransform π C A).Nonempty →
      ∃ y ∈ V ∩ geoStrictTransform π C A, W y j ^ μ ≠ 0 := by
    rintro A μ V hV hVO ⟨y₀, hy₀V, hy₀S⟩
    obtain ⟨y₁, hy₁V, hy₁S, hy₁C⟩ := mem_closure_iff.mp hy₀S V hV hy₀V
    exact ⟨y₁, ⟨hy₁V, subset_closure ⟨hy₁S, hy₁C⟩⟩,
      pow_ne_zero _ fun h => hy₁C ((hCu y₁ (hVO hy₁V)).mpr h)⟩
  have hd : (geoTransformAlong 𝔪 T).d = 𝔪.d := d_geoTransformAlong 𝔪 T
  have hzN : z ∈ geoStrictTransform π C NT := geoStrictTransform_mono' π C hSN hz
  refine ⟨kS, kN, hk, hkn, c', hc'N, fun h' => ∃ g, G g ∧ HolomorphicAt n h' z ∧
    (geoTransformAlong 𝔪 (.step T C π hπ)).ideal.mem z h' ∧
    ∀ᶠ y in 𝓝 z, y ∈ geoStrictTransform π C NT → g (π y) = W y j ^ 𝔪.d * h' y,
    fun h' ⟨_, _, _, hm, _⟩ => hm, ?_, ?_⟩
  · -- the new generators generate the transform along `N'`
    intro f hf
    have hfhol : HolomorphicAt n f z := by
      have h := hf
      rw [geoTransformAlong_step, geoTransform_ideal] at h
      exact h.1
    have h1 := isInSpanOnAt_pow_mul_of_mem_geoTransform hπ (geoTransformAlong 𝔪 T) hl hzO hf
    rw [hd] at h1
    have hspan : IsInSpanOnAt (n := n) (geoStrictTransform π C NT)
        (fun t => ∃ h', (∃ g, G g ∧ HolomorphicAt n h' z ∧
          (geoTransformAlong 𝔪 (.step T C π hπ)).ideal.mem z h' ∧
          ∀ᶠ y in 𝓝 z, y ∈ geoStrictTransform π C NT → g (π y) = W y j ^ 𝔪.d * h' y) ∧
          t = fun y => W y j ^ 𝔪.d * h' y) z (fun y => W y j ^ 𝔪.d * f y) := by
      refine IsInSpanOnAt.trans (fun t ht => ?_) h1
      refine IsInSpanOnAt.trans (fun s hs => ?_) (IsInSpanAt.restrict (GermIdeal.mem_pullback_iff.mp ht))
      obtain ⟨a, ha, rfl⟩ := hs
      refine IsInSpanOnAt.trans (fun t' ht' => ?_)
        (isInSpanOnAt_comp hπc hπd (geoStrictTransform_subset_preimage hπc hNT.1) (hGgen a ha))
      obtain ⟨g, hg, rfl⟩ := ht'
      obtain ⟨h', hh'hol, hh'mem, hrel⟩ :=
        exists_mem_geoTransform_eq_pow_mul hπ (geoTransformAlong 𝔪 T) hNT hcohT hCadm hl hzO hzN (hGmem g hg)
      rw [hd] at hrel
      refine ⟨1, fun _ => fun y => W y j ^ 𝔪.d * h' y, fun _ _ => 1,
        fun _ => ⟨h', ⟨g, hg, hh'hol, hh'mem, hrel⟩, rfl⟩, fun _ => holomorphicAt_const 1, ?_⟩
      filter_upwards [hrel] with y hy hyN
      simp [hy hyN]
    obtain ⟨K, t, b, ht, hb, hsum⟩ := hspan
    choose h' hh' htdef using ht
    refine ⟨K, h', b, fun i => hh' i, hb, ?_⟩
    exact RestrictedIdealQuotient.eventuallyEq_within_of_mul_eventuallyEq_within hO (hnon NT 𝔪.d) hzO
      (F := f) (G := fun y => ∑ i, b i y * h' i y) hfhol
      (HolomorphicAt.sum _ fun i _ => (hb i).mul (hh' i).choose_spec.2.1) (by
        filter_upwards [hsum] with y hy hyN
        rw [hy hyN, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [htdef i]; ring)
  · -- the derivatives
    rintro h' ⟨g, hg, hh', -, hrel⟩ L hL hLt hLlen
    have hgp : HolomorphicAt n g (π z) := hhol _ _ (hGmem g hg)
    have hLj : ∀ l ∈ L, l ≠ j ∧ kC ≤ l.1 ∧ l.1 < kN := fun l hl' => by
      have h1 := hL l hl'
      have h2 := hLt l hl'
      exact ⟨fun h => by rw [h] at h1; omega, by omega, h2⟩
    have hrel' : ∀ᶠ y in 𝓝 z, y ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).N →
        g (π y) = W y j ^ 𝔪.d * h' y := hrel
    have hid := nd_monomial_identity_along hπc c'' c' hO hzO hWeq' hc' hN'ev hgp hh' hrel' L hLj
    have hnd := (hπc.tendsto z).eventually (hc''nd L hL g hgp)
    obtain ⟨K, s, aa, hs, haa, hsum⟩ := hGder g hg L hL hLt hLlen
    have hdL : L.length ≤ 𝔪.d := hLlen.le
    have h𝔫N : (geoTransformAlong (derivMarkedAlong 𝔪 L.length) T).N = NT := hDN _ hdL
    have h𝔫d : (geoTransformAlong (derivMarkedAlong 𝔪 L.length) T).d = 𝔪.d - L.length := by
      rw [d_geoTransformAlong, derivMarkedAlong_d]
    have hzN𝔫 : z ∈ geoStrictTransform π C (geoTransformAlong (derivMarkedAlong 𝔪 L.length) T).N := by
      rw [h𝔫N]; exact hzN
    have hex : ∀ i, ∃ s' : Z → ℂ, HolomorphicAt n s' z ∧
        ((geoTransformAlong (derivMarkedAlong 𝔪 L.length) T).geoTransform C π).ideal.mem z s' ∧
        ∀ᶠ y in 𝓝 z, y ∈ geoStrictTransform π C (geoTransformAlong (derivMarkedAlong 𝔪 L.length) T).N →
          s i (π y) = W y j ^ (geoTransformAlong (derivMarkedAlong 𝔪 L.length) T).d * s' y := fun i =>
      exists_mem_geoTransform_eq_pow_mul hπ _ (h𝔫N ▸ hNT) (hDcoh _ hdL) (hDadm _ hdL) hl hzO hzN𝔫 (hs i)
    choose s' hs'hol hs'mem hs'eq using hex
    have hsub : ∀ᶠ z' in 𝓝 z, z' ∈ strictAlong (.step T C π hπ) S → π z' ∈ strictAlong T S :=
      Eventually.of_forall fun z' hz' => geoStrictTransform_subset_preimage hπc hSc hz'
    have hmul : ∀ᶠ z' in 𝓝 z, z' ∈ geoStrictTransform π C (strictAlong T S) →
        W z' j ^ 𝔪.d * c'.nd L h' z' = W z' j ^ 𝔪.d * ∑ i, (aa i ∘ π) z' * s' i z' := by
      filter_upwards [hid, hnd, (hπc.tendsto z).eventually hsum, eventually_all.mpr hs'eq, hsub] with
        z' h1 h2 h3 h4 h5 hz'
      have hz'N : z' ∈ geoStrictTransform π C NT := geoStrictTransform_mono' π C hSN hz'
      rw [h1 (by rw [hN']; exact hz'N), h2, h3 (h5 hz'), Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h4i : s i (π z') = W z' j ^ (𝔪.d - L.length) * s' i z' := by
        rw [← h𝔫d]; exact h4 i (by rw [h𝔫N]; exact hz'N)
      have e : W z' j ^ 𝔪.d = W z' j ^ L.length * W z' j ^ (𝔪.d - L.length) := by
        rw [← pow_add, Nat.add_sub_cancel' hdL]
      rw [h4i, Function.comp_apply, e]
      ring
    have hcan := RestrictedIdealQuotient.eventuallyEq_within_of_mul_eventuallyEq_within hO
      (hnon (strictAlong T S) 𝔪.d) hzO
      (CoefficientRestrictionTower.FlatChart.holomorphicAt_nd c' hh' L)
      (HolomorphicAt.sum _ fun i _ =>
        (HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd) (haa i)).mul (hs'hol i)) hmul
    exact ⟨K, s', fun i => aa i ∘ π, hs'mem,
      fun i => HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd) (haa i), hcan⟩

end CentreStep

/-! ### Along multiple test blow-ups -/

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Every point of the strict transform of `S` is good** along a multiple test blow-up of `𝔪` with centres in the strict
transforms of `S ⊆ N` (induction on the tower: `goodAtAlong_refl`, `goodAtAlong_step_of_mem`,
`goodAtAlong_step_of_notMem`). -/
theorem goodAtAlong_tower (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    {S : Set X} (hS : IsClosedSubmanifold n S) (hSN : S ⊆ 𝔪.N) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T → CentresIn S T →
      ∀ p ∈ strictAlong T S, GoodAtAlong 𝔪 S T p
  | _, .refl => fun _ _ p hp => goodAtAlong_refl 𝔪 hN h𝔞 hS hSN hp
  | _, .step T C π hπ => fun hT hTS z hz => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      obtain ⟨hTS0, hCS⟩ := hTS
      obtain ⟨-, hNT, hcohT, hST, hSNT, -, -⟩ := restrict_tower_along 𝔪 hN h𝔞 hS hSN T hT0 hTS0
      have hSc : IsClosed (strictAlong T S) := hST.1
      have hpz : π z ∈ strictAlong T S :=
        geoStrictTransform_subset_preimage hπ.contMDiff.continuous hSc hz
      have hgood := goodAtAlong_tower 𝔪 hN h𝔞 hS hSN T hT0 hTS0 (π z) hpz
      have hDN : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarkedAlong 𝔪 i) T).N = (geoTransformAlong 𝔪 T).N :=
        fun i hi => (inclusions_tower_along 𝔪 hN h𝔞 hi T hT0).2.1
      have hDcoh : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarkedAlong 𝔪 i) T).ideal.IsCoherent :=
        fun i hi => (inclusions_tower_along 𝔪 hN h𝔞 hi T hT0).2.2.2.2.2.1
      have hDadm : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarkedAlong 𝔪 i) T).IsAdmissibleCentre C :=
        fun i hi => ((isGeoTestTower_step_iff _ T C π hπ).mp
          (inclusions_tower_along 𝔪 hN h𝔞 hi (.step T C π hπ) hT).1).2
      by_cases hzC : π z ∈ C
      · exact goodAtAlong_step_of_mem 𝔪 T hπ hNT hcohT hDN hDcoh hC hDadm hSc hSNT hCS hz hzC hgood
      · exact goodAtAlong_step_of_notMem 𝔪 T hπ hNT.1 hcohT hDcoh hSc hzC hgood

/-- **Włodarczyk `le:S` (2) along `N`, the reverse inclusion** (GGT Proposition 5.6.4 (2)): along a multiple test blow-up
`T` of `𝔪 = (X, N, E, 𝔞, μ)` (`N` a closed submanifold, `𝔞` coherent, `μ ≥ 1`) with centres in the strict transforms of a
closed submanifold `S ⊆ N`, `supp[𝓒_N(𝔪)|_S]_T ⊆ supp(𝔪_T)`. -/
theorem cosupp_coeffAlong_withN_tower_subset (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) {S : Set X} (hS : IsClosedSubmanifold n S) (hSN : S ⊆ 𝔪.N)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (hTS : CentresIn S T) :
    (geoTransformAlong (withN (coeffMarkedAlong 𝔪) S) T).cosupp ⊆ (geoTransformAlong 𝔪 T).cosupp := by
  intro x hx
  obtain ⟨-, hRE, -⟩ := coeffAlong_restrict_tower 𝔪 hN h𝔞 hd hS hSN T hT hTS
  obtain ⟨-, hNT, hcohT, hST, hSNT, -, -⟩ := restrict_tower_along 𝔪 hN h𝔞 hS hSN T hT hTS
  have hfam := isSubmanifoldFamily_derivMarkedAlong hN h𝔞
  have hall : ∀ i < 𝔪.d, IsGeoTestTower (derivMarkedAlong 𝔪 i) T :=
    fun i hi => (inclusions_tower_along 𝔪 hN h𝔞 (le_of_lt hi) T hT).1
  obtain ⟨-, hmsum⟩ := geoTransformAlong_msum_along (fun i => derivMarkedAlong 𝔪 i) hd hfam T
  obtain ⟨he, -, hfamT⟩ := hmsum hall
  -- `x` is in the cosupport of `𝓒_N(𝔪)_T` along `S_T`
  have hx1 : x ∈ cosupport n (strictAlong T S) (geoTransformAlong (coeffMarkedAlong 𝔪) T).ideal
      (coeffMarkedAlong 𝔪).d := by
    rw [hRE.cosupp_eq] at hx
    have := hx
    rwa [cosupp_withN, d_geoTransformAlong] at this
  have hxS : x ∈ strictAlong T S := hx1.1
  -- hence in that of the sum of the transforms `[𝓓_N^i 𝔪]_T` along `S_T ⊆ N_T`
  have hNc : (geoTransformAlong (coeffMarkedAlong 𝔪) T).N = (geoTransformAlong 𝔪 T).N := by
    rw [HomogenizedGlueingTower.N_geoTransformAlong, HomogenizedGlueingTower.N_geoTransformAlong]
    rfl
  have hle : RestrictedIdealWeight.RestrictLe (strictAlong T S) (msum (fun i => geoTransformAlong (derivMarkedAlong 𝔪 i) T) 𝔪.d).ideal
      (geoTransformAlong (coeffMarkedAlong 𝔪) T).ideal :=
    restrictLe_mono (hSNT.trans hNc.symm.subset) he.ge
  have hx2 := cosupport_subset_of_restrictLe hle _ hx1
  -- hence every `[𝓓_N^i 𝔪]_T` has order `≥ μ - i` along `S_T` at `x`
  have hD : ∀ i < 𝔪.d, OrderGE n (strictAlong T S) (geoTransformAlong (derivMarkedAlong 𝔪 i) T).ideal x
      (𝔪.d - i) := by
    intro i hi
    have hJ : ∀ i < 𝔪.d, ∀ y g, (idealPow (geoTransformAlong (derivMarkedAlong 𝔪 i) T).ideal
        (sumExp (fun j => (geoTransformAlong (derivMarkedAlong 𝔪 j) T).d) 𝔪.d i)).mem y g → HolomorphicAt n g y :=
      fun _ _ _ _ hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg
    have hmark : (coeffMarkedAlong 𝔪).d =
        (Finset.range 𝔪.d).prod fun j => (geoTransformAlong (derivMarkedAlong 𝔪 j) T).d := by
      simp only [d_geoTransformAlong]; rfl
    rw [hmark] at hx2
    have hx3 := ((mem_cosupport_finSumIdeal hJ).mp hx2).2 i hi
    have hD1 : ∀ j < 𝔪.d, 1 ≤ (geoTransformAlong (derivMarkedAlong 𝔪 j) T).d := fun j hj => by
      rw [d_geoTransformAlong, derivMarkedAlong_d]; omega
    have hpow := MarkedIdealOperationsAlong.cosupport_idealPow_mul_eq_along hST.2
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent (hfamT.coh i hi)) (one_le_sumExp hD1 i)
      (geoTransformAlong (derivMarkedAlong 𝔪 i) T).d
    rw [mul_sumExp (fun j => (geoTransformAlong (derivMarkedAlong 𝔪 j) T).d) hi] at hpow
    rw [hpow, d_geoTransformAlong, derivMarkedAlong_d] at hx3
    exact hx3.2
  -- the invariant gives the order of `𝔪_T` along `N_T`
  have hgood := goodAtAlong_tower 𝔪 hN h𝔞 hS hSN T hT hTS x hxS
  have hord := hgood.orderGE 𝔪 S hcohT hD
  show x ∈ cosupport n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).d
  rw [d_geoTransformAlong]
  exact ⟨hSNT hxS, hord⟩

/-- **`supp[𝓒_N(𝔪)|_S]_T = supp(𝔪_T) ∩ S_T`** along a multiple test blow-up of `𝔪` with centres in the strict transforms of
`S ⊆ N`. -/
theorem cosupp_coeffAlong_withN_tower (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) {S : Set X} (hS : IsClosedSubmanifold n S) (hSN : S ⊆ 𝔪.N)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (hTS : CentresIn S T) :
    (geoTransformAlong (withN (coeffMarkedAlong 𝔪) S) T).cosupp = (geoTransformAlong 𝔪 T).cosupp ∩ strictAlong T S := by
  refine Subset.antisymm (fun x hx => ⟨cosupp_coeffAlong_withN_tower_subset 𝔪 hN h𝔞 hd hS hSN T hT hTS hx, ?_⟩)
    (coeffAlong_restrict_tower 𝔪 hN h𝔞 hd hS hSN T hT hTS).2.2
  have h := (geoTransformAlong (withN (coeffMarkedAlong 𝔪) S) T).cosupp_subset_N hx
  rwa [N_geoTransformAlong_withN] at h

/-- **Włodarczyk `le:S` in full along `N`** (GGT Proposition 5.6.4): for `𝔪 = (X, N, E, 𝔞, μ)` with `N` a closed
submanifold, `𝔞` coherent and `μ ≥ 1`, and a closed submanifold `S ⊆ N`, a tower is a multiple test blow-up of the
restricted coefficient ideal along `N`, `𝓒_N(𝔪)|_S`, if and only if it is a multiple test blow-up of `𝔪` with centres in
the strict transforms of `S`, and along it `supp[𝓒_N(𝔪)|_S]_T = supp(𝔪_T) ∩ S_T`. -/
theorem coeffAlong_restrict_tower_iff (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) {S : Set X} (hS : IsClosedSubmanifold n S) (hSN : S ⊆ 𝔪.N) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      (IsGeoTestTower (withN (coeffMarkedAlong 𝔪) S) T ↔ IsGeoTestTower 𝔪 T ∧ CentresIn S T) ∧
      (IsGeoTestTower (withN (coeffMarkedAlong 𝔪) S) T →
        (geoTransformAlong (withN (coeffMarkedAlong 𝔪) S) T).cosupp =
          (geoTransformAlong 𝔪 T).cosupp ∩ strictAlong T S)
  | _, .refl => ⟨⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩, fun _ =>
      CoefficientIdealAlongRestriction.cosupp_coeffMarkedAlong_withN hN.2
        (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞) hd hSN⟩
  | _, .step T C π hπ => by
      obtain ⟨ih, -⟩ := coeffAlong_restrict_tower_iff 𝔪 hN h𝔞 hd hS hSN T
      have hE : (geoTransformAlong (withN (coeffMarkedAlong 𝔪) S) T).E = (geoTransformAlong 𝔪 T).E :=
        MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := withN (coeffMarkedAlong 𝔪) S) (𝔫 := 𝔪) rfl T
      have hiff : IsGeoTestTower (withN (coeffMarkedAlong 𝔪) S) (.step T C π hπ) ↔
          IsGeoTestTower 𝔪 (.step T C π hπ) ∧ CentresIn S (.step T C π hπ) := by
        rw [isGeoTestTower_step_iff, isGeoTestTower_step_iff, centresIn_step_iff]
        constructor
        · rintro ⟨h0, hC⟩
          obtain ⟨hT0, hTS0⟩ := ih.mp h0
          have hcos := cosupp_coeffAlong_withN_tower 𝔪 hN h𝔞 hd hS hSN T hT0 hTS0
          refine ⟨⟨hT0, hC.1, fun x hx => (hcos ▸ hC.2.1 hx).1, hE ▸ hC.2.2⟩, hTS0,
            fun x hx => (hcos ▸ hC.2.1 hx).2⟩
        · rintro ⟨⟨hT0, hC⟩, hTS0, hCS⟩
          have hcos := cosupp_coeffAlong_withN_tower 𝔪 hN h𝔞 hd hS hSN T hT0 hTS0
          refine ⟨ih.mpr ⟨hT0, hTS0⟩, hC.1, fun x hx => ?_, hE.symm ▸ hC.2.2⟩
          rw [hcos]; exact ⟨hC.2.1 hx, hCS hx⟩
      refine ⟨hiff, fun h => ?_⟩
      obtain ⟨hT', hTS'⟩ := hiff.mp h
      exact cosupp_coeffAlong_withN_tower 𝔪 hN h𝔞 hd hS hSN _ hT' hTS'

end Tower

end

end Hironaka.CoefficientIdealAlongRestrictionFull
