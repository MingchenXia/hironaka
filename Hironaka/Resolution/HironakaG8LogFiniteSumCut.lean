import Hironaka.Resolution.HironakaG8LogControlledMarked
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.GiraudAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Cosupports of the logarithmic derivative family and of its common-mark sum (G8 lane, run 0080; leaf G8-3H-C09)

Blueprint: `hironaka-g8-resume-log-finite-sum-cut.tex`.

For a marked ideal `𝔪 = (X, N, E, 𝔞, d)` let `𝔪_j = rawLogMarked 𝔪 j = (X, N, E, 𝓓_{N,E}^j 𝔞, d - j)` and, for
`k < d`, `𝓒^k(𝔪) = bmFiniteSum 𝔪_• (k + 1) = (∑_{j ≤ k} (𝓓_{N,E}^j 𝔞)^{L/(d-j)}, L)`, `L = lcm_{j ≤ k}(d - j)`
(`HironakaActualIteratedLogMarkedFamily`, BM08 §3.4).  This module proves (BM08 Lemmas 3.2(3), 3.8(1), 3.9):

* `orderGE_logDerivIdealAlong_of_orderGE_succ`: a logarithmic derivative lowers the order along `N` by at most one;
  hence `cosupp 𝔪 ⊆ cosupp 𝔪_j` for `j ≤ d` (`cosupp_subset_cosupp_rawLogMarked`);
* `cosupport_finSumIdeal`: the cosupport of a finite sum with one mark is the intersection of the cosupports;
* `cosupp_bmFiniteSum`: for a family on one carrier with positive marks (the mark `0` excluded) the cosupport of
  the common-mark sum is the intersection of the cosupports (powers along a submanifold:
  `MarkedIdealOperationsAlong.cosupport_idealPow_mul_eq_along`);
* `cosupp_bmFiniteSum_rawLogMarked`: `cosupp 𝓒^k(𝔪) = cosupp 𝔪` for `k < d` (BM08 Lemma 3.9);
* the empty sum: mark `1` and cosupport the whole carrier (`bmFiniteSum_zero_d`, `cosupp_bmFiniteSum_zero`).

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LogFiniteSumCut

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.DerivativeIdeal Hironaka.DerivativeIdealAlong
  Hironaka.OrderTaylor Hironaka.IdealOrderArithmetic
  Hironaka.HomogenizedGlueing
  Hironaka.RelativePrincipalizationSpan
  Hironaka.HironakaActualIntrinsicLogDerivativeFrame
  Hironaka.HironakaActualIteratedLogMarkedFamily
  Hironaka.HironakaG8LogDerivEtale
  Hironaka.HironakaG8LogControlledInclusion

noncomputable section

/-! ### Logarithmic derivatives and the order along the carrier -/

section Order

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {E : List (Set M)} {𝔞 : GermIdeal n M}

/-- **A logarithmic derivative lowers the order along `N` by at most one**: if `ord_x(𝔞|_N) ≥ μ + 1`, then
`ord_x((𝓓_{N,E} 𝔞)|_N) ≥ μ` (any sets `N`, `E`; BM08 Lemma 3.2(3)). -/
theorem orderGE_logDerivIdealAlong_of_orderGE_succ (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    {x : M} {μ : ℕ} (hx : OrderGE n N 𝔞 x (μ + 1)) : OrderGE n N (logDerivIdealAlong N E 𝔞) x μ := by
  intro g hg
  refine IsInSpanAt.vanishesToOrderOn (mem_logDerivIdealAlong_iff.mp hg) ?_
  rintro s (hs | hs | ⟨e, ξ, f, hξ, hf, rfl⟩)
  · exact (hx s hs).mono (Nat.le_succ μ)
  · exact GiraudAlong.vanishesToOrderOn_of_mem_vanishingIdeal hs μ
  · obtain ⟨h, hh, hfh⟩ := hx f hf
    have hfhol := h𝔞 x f hf
    have hhhol : HolomorphicAt n h x := GermIdealOrder.holomorphicAt_of_mem_idealPow hh
    have hd : (vanishingIdeal (n := n) N).mem x (fun p => f p - h p) :=
      ⟨GiraudAlong.holomorphicAt_sub hfhol hhhol, hfh.mono fun p hp hpN => by simp only [hp hpN, sub_self]⟩
    have hξd := hξ.1.preserves _ hd
    refine ⟨fieldDeriv e ξ h, ?_, ?_⟩
    · exact mem_idealPow_sum Finset.univ fun m _ => mul_mem_idealPow (hξ.1.holomorphicAt m)
        (chartDeriv_mem_idealPow hξ.1.mem_source μ h hh)
    · have hsplit := GiraudAlong.fieldDeriv_add_eventuallyEq (ξ := ξ) hξ.1.mem_source
        (GiraudAlong.holomorphicAt_sub hfhol hhhol) hhhol
      have hfeq : (fun q => (f q - h q) + h q) = f := funext fun q => sub_add_cancel _ _
      rw [hfeq] at hsplit
      filter_upwards [hsplit, hξd.2] with p hp hp0 hpN
      rw [hp, hp0 hpN, zero_add]

/-- `cosupp(𝔞|_N, μ + 1) ⊆ cosupp((𝓓_{N,E} 𝔞)|_N, μ)`. -/
theorem cosupport_succ_subset_cosupport_logDerivIdealAlong (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    (μ : ℕ) : cosupport n N 𝔞 (μ + 1) ⊆ cosupport n N (logDerivIdealAlong N E 𝔞) μ :=
  fun _ hx => ⟨hx.1, orderGE_logDerivIdealAlong_of_orderGE_succ h𝔞 hx.2⟩

/-- `cosupp(𝔞|_N, μ + r) ⊆ cosupp((𝓓_{N,E}^r 𝔞)|_N, μ)`. -/
theorem cosupport_add_subset_cosupport_logIter (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    ∀ r μ : ℕ, cosupport n N 𝔞 (μ + r) ⊆ cosupport n N ((logDerivIdealAlong N E)^[r] 𝔞) μ
  | 0, _ => subset_rfl
  | r + 1, μ => by
    rw [Function.iterate_succ_apply']
    refine Subset.trans ?_ (cosupport_succ_subset_cosupport_logDerivIdealAlong
      (holomorphicAt_of_mem_logIter h𝔞 r) μ)
    rw [show μ + (r + 1) = μ + 1 + r by omega]
    exact cosupport_add_subset_cosupport_logIter h𝔞 r (μ + 1)

end Order

/-! ### Finite sums with one mark -/

section FinSum

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The cosupport of a finite sum with one mark is the intersection of the cosupports** (BM08 Lemma 3.8(1) for
equal marks; the empty sum, the zero ideal, has cosupport `N`). -/
theorem cosupport_finSumIdeal {N : Set M} {J : ℕ → GermIdeal n M}
    (hJ : ∀ i x g, (J i).mem x g → HolomorphicAt n g x) (m μ : ℕ) :
    cosupport n N (finSumIdeal J m) μ = {x | x ∈ N ∧ ∀ i < m, x ∈ cosupport n N (J i) μ} := by
  ext x
  constructor
  · rintro ⟨hxN, hx⟩
    refine ⟨hxN, fun i hi => ⟨hxN, fun g hg => hx g ?_⟩⟩
    show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J i).mem x s) x g
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨i, hi, hg⟩ (hJ i x g hg)
  · rintro ⟨hxN, hx⟩
    refine ⟨hxN, fun g hg => ?_⟩
    have hg' : IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J i).mem x s) x g := hg
    exact IsInSpanAt.vanishesToOrderOn hg' fun s ⟨i, hi, hs⟩ => (hx i hi).2 s hs

end FinSum

/-! ### The common-mark sum -/

section Marked

variable {n : ℕ} {X : CMfd.{0} n}

/-- **The cosupport of the common-mark sum** (BM08 Lemma 3.8(1), finite sums with `L = lcm` of the marks): for a
family on one carrier `N` (regular at each of its points) with positive marks and ideals of holomorphic germs,
`cosupp(∑_{i<m} 𝓘_i^{L/d_i}, L) = N ∩ ⋂_{i<m} cosupp(𝓘_i, d_i)`. -/
theorem cosupp_bmFiniteSum (Q : ℕ → MarkedIdeal n X) (m : ℕ)
    (hN : ∀ x ∈ (Q 0).N, ∃ k, RegularAtDim (n := n) (Q 0).N x k) (hSameN : ∀ i < m, (Q i).N = (Q 0).N)
    (hPos : ∀ i < m, 0 < (Q i).d) (hhol : ∀ i < m, ∀ x g, (Q i).ideal.mem x g → HolomorphicAt n g x) :
    (bmFiniteSum Q m).cosupp = {x | x ∈ (Q 0).N ∧ ∀ i < m, x ∈ (Q i).cosupp} := by
  obtain ⟨-, hspec⟩ := bmCommonMark_spec Q m hPos
  show cosupport n (Q 0).N (finSumIdeal (fun i => idealPow (Q i).ideal (bmCommonMark Q m / (Q i).d)) m)
    (bmCommonMark Q m) = _
  rw [cosupport_finSumIdeal (fun i x g hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg)]
  ext x
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => forall₂_congr fun i hi => ?_
  obtain ⟨-, hk, hmul⟩ := hspec i hi
  have h := MarkedIdealOperationsAlong.cosupport_idealPow_mul_eq_along hN (hhol i hi) hk (Q i).d
  rw [hmul] at h
  rw [h, MarkedIdeals.MarkedIdeal.cosupp, hSameN i hi]

/-- The empty common-mark sum has mark `1`. -/
theorem bmFiniteSum_zero_d (Q : ℕ → MarkedIdeal n X) : (bmFiniteSum Q 0).d = 1 := by
  show (Finset.range 0).lcm (fun i => (Q i).d) = 1
  simp

/-- The empty common-mark sum (the zero ideal, mark `1`) has cosupport the whole carrier. -/
theorem cosupp_bmFiniteSum_zero (Q : ℕ → MarkedIdeal n X) : (bmFiniteSum Q 0).cosupp = (Q 0).N := by
  show cosupport n (Q 0).N (finSumIdeal (fun i => idealPow (Q i).ideal (bmCommonMark Q 0 / (Q i).d)) 0)
    (bmCommonMark Q 0) = _
  rw [cosupport_finSumIdeal (fun i x g hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg)]
  ext x
  simp

/-- **`cosupp 𝔪 ⊆ cosupp 𝔪_j`** for `j ≤ d` (BM08 Lemma 3.2(3), logarithmic). -/
theorem cosupp_subset_cosupp_rawLogMarked (𝔪 : MarkedIdeal n X)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) {j : ℕ} (hj : j ≤ 𝔪.d) :
    𝔪.cosupp ⊆ (rawLogMarked 𝔪 j).cosupp := by
  have h := cosupport_add_subset_cosupport_logIter (N := 𝔪.N) (E := 𝔪.E) h𝔞 j (𝔪.d - j)
  rw [Nat.sub_add_cancel hj] at h
  exact h

/-- Marks of the logarithmic family are positive below the mark (the mark `0` occurs only at `j = d`). -/
theorem rawLogMarked_d_pos (𝔪 : MarkedIdeal n X) {k : ℕ} (hk : k < 𝔪.d) :
    ∀ i < k + 1, 0 < (rawLogMarked 𝔪 i).d := fun i hi => by
  show 0 < 𝔪.d - i
  omega

/-- **`cosupp 𝓒^k(𝔪) = cosupp 𝔪` for `k < d`** (BM08 Lemma 3.9, logarithmic): the common-mark sum of the first
`k + 1` logarithmic derivative marked ideals has the cosupport of `𝔪`. -/
theorem cosupp_bmFiniteSum_rawLogMarked (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) {k : ℕ} (hk : k < 𝔪.d) :
    (bmFiniteSum (rawLogMarked 𝔪) (k + 1)).cosupp = 𝔪.cosupp := by
  rw [cosupp_bmFiniteSum (rawLogMarked 𝔪) (k + 1) hN.2 (fun _ _ => rfl) (rawLogMarked_d_pos 𝔪 hk)
    (fun i _ => holomorphicAt_of_mem_logIter h𝔞 i)]
  ext x
  constructor
  · rintro ⟨-, hx⟩
    simpa [rawLogMarked, rawIter] using hx 0 (Nat.succ_pos k)
  · intro hx
    exact ⟨𝔪.cosupp_subset_N hx, fun i hi => cosupp_subset_cosupp_rawLogMarked 𝔪 h𝔞 (by omega) hx⟩

end Marked

end

end Hironaka.HironakaG8LogFiniteSumCut
