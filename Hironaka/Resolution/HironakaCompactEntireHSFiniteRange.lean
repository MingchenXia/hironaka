import Hironaka.Resolution.HironakaCompactAnalyticDescendingChain
import Hironaka.Resolution.HironakaActualHilbertSamuelWellFounded
import Hironaka.Resolution.HironakaActualWholeAmbientHSSuperlevel

/-! Compact finiteness of actual entire Hilbert--Samuel profiles, via their
well-quasi-order and analytic descending-chain stability. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaCompactEntireHSFiniteRange
open Hironaka.HolomorphicIdealSheaves
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci HironakaActualHilbertSamuelWellFounded
  HironakaActualWholeAmbientHSSuperlevel HironakaCompactAnalyticDescendingChain
noncomputable section

/-- Actual coherence and compactness imply finite range of the SAME entire
Hilbert--Samuel profiles, without a supplied cutoff or resolution. -/
theorem compact_entire_hs_finite_range {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (A : GermIdeal n M) (hA : A.IsCoherent) (K : Set M) (hK : IsCompact K) :
    (hilbertSamuelAt A '' K).Finite := by
  classical
  by_contra hInf
  have hInfinite : (hilbertSamuelAt A '' K).Infinite := hInf
  let e := hInfinite.natEmbedding _
  let P : ℕ → ActualHilbertSamuelProfile n := fun i =>
    ⟨(e i).val, by
      obtain ⟨x,hxK,hx⟩ := (e i).property
      rw [← hx]
      exact analytic_hilbertSamuel_realizable
        (wholeChartStalkIdeal A x x (mem_chart_source (ComplexModel n) x))⟩
  have hPInj : Function.Injective P := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun p : ActualHilbertSamuelProfile n => p.val) hij
  obtain ⟨g,hg⟩ := (actual_hilbertSamuel_wellQuasiOrdered n).exists_monotone_subseq P
  let H : ℕ → (ℕ → ℕ) := fun i => (P (g i)).val
  have hH : ∀ {i j : ℕ}, i ≤ j → H i ≤ H j := by
    intro i j hij
    exact hg i j hij
  have hHInj : Function.Injective H := by
    intro i j hij
    apply g.injective
    apply hPInj
    exact Subtype.ext hij
  let D : ℕ → Set M := fun i => actualWholeAmbientHSSuperlevel A (H i)
  have hD : ∀ i, IsComplexAnalyticSubset (n := n) (D i) :=
    fun i => isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel A hA (H i)
  have hanti : Antitone D := by
    intro i j hij x hx ℓ
    exact le_trans (hH hij ℓ) (hx ℓ)
  obtain ⟨N,hstable⟩ := analytic_descending_chain_stable_on_compact hD hanti hK
  obtain ⟨x,hxK,hxH⟩ := (e (g N)).property
  have hxHN : hilbertSamuelAt A x = H N := hxH
  have hxDN : x ∈ D N := by
    intro ℓ
    rw [hxHN]
  have hxDN1 : x ∈ D (N+1) ∩ K := (hstable (N+1) (Nat.le_succ N)).symm ▸ ⟨hxDN,hxK⟩
  have hback : H (N+1) ≤ H N := by
    intro ℓ
    simpa only [← hxHN] using hxDN1.1 ℓ
  have hEq : H N = H (N+1) := le_antisymm (hH (Nat.le_succ N)) hback
  have hbad : N = N+1 := hHInj hEq
  omega
end
end Hironaka.HironakaCompactEntireHSFiniteRange
