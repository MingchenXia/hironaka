import Hironaka.Resolution.HironakaG8SuccExponents

/-! # Divisibility of the original exceptional sum

A positive-mark exceptional sum is divisible at a trace exactly when it is
already divisible to the full mark. This isolates the arithmetic dichotomy
needed in the successor residual.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ExceptionalDivisibility
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder DivisorExponentAlong
  HironakaG11InvBMLower HironakaG8SuccExponents

variable {n : ℕ} {Y : CMfd.{0} n}

/-- Full-mark divisibility is equivalent to the carrier trace lying in
every original exceptional member near the point. -/
theorem exceptionalTerm_divisible_iff_trace
    {N H : Set Y} {S : List (Set Y)} (hS : ∀ D ∈ S, IsClosed D)
    {δ : ℕ} (hδ : 1 ≤ δ) (y : Y) :
    IsDivNearAlong n N (exceptionalTermBM (n := n) S δ) H δ y ↔
      ∀ᶠ z in 𝓝 y, z ∈ N → z ∈ H → ∀ D ∈ S, z ∈ D := by
  unfold IsDivNearAlong
  constructor
  · intro h
    filter_upwards [h] with z hz hzN hzH
    have hzδ := hz hzN hzH
    have hz1 : z ∈ cosupport n N (exceptionalTermBM (n := n) S δ) 1 :=
      ⟨hzδ.1, OrderGE.mono hδ hzδ.2⟩
    exact mem_of_mem_cosupport_one_exceptionalTermBM hS hz1
  · intro h
    filter_upwards [h] with z hz hzN hzH
    exact mem_cosupport_exceptionalTermBM hzN (hz hzN hzH)

/-- For closed members and positive mark, divisibility of the exceptional
sum along any carrier and trace has no intermediate positive exponent. -/
theorem exceptionalTerm_divisible_one_iff_mark
    {N H : Set Y} {S : List (Set Y)} (hS : ∀ D ∈ S, IsClosed D)
    {δ : ℕ} (hδ : 1 ≤ δ) (y : Y) :
    IsDivNearAlong n N (exceptionalTermBM (n := n) S δ) H 1 y ↔
      IsDivNearAlong n N (exceptionalTermBM (n := n) S δ) H δ y := by
  unfold IsDivNearAlong
  constructor
  · intro h
    filter_upwards [h] with z hz hzN hzH
    have hz1 := hz hzN hzH
    exact mem_cosupport_exceptionalTermBM hzN
      (mem_of_mem_cosupport_one_exceptionalTermBM hS hz1)
  · intro h
    filter_upwards [h] with z hz hzN hzH
    have hzδ := hz hzN hzH
    exact ⟨hzδ.1, OrderGE.mono hδ hzδ.2⟩

/-- Every positive threshold up to the mark has exactly the same
exceptional-sum divisibility test. -/
theorem exceptionalTerm_divisible_below_iff_trace
    {N H : Set Y} {S : List (Set Y)} (hS : ∀ D ∈ S, IsClosed D)
    {δ e : ℕ} (he : 1 ≤ e) (heδ : e ≤ δ) (y : Y) :
    IsDivNearAlong n N (exceptionalTermBM (n := n) S δ) H e y ↔
      ∀ᶠ z in 𝓝 y, z ∈ N → z ∈ H → ∀ D ∈ S, z ∈ D := by
  have hδ : 1 ≤ δ := le_trans he heδ
  rw [← exceptionalTerm_divisible_iff_trace hS hδ y]
  constructor
  · intro h
    exact (exceptionalTerm_divisible_one_iff_mark hS hδ y).mp (h.mono he)
  · intro h
    exact h.mono heδ

end
end Hironaka.HironakaG8ExceptionalDivisibility
