import Hironaka.Resolution.HironakaG4PreparedDivisorChart
import Hironaka.Resolution.HironakaG4WeightedBinomialStraightening
import Hironaka.Analytic.RegularAtDimTransport

/-! A weighted binomial chart from an actual normal correction. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG4WeightedBinomialChart
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupFlatCoordinates NormalCrossings
  HironakaG34CoordinateScaling HironakaG4OptionalBoundaryTransform HironakaG4OptionalDivisorMasks
  HironakaG4WeightedBinomialStraightening

variable {n : ℕ} {X : CMfd.{u} n}

/-- A prepared actual chart plus a normal correction produces an actual chart
with unchanged carrier and divisor equations and the selected weighted binomial. -/
theorem exists_weighted_binomial_chart {N H : Set X} {E : List (Set X)} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (S : Finset (Fin n)) (m : Fin E.length → Option (Fin n))
    (hm : DivisorMasksValid S m)
    (hN : ∀ y ∈ flatDomain Φ, y ∈ N ↔ flatMap Φ y ∈ coordSubspace S)
    (hE : ∀ i y, y ∈ flatDomain Φ → (y ∈ E.get i ↔
      flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))))
    (s t : Fin n) (c : Fin n → ℕ) (hs : s ∈ S) (hst : t ≠ s) (hcs : c s = 0)
    (g : ComplexModel n → ℂ) (U : Set (ComplexModel n)) (hU : IsOpen U)
    (h0U : (0 : ComplexModel n) ∈ U) (hg : DifferentiableOn ℂ g U) (hg0 : g 0 = 0)
    (hvan : ∀ z ∈ U, z ∈ coordSubspace S → g z = 0)
    (hderiv : fderiv ℂ g 0 (EuclideanSpace.single s 1) ≠ 0)
    (hH : ∀ y ∈ flatDomain Φ, flatMap Φ y ∈ U →
      (y ∈ H ↔ g (flatMap Φ y) + flatMap Φ y t * ∏ b, flatMap Φ y b ^ c b = 0)) :
    ∃ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x),
      Ψ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Ψ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ y ∈ flatDomain Ψ, y ∈ N ↔ flatMap Ψ y ∈ coordSubspace S) ∧
      (∀ i y, y ∈ flatDomain Ψ → (y ∈ E.get i ↔
        flatMap Ψ y ∈ optionalCoordLocus ((m i).map (fun k => {k})))) ∧
      ∀ y ∈ flatDomain Ψ, y ∈ H ↔ binomial s t c (flatMap Ψ y) = 0 := by
  classical
  obtain ⟨Θ, hΘU, hΘ0, hΘs, hΘother, hΘcarrier⟩ :=
    exists_carrier_preserving_replacement hU h0U hg hg0 S s hs hvan hderiv
  let Ψ := RegularAtDimTransport.LocalHolomorphicEquivAt.comp Φ Θ hΦ0
  refine ⟨Ψ, fun w hw => hΦsrc hw.1, ?_, ?_, ?_, ?_⟩
  · change Θ.toFun (Φ.toFun (chartAt (ComplexModel n) x x)) = 0
    rw [hΦ0, hΘ0]
  · intro y hy
    have hyΦ : y ∈ flatDomain Φ := ⟨hy.1, hy.2.1⟩
    have hyΘ : flatMap Φ y ∈ Θ.source := hy.2.2
    change y ∈ N ↔ Θ.toFun (flatMap Φ y) ∈ coordSubspace S
    exact (hN y hyΦ).trans (hΘcarrier _ hyΘ)
  · intro i y hy
    have hyΦ : y ∈ flatDomain Φ := ⟨hy.1, hy.2.1⟩
    change y ∈ E.get i ↔ Θ.toFun (flatMap Φ y) ∈ optionalCoordLocus ((m i).map (fun k => {k}))
    cases hmi : m i with
    | none => simpa [hmi, optionalCoordLocus] using hE i y hyΦ
    | some k =>
      have hks : k ≠ s := by
        intro hks
        subst k
        exact hm.1 i s hmi hs
      have heq := hΘother (flatMap Φ y) k hks
      simpa [hmi, optionalCoordLocus, coordSubspace, heq] using hE i y hyΦ
  · intro y hy
    have hyΦ : y ∈ flatDomain Φ := ⟨hy.1, hy.2.1⟩
    have hyΘ : flatMap Φ y ∈ Θ.source := hy.2.2
    change y ∈ H ↔ binomial s t c (Θ.toFun (flatMap Φ y)) = 0
    rw [binomial_after_replacement Θ g s t c hst hcs hΘs hΘother]
    exact hH y hyΦ (hΘU hyΘ)

end
end Hironaka.HironakaG4WeightedBinomialChart
