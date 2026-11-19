import Hironaka.Resolution.HironakaG4PreparedGammaChart
import Hironaka.Blowup.NormalCrossingsInvariance

/-! Move a prepared weighted chart from an open subtype to its ambient manifold. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG4OpenGammaChart
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupFlatCoordinates NormalCrossings AnalyticSubsetOpens
  HironakaG4WeightedBinomialStraightening HironakaG4OptionalBoundaryTransform
  HironakaG34CoordinateScaling

variable {n : ℕ} {X : CMfd.{u} n} {ι : Type v}

/-- The same local equivalence supplies the ambient weighted chart; its
entire domain lies in the open subtype on which it was constructed. -/
theorem ambient_gamma_chart_of_open (U : Opens X) (x : U)
    (N H : Set X) (D : ι → Set X) (S : Finset (Fin n)) (m : ι → Option (Fin n))
    (s t : Fin n) (c : Fin n → ℕ)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hN : ∀ y ∈ flatDomain Φ, y ∈ (Subtype.val : U → X) ⁻¹' N ↔ flatMap Φ y ∈ coordSubspace S)
    (hD : ∀ i y, y ∈ flatDomain Φ → (y ∈ (Subtype.val : U → X) ⁻¹' D i ↔
      flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))))
    (hH : ∀ y ∈ flatDomain Φ, y ∈ (Subtype.val : U → X) ⁻¹' H ↔ binomial s t c (flatMap Φ y) = 0) :
    ∃ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (x : X) x),
      Ψ.source ⊆ (chartAt (ComplexModel n) (x : X)).target ∧
      (∀ y ∈ flatDomain Ψ, y ∈ U) ∧
      (∀ y ∈ flatDomain Ψ, y ∈ N ↔ flatMap Ψ y ∈ coordSubspace S) ∧
      (∀ i y, y ∈ flatDomain Ψ → (y ∈ D i ↔
        flatMap Ψ y ∈ optionalCoordLocus ((m i).map (fun k => {k})))) ∧
      ∀ y ∈ flatDomain Ψ, y ∈ H ↔ binomial s t c (flatMap Ψ y) = 0 := by
  refine ⟨Φ, hsrc.trans (chartAt_opens_target_subset x), ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact mem_opens_of_chart_mem_target hy.1 (hsrc hy.2)
  · intro y hy
    have hyU : y ∈ U := mem_opens_of_chart_mem_target hy.1 (hsrc hy.2)
    exact hN ⟨y,hyU⟩ ⟨mem_chartAt_opens_source.mpr hy.1,hy.2⟩
  · intro i y hy
    have hyU : y ∈ U := mem_opens_of_chart_mem_target hy.1 (hsrc hy.2)
    exact hD i ⟨y,hyU⟩ ⟨mem_chartAt_opens_source.mpr hy.1,hy.2⟩
  · intro y hy
    have hyU : y ∈ U := mem_opens_of_chart_mem_target hy.1 (hsrc hy.2)
    exact hH ⟨y,hyU⟩ ⟨mem_chartAt_opens_source.mpr hy.1,hy.2⟩

end
end Hironaka.HironakaG4OpenGammaChart
