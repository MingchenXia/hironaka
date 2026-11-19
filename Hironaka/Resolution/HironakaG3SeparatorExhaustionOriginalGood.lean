import Hironaka.Resolution.HironakaG3SeparatorBoundaryFootprint
import Hironaka.Resolution.HironakaG3SeparatorComposedOriginalGood
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatorExhaustionOriginalGood
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass HironakaG3REmbeddedGlobalSNC
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedMixedGluing HironakaG3IndexedMixedGlobalSNC
  HironakaG3IndexedMixedBad HironakaG3IndexedMixedChartBoundary
  HironakaG3SeparatorBoundaryFootprint HironakaG3SeparatorComposedOriginalGood

theorem separator_exhaustion_composed_original_good {n d : ℕ} {X Z Y : CMfd.{0} n}
    {ι κ ρ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hLF : LocallyFinite (fun i => (V i).carrier)) (hDim : ∀ i, (V i).dim < n)
    (hDistinct : ∀ i j, i ≠ j → ¬ (V i).carrier ⊆ (V j).carrier)
    (W : Set X) (hW : W = ⋃ i, (V i).carrier) (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    {P : Z → X} (hG : IsGluedFrom (indexedMixedClass V D) Z P)
    (Ex : SNCExhaustion Z) (B : ρ → Set Z)
    (hCharts : ∀ k, ∃ (c : TowerChart (indexedMixedClass V D) Z P) (Ef : List (Set c.Y)),
      MixedBoundaryWitness V D c Ef ∧ Ex.W k = c.V ∧ Ex.B k = mixedChartBoundary V D c Ef)
    (hUnion : (⋃ j, B j) = ⋃ k, ⋃ H ∈ Ex.B k, H)
    (Q : Y → Z) (hQm : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ Q)
    (hQ : IsIsomorphismOver n Q
      (⋃ i, (strictTransform n P (V i).carrier \ regularLocus (n := n) (strictTransform n P (V i).carrier) (V i).dim) ∪
        (strictTransform n P (V i).carrier ∩ ⋃ j, B j))ᶜ) :
    IsIsomorphismOver n (P ∘ Q) (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ j, D j)ᶜ := by
  have hB : (⋃ j, B j) ⊆ P ⁻¹' ((⋃ j, D j) ∪ indexedMixedBad V) := by
    rw [hUnion]
    exact separator_global_boundary_footprint V D hDim hDistinct hD Ex hCharts
  exact separator_composed_original_good V hLF hDim hDistinct W hW D B hG hB Q hQm hQ
end
end Hironaka.HironakaG3SeparatorExhaustionOriginalGood
