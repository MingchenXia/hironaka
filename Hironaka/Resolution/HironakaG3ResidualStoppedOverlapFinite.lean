import Hironaka.Resolution.HironakaG3ResidualOverlapBoundary
import Hironaka.Resolution.HironakaG3ResidualStoppingOpens
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ResidualStoppedOverlapFinite
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MaxLocusLocal NormalCrossings HironakaG3RTowerClass
  HironakaG3RBoundaryEmbedded HironakaG3StoppedDifferentBoundaries HironakaG3ResidualOverlapBoundary
  HironakaG3ResidualStoppingOpens HironakaOriginalTerminalOverlapComparison HironakaG3EmptyAwareHistory

/-- Actual stopped native histories for independently chosen complete residual
windows align on the literal overlap. -/
theorem residual_stopped_histories_overlap_of_window_avoid {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {ι : Type*} [LinearOrder ι] (V : Set X) (hVa : IsComplexAnalyticSubset (n := n) V)
    {r : ℕ} (hr : r < n) (hpure : V ⊆ closure (regularLocus (n := n) V r))
    (D : ι → Set X) (hD : ∀ i, IsClosed (D i)) (S R₁ R₂ : Finset ι)
    (hD₁ : Disjoint S R₁) (hD₂ : Disjoint S R₂)
    (hSNC₁ : IsSNCDivisor n ((R₁.sort (· ≤ ·)).map D))
    (hSNC₂ : IsSNCDivisor n ((R₂.sort (· ≤ ·)).map D))
    (hAvoid₁ : V ⊆ closure (V \ ⋃ H ∈ (R₁.sort (· ≤ ·)).map D, H))
    (hAvoid₂ : V ⊆ closure (V \ ⋃ H ∈ (R₂.sort (· ≤ ·)).map D, H))
    (U₁ U₂ : Opens X)
    (hVis₁ : ∀ i, i ∉ S → (D i ∩ (U₁ : Set X)).Nonempty → i ∈ R₁)
    (hVis₂ : ∀ i, i ∉ S → (D i ∩ (U₂ : Set X)).Nonempty → i ∈ R₂)
    {Y₁ Y₂ : CMfd.{0} n} (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁)
    (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂)
    (h₁ : bdryClass V r ((R₁.sort (· ≤ ·)).map D) U₁ Y₁ T₁)
    (h₂ : bdryClass V r ((R₂.sort (· ≤ ·)).map D) U₂ Y₂ T₂) :
    ∃ ψ : (openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      (openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
      EmptyAwareTowerIso (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
        (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁) (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂) ψ := by
  let E₁ := (R₁.sort (· ≤ ·)).map D
  let E₂ := (R₂.sort (· ≤ ·)).map D
  have hdom₁ := isInvDomain_bdry hVa hr hpure hSNC₁
  have hdom₂ := isInvDomain_bdry hVa hr hpure hSNC₂
  have htrace := residual_overlap_marked_boundary D S R₁ R₂ hD₁ hD₂ U₁ U₂ hVis₁ hVis₂ (vanishingIdeal (n := n) V)
  have hopen := residual_overlap_stopping_opens V hVa.isClosed r D hD S R₁ R₂ hD₁ hD₂ U₁ U₂ hVis₁ hVis₂
  exact stopped_structural_overlap_different_boundaries hn hVa.isClosed E₁ E₂ (bdryOpen V r E₁) (bdryOpen V r E₂)
    (disjoint_bdryOpen hVa.isClosed r hSNC₁.1) (disjoint_bdryOpen hVa.isClosed r hSNC₂.1)
    (fun x hx => regularAtDim_of_mem_bdryOpen hVa.isClosed hSNC₁.1 hx x.property)
    (fun x hx => regularAtDim_of_mem_bdryOpen hVa.isClosed hSNC₂.1 hx x.property)
    (subset_closure_inter_bdryOpen hVa.isClosed hpure hSNC₁.1 hAvoid₁)
    (subset_closure_inter_bdryOpen hVa.isClosed hpure hSNC₂.1 hAvoid₂)
    hdom₁ hdom₂ U₁ U₂ T₁ T₂ h₁ h₂ htrace hopen
end
end Hironaka.HironakaG3ResidualStoppedOverlapFinite
