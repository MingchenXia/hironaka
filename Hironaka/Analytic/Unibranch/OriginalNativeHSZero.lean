import Hironaka.Analytic.Unibranch.OriginalLocalEmbeddingStalkHS
import Hironaka.Resolution.HironakaG1NativeFiniteProductHSValues

/-! Actual HS(0)=1 at ANY actual native point, with no singularity premise.
Full Blueprint FIRST: original-native-hs-zero.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSZero
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  SourceReducedComplexSpace HironakaHolomorphicJetChartInvariance
  HironakaActualReferenceHSSingularCentre OriginalLocalEmbeddingStalkHS

/-- Normalization at EVERY genuine native point, regular or singular. -/
theorem originalStalkHS_zero (X : SourceReducedComplexSpace) (x : X.obj.left) :
    originalStalkHS X x 0=1 := by
  let e := LocalEmbedding.ofPoint X x
  obtain ⟨c,hc⟩ := LocalEmbedding.mem_range_ofPoint X x
  have hz := BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (n := e.dim) e.analytic.isClosed
  have hzero := hilbertSamuelAt_zero_eq_support (vanishingIdeal (n := e.dim) e.carrier)
    (CartanIrreducible.cartanCoherence e.carrier e.analytic) c.val
  have hmem : c.val∈(vanishingIdeal (n := e.dim) e.carrier).zeroLocus := hz.symm ▸ c.property
  have hnative := originalStalkHS_localEmbedding_eq X e c 0
  rw [hc] at hnative
  exact hnative.trans (by simpa only [if_pos hmem] using hzero)

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSZero
