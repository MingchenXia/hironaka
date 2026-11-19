import Hironaka.Resolution.HironakaG1CommonGraphHSCut
import Hironaka.Resolution.HironakaG1ProperCarrierNormalContact
import Hironaka.Resolution.HironakaG11PresLineState

/-! The actual ambient Hilbert–Samuel cut of the literal one-normal padding. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1ProperNormalNativeCut
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualOpenZeroSectionDifferentials HironakaActualCentreJointJets
  HironakaRelativeNormalIdeal HironakaActualIntrinsicStableAmbientIso
  HironakaActualAnalyticSubspacePresentationIndependence HironakaReducedComplexAnalyticSpaces
  HironakaG1CommonGraphHSCut HironakaActualReferenceHSSingularCentre
  HironakaG11PresLineState HironakaHolomorphicJetChartInvariance HironakaEmbeddedAnalytic
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  MarkedIdeals ResolutionInvariantSpec

variable {n : ℕ} {U : Opens (ComplexModel n)}

private theorem projection_zeroSection_eq (x : U) : projection U (zeroSection U x) = x := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x.val

private theorem zeroSection_projection_eq {z : productOpen U}
    (hz : actualJointNormalProjection n 1 z.val = 0) : zeroSection U (projection U z) = z := by
  apply Subtype.ext
  change tangentInclusion n 1 (tangentProjection n 1 z.val) = z.val
  simpa only [join,hz,map_zero,add_zero] using join_projections (n := n) (m := 1) z.val

theorem liftedCarrier_isAnalytic {W : Set U}
    (hW : IsComplexAnalyticSubset (n := n) W) :
    IsComplexAnalyticSubset (n := n+1) (liftedCarrier W) := by
  have hbase := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (projection_contMDiff U) hW
  have hnormal := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    ((actualJointNormalProjection n 1).contMDiff.comp
      (contMDiff_subtype_val (U := productOpen U)))
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel 1))
  exact hbase.inter hnormal


/-- The literal zero graph carries the entire source cut and its ambient upper
bound, even at points of the product off the graph. -/
theorem liftedCarrier_cut_and_bound {W : Set U}
    (hW : IsComplexAnalyticSubset (n := n) W) (H : ℕ → ℕ) (hH : 0 < H 0) :
    {z | ∀ q, hilbertSamuelAt (vanishingIdeal (n := n+1) (liftedCarrier W)) z q = H q} =
      zeroSection U '' {x | ∀ q, hilbertSamuelAt (vanishingIdeal (n := n) W) x q = H q} ∧
    ((∀ x q, hilbertSamuelAt (vanishingIdeal (n := n) W) x q ≤ H q) →
      ∀ z q, hilbertSamuelAt (vanishingIdeal (n := n+1) (liftedCarrier W)) z q ≤ H q) := by
  have hMaps (x : U) (hx : x ∈ W) : zeroSection U x ∈ liftedCarrier W := by
    refine ⟨?_, ?_⟩
    · simpa only [projection_zeroSection_eq] using hx
    · exact actualJointNormalProjection_tangent n 1 x.val
  have hProj (z : productOpen U) (hz : z ∈ liftedCarrier W) : projection U z ∈ W := hz.1
  let e := actualSubspaceMutualRestrictionIso (zeroSection_contMDiff U) (projection_contMDiff U)
    hMaps hProj (fun x _ => projection_zeroSection_eq x) (fun _ hz => zeroSection_projection_eq hz.2)
  obtain ⟨hCut,hUpper⟩ := ambient_cut_and_bound_of_intrinsic_iso (liftedCarrier_isAnalytic hW) e
    (actualSubspaceMap_point (zeroSection_contMDiff U) hMaps) H hH
  refine ⟨hCut.trans ?_, hUpper⟩
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.val,hx,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    have hxW : x ∈ W := by
      by_contra hnx
      have h0 := hx 0
      rw [hilbertSamuelAt_zero_eq_support _ (CartanIrreducible.cartanCoherence W hW),
        BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hW.isClosed, if_neg hnx] at h0
      exact (Nat.ne_of_gt hH) h0.symm
    exact ⟨⟨x,hxW⟩,hx,rfl⟩

/-- The actual padded record's cosupport is the entire ambient HS cut of the
zero graph, with the same source reference and an ambient upper bound. -/
theorem properNormalMarked_native_cut_and_bound {W : Set U} {Q : MarkedIdeal n U}
    (H : ℕ → ℕ) (hQ : NativeHSState (X := BlowupTowers.CMfd.of (n := n) U) Q W H) (hDomain : IsInvDomain n Q) :
    (properNormalMarked Q).cosupp =
      {z | ∀ q, hilbertSamuelAt (vanishingIdeal (n := n+1) (liftedCarrier W)) z q = H q} ∧
    (∀ z q, hilbertSamuelAt (vanishingIdeal (n := n+1) (liftedCarrier W)) z q ≤ H q) := by
  obtain ⟨hSing,hW,_,_,_,_,_,_,_,_,_,_,_,hSourceCut,hSourceUpper,_⟩ := hQ
  obtain ⟨m,X₀,W₀,x₀,hW₀,hx₀,rfl⟩ := hSing
  have hPos : 0 < hilbertSamuelAt (vanishingIdeal (n := m) W₀) x₀ 0 := by
    rw [hilbertSamuelAt_zero_eq_support _ (CartanIrreducible.cartanCoherence W₀ hW₀),
      BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hW₀.isClosed,
      if_pos (singularSet_subset W₀ hx₀)]
    exact Nat.zero_lt_one
  obtain ⟨hCut,hBound⟩ := liftedCarrier_cut_and_bound hW _ hPos
  exact ⟨(properNormalMarked_cosupp Q hDomain).trans
    ((congrArg (fun s => zeroSection U '' s) hSourceCut).trans hCut.symm), hBound hSourceUpper⟩

#print axioms properNormalMarked_native_cut_and_bound

end
end Hironaka.HironakaG1ProperNormalNativeCut
