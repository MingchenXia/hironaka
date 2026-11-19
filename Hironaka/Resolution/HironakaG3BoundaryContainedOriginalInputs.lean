import Hironaka.Resolution.HironakaG3BoundaryContainedGlobalLift
import Hironaka.Resolution.HironakaActualNativeInvariantDomain
import Hironaka.Resolution.HironakaG3RBoundaryEmbedded
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3BoundaryContainedOriginalInputs
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeInvariantDomain
  HironakaActualClosedContactBlowupRestriction HironakaG3RBoundaryEmbedded
open ResolutionInvariantSpec (IsInvDomain)

/-- The coherent ambient ideal, its exact native trace, native domain and
stopping-open hypotheses follow from the actual analytic contained target. -/
theorem original_contained_input_data
    {d t : ℕ} (_hd : 0 < d) {X : CMfd.{0} (d+t)}
    (N : Set X) (_hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (hB : IsSNCDivisor (d+t) B) (hTrans : IsTransverse (d+t) N B) :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    ∀ (V : Set (nativeManifold (Nat.le_add_right d t) N hN))
      (_hVa : IsComplexAnalyticSubset (n := d) V)
      (_hWa : IsComplexAnalyticSubset (n := d+t) ((Subtype.val : N → X) '' V))
      {r : ℕ} (_hr : r < d) (_hpure : V ⊆ closure (regularLocus (n := d) V r))
      (_hAvoid : V ⊆ closure (V \ ⋃ H ∈ B.map ((Subtype.val : N → X) ⁻¹' ·), H)),
      let E := B.map ((Subtype.val : N → X) ⁻¹' ·)
      let O := bdryOpen V r E
      (vanishingIdeal (n := d+t) ((Subtype.val : N → X) '' V)).IsCoherent ∧
      (vanishingIdeal (n := d+t) N).Le (vanishingIdeal (n := d+t) ((Subtype.val : N → X) '' V)) ∧
      GermIdeal.pullback (m := d) (Subtype.val : N → X)
        (vanishingIdeal (n := d+t) ((Subtype.val : N → X) '' V)) = vanishingIdeal (n := d) V ∧
      IsInvDomain d (⟨univ, E, vanishingIdeal (n := d) V, 1⟩ : MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)) ∧
      (∀ H ∈ E, Disjoint H (O : Set (nativeManifold (Nat.le_add_right d t) N hN))) ∧
      (∀ x : O, (x : nativeManifold (Nat.le_add_right d t) N hN) ∈ V → RegularAtDim (n := d) V x r) ∧
      V ⊆ closure (V ∩ O) := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  intro V hVa hWa r hr hpure hAvoid
  let E := B.map ((Subtype.val : N → X) ⁻¹' ·)
  let O := bdryOpen V r E
  have hE : IsSNCDivisor d E := isSNCDivisor_native_preimage (by omega) (Nat.le_add_right d t) hN hB hTrans
  have hEc : ∀ H ∈ E, IsClosed H := hE.1
  refine ⟨CartanIrreducible.cartanCoherence _ hWa, ?_, ?_, isInvDomain_bdry hVa hr hpure hE,
    disjoint_bdryOpen hVa.isClosed r hEc, ?_, subset_closure_inter_bdryOpen hVa.isClosed hpure hEc hAvoid⟩
  · apply BlowupFunctionTransform.vanishingIdeal_le_of_subset
    rintro _ ⟨p,_hp,rfl⟩
    exact p.property
  · exact centre_pullback (Nat.le_add_right d t) hN V
  · intro x hx
    exact regularAtDim_of_mem_bdryOpen hVa.isClosed hEc hx x.property

end
end Hironaka.HironakaG3BoundaryContainedOriginalInputs
