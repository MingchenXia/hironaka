import Hironaka.Analytic.Unibranch.HironakaG10LocalSupportAnalytic
import Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
import Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary

/-! # Local analytic Hironaka boundary for an actual flattener -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open Hironaka

namespace Hironaka.Analytic.Unibranch.HironakaG10LocalStratumClosure

open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10LocalSupportAnalytic
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10NativeAnalyticClosureDifference
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary
open Hironaka.ClosureDifferenceAnalytic

noncomputable section

/-- For an actual local flattener, if a positive stratum is locally analytic on the domain
  then the closure of its complement has native analytic charts at every point of the
  flattener domain. No global analyticity of the flattener support is assumed. -/
theorem locallyAnalytic_stratumClosure
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (B : Set X.obj.left)
    (Z : LocalFlattener f) (i : ℕ)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B (i + 1))) (x : X.obj.left) (hx : x ∈ Z.V) :
    ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧ range e.toPoint ⊆ Z.V ∧
      ∃ A : Set e.ambient, IsComplexAnalyticSubset (n := e.dim) A ∧
        e.toPoint ⁻¹' closure ((strata f B (i + 1) ∩ Z.V) \ Z.support) = Subtype.val ⁻¹' A := by
  obtain ⟨e,he,heV,A,hA,htrace⟩ := local_support_analytic Z x hx
  let SA : Set e.ambient := Subtype.val '' (e.toPoint ⁻¹' strata f B (i + 1))
  let SZ : Set e.ambient := Subtype.val '' (e.toPoint ⁻¹' Z.support)
  have hSA : IsComplexAnalyticSubset (n := e.dim) SA := analytic_image_local_trace hS e heV
  have hSZ : IsComplexAnalyticSubset (n := e.dim) SZ := by
    dsimp [SZ]
    rw [htrace, Set.image_preimage_eq_inter_range, Subtype.range_coe]
    exact hA.inter e.analytic
  refine ⟨e,he,heV,closure (SA \ SZ),
    isComplexAnalyticSubset_closure_diff hSA hSZ, ?_⟩
  have heW : e.toPoint ⁻¹' Z.V = univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro z
    exact heV ⟨z,rfl⟩
  have hdiff : e.toPoint ⁻¹' ((strata f B (i + 1) ∩ Z.V) \ Z.support) =
      (e.toPoint ⁻¹' strata f B (i + 1)) \ (e.toPoint ⁻¹' Z.support) := by
    rw [Set.preimage_sdiff, Set.preimage_inter, heW, Set.inter_univ]
  change e.toPoint ⁻¹' closure ((strata f B (i + 1) ∩ Z.V) \ Z.support) = _
  rw [e.isOpenEmbedding_toPoint.isOpenMap.preimage_closure_eq_closure_preimage
    e.isOpenEmbedding_toPoint.continuous, hdiff,
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    Set.image_sdiff Subtype.val_injective]

end
end Hironaka.Analytic.Unibranch.HironakaG10LocalStratumClosure
