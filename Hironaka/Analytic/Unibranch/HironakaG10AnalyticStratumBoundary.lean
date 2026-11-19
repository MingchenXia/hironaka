import Hironaka.Analytic.Unibranch.HironakaG10IrreducibleBoundary

/-! # Compact analytic boundaries of global stratum data -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary

open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10NativeAnalyticClosureDifference
  Hironaka.Analytic.Unibranch.HironakaG10IrreducibleBoundary
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus

noncomputable section

/-- Hironaka's boundary for one positive relative non-flat stratum. -/
def stratumBoundary {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (B W Z : Set X.obj.left) (i : ℕ) : Set X.obj.left :=
  closure ((strata f B (i + 1) ∩ W) \ Z) ∩ Z

/-- If the open domain contains `Z`, the boundary is independent of that
  domain and equals the global closure difference intersected with `Z`. -/
theorem stratumBoundary_eq_global {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (B W Z : Set X.obj.left) (i : ℕ) (hW : IsOpen W) (hZW : Z ⊆ W) :
    stratumBoundary f B W Z i = closure (strata f B (i + 1) \ Z) ∩ Z := by
  apply Subset.antisymm
  · exact inter_subset_inter_left Z (closure_mono (fun _ hx => ⟨hx.1.1, hx.2⟩))
  · intro x hx
    refine ⟨?_, hx.2⟩
    have hxcl := mem_closure_iff.mp hx.1
    rw [mem_closure_iff]
    intro O hO hxO
    obtain ⟨y, ⟨hyO, hyW⟩, hyS, hyZ⟩ :=
      hxcl (O ∩ W) (hO.inter hW) ⟨hxO, hZW hx.2⟩
    exact ⟨y, hyO, ⟨⟨hyS, hyW⟩, hyZ⟩⟩

/-- If the stratum and the flattener support are globally analytic and the
  domain contains the support, the actual boundary is analytic. -/
theorem stratumBoundary_analytic {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (B W Z : Set X.obj.left) (i : ℕ) (hW : IsOpen W) (hZW : Z ⊆ W)
    (hS : X.IsAnalyticSubset (strata f B (i + 1))) (hZ : X.IsAnalyticSubset Z) :
    X.IsAnalyticSubset (stratumBoundary f B W Z i) := by
  rw [stratumBoundary_eq_global f B W Z i hW hZW]
  exact isAnalyticSubset_inter (isAnalyticSubset_closure_diff hS hZ) hZ

/-- On a compact base, this boundary is compact and lies in the absolute
  non-flat image. -/
theorem stratumBoundary_compact_subset_nonflat {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B W Z : Set X.obj.left) (i : ℕ)
    (hW : IsOpen W) (hZW : Z ⊆ W)
    (hS : X.IsAnalyticSubset (strata f B (i + 1))) (hZ : X.IsAnalyticSubset Z) :
    IsCompact (stratumBoundary f B W Z i) ∧ stratumBoundary f B W Z i ⊆ nonflatImage f := by
  exact ⟨(stratumBoundary_analytic f B W Z i hW hZW hS hZ).isClosed.isCompact,
    closed_stratum_boundary_subset_nonflatImage f B W Z i hS.isClosed⟩

end
end Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary
