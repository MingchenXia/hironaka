import Hironaka.Analytic.Unibranch.HironakaG10VanishingStalkIdentity
import Hironaka.Analytic.Unibranch.HironakaG10LocalIntrinsicIdeal
import Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary

/-! # A tracked boundary lies in the next relative non-flat stratum -/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryNextStratum

open Hironaka HironakaG10HirIdealGerms
  HironakaIntrinsicReducedCentreOpenPullback
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
  Hironaka.Analytic.Unibranch.HironakaG10LocalIntrinsicIdeal
  Hironaka.Analytic.Unibranch.HironakaG10LocalBoundaryGlobalCut
  Hironaka.Analytic.Unibranch.HironakaG10VanishingStalkIdentity
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary

noncomputable section

/-- The boundary of a locally analytic stratum against an actual local
  flattener lies in the next relative non-flat stratum. -/
theorem tracked_boundary_subset_next_stratum {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B : Set X.obj.left) (Z : LocalFlattener f) (i : ℕ)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B (i + 1))) :
    stratumBoundary f B Z.V Z.support i ⊆ strata f B (i + 2) := by
  intro x hx
  have hxZ : x ∈ Z.support := hx.2
  have hxS : x ∈ strata f B (i + 1) :=
    mem_of_mem_closure_inter_domain Z.isOpen hS hxZ.1
      (closure_mono (show (strata f B (i + 1) ∩ Z.V) \ Z.support ⊆
        strata f B (i + 1) ∩ Z.V from sdiff_subset) hx.1)
  change x ∈ strata f B (i + 1) ∧ ¬ FlatOverAt f x
    (vanishingIdealAt X.obj.left (strata f B (i + 1)) x)
  refine ⟨hxS, ?_⟩
  intro hflat
  let IS := intrinsicCentreStalkRange X.obj.left (strata f B (i + 1))
  have hIS : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IS :=
    local_intrinsicCentreStalkRange_finitelyGenerated X Z.V _ hS
  have hle : Z.H x ≤ IS x := by
    apply (Z.flattener x hxZ.1 hxZ.2 (IS x)).1
    change FlatOverAt f x (intrinsicCentreStalkRange X.obj.left (strata f B (i + 1)) x)
    rw [← vanishingIdealAt_eq_intrinsicCentreStalkRange]
    exact hflat
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ Z.V ∧ Z.H y ≤ IS y := by
    filter_upwards [Z.isOpen.mem_nhds hxZ.1,
      eventually_le_of_le Z.fg hIS Z.isOpen Z.isOpen hxZ.1 hxZ.1 hle] with y hyV hy
    exact ⟨hyV,hy⟩
  obtain ⟨y,hy,hyS,hyNot⟩ := (mem_closure_iff_nhds.mp hx.1) _ hnear
  have hISproper : IS y ≠ ⊤ := by
    intro htop
    have hmax := intrinsicCentreStalkRange_le_maximalIdeal X.obj.left (strata f B (i + 1)) y hyS.1
    change IS y ≤ IsLocalRing.maximalIdeal (X.obj.left.presheaf.stalk y) at hmax
    rw [htop] at hmax
    exact (IsLocalRing.maximalIdeal.isMaximal (X.obj.left.presheaf.stalk y)).ne_top (top_le_iff.mp hmax)
  have hZproper : Z.H y ≠ ⊤ := fun htop => hISproper (top_le_iff.mp (htop ▸ hy.2))
  exact hyNot ⟨hy.1,hZproper⟩

end
end Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryNextStratum
