import Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryCoincidence
import Hironaka.Analytic.Unibranch.HironakaG10LocalStratumClosure
import Hironaka.Analytic.Unibranch.HironakaG10LocalIntrinsicIdeal
import Hironaka.Analytic.Unibranch.HironakaG10SchemeBoundaryThickening

/-! # The source boundary ideal is supported in C_i near tracked boundaries -/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10BoundarySupportContainment

open Hironaka HironakaIntrinsicReducedCentreOpenPullback
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
  Hironaka.Analytic.Unibranch.HironakaG10LocalIntrinsicIdeal
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary
  Hironaka.Analytic.Unibranch.HironakaG10SchemeBoundaryThickening
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryCSet
  Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryCoincidence

/-- On the flattener domain, the nonunit locus of the actual nonradical
  scheme-boundary ideal is exactly its geometric boundary support. -/
theorem schemeBoundary_nonunit_iff {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B : Set X.obj.left) (Z : LocalFlattener f) (i : ℕ)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B (i + 1)))
    (x : X.obj.left) (hxV : x ∈ Z.V) :
    (intrinsicCentreStalkRange X.obj.left
      (closure ((strata f B (i + 1) ∩ Z.V) \ Z.support)) x ⊔ Z.H x) ≠ ⊤ ↔
      x ∈ stratumBoundary f B Z.V Z.support i := by
  let G := closure ((strata f B (i + 1) ∩ Z.V) \ Z.support)
  have hG : IsLocallyAnalyticOn X Z.V G := closure_locallyAnalytic f B Z i hS
  change intrinsicCentreStalkRange X.obj.left G x ⊔ Z.H x ≠ ⊤ ↔ x ∈ G ∧ x ∈ Z.support
  constructor
  · intro h
    have hxG : x ∈ G := by
      by_contra hn
      have ht := intrinsicCentreStalkRange_eq_top_of_not_mem X Z.V G Z.isOpen hG x hxV hn
      exact h (by rw [ht, top_sup_eq])
    have hxH : Z.H x ≠ ⊤ := fun ht => h (by rw [ht, sup_top_eq])
    exact ⟨hxG,hxV,hxH⟩
  · rintro ⟨hxG,hxV',hxH⟩ htop
    have hle : intrinsicCentreStalkRange X.obj.left G x ⊔ Z.H x ≤
        IsLocalRing.maximalIdeal (X.obj.left.presheaf.stalk x) :=
      sup_le (intrinsicCentreStalkRange_le_maximalIdeal _ _ _ hxG) (IsLocalRing.le_maximalIdeal hxH)
    rw [htop] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal (X.obj.left.presheaf.stalk x)).ne_top (top_le_iff.mp hle)

/-- Near each actual tracked boundary point, the auxiliary scheme-boundary
  ideal has nonunit locus contained in the source higher-component set. -/
theorem eventually_auxBoundary_support_subset_cset {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B : Set X.obj.left) {q : ℕ} (Z : Fin q → LocalFlattener f)
    (Zaux : LocalFlattener f) (i : ℕ)
    (hS : ∀ p, IsLocallyAnalyticOn X (Z p).V (strata f B (i + 1)))
    (N : ℕ) (hN : strata f B N = ∅)
    (hcover : ∀ j x, x ∈ strata f B j → ∃ C, IsStratumComponent f B j C ∧ x ∈ C)
    (hC : Cset f B (fun p => (Z p).support) (i + 1) ⊆ Zaux.support)
    (p : Fin q) (x : X.obj.left) (hx : x ∈ stratumBoundary f B (Z p).V (Z p).support i) :
    ∀ᶠ y in 𝓝 x,
      (intrinsicCentreStalkRange X.obj.left
        (closure ((strata f B (i + 1) ∩ Zaux.V) \ Zaux.support)) y ⊔ Zaux.H y) ≠ ⊤ →
        y ∈ Cset f B (fun p => (Z p).support) (i + 1) := by
  have hEq := tracked_boundary_scheme_agrees f B Z Zaux i hS N hN hcover hC p x hx
  have hV := (Z p).isOpen.mem_nhds hx.2.1
  filter_upwards [hEq,hV] with y hyEq hyV hyNonunit
  have hyNonunit' : (intrinsicCentreStalkRange X.obj.left
      (closure ((strata f B (i + 1) ∩ (Z p).V) \ (Z p).support)) y ⊔ (Z p).H y) ≠ ⊤ := by
    rw [← hyEq]
    exact hyNonunit
  have hyE := (schemeBoundary_nonunit_iff f B (Z p) i (hS p) y hyV).mp hyNonunit'
  exact tracked_boundary_subset_cset f B Z i hS N hN hcover p hyE

end Hironaka.Analytic.Unibranch.HironakaG10BoundarySupportContainment
