import Hironaka.Analytic.Unibranch.HironakaG10PNSourceNoether
import Hironaka.Analytic.Unibranch.HironakaG10LocalIntrinsicIdeal
import Hironaka.Analytic.Unibranch.HironakaG10VanishingStalkIdentity

/-! # Noether stationarity for Hironaka's actual analytic strata -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry Opposite
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10AnalyticStrataNoether
open Hironaka HironakaG10PNIdealFamily
  HironakaIntrinsicReducedCentreOpenPullback
open Hironaka.Analytic.Unibranch.HironakaG10PNSourceNoether
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
  Hironaka.Analytic.Unibranch.HironakaG10LocalIntrinsicIdeal
  Hironaka.Analytic.Unibranch.HironakaG10VanishingStalkIdentity
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata

noncomputable section

/-- Inclusion reverses the actual intrinsic reduced vanishing stalk ideals. -/
theorem intrinsicCentreStalkRange_anti {X : LocallyRingedSpace.{0}}
    {A B : Set X} (hAB : A ⊆ B) (x : X) :
    intrinsicCentreStalkRange X B x ≤ intrinsicCentreStalkRange X A x := by
  rw [← vanishingIdealAt_eq_intrinsicCentreStalkRange,
    ← vanishingIdealAt_eq_intrinsicCentreStalkRange]
  apply Ideal.span_mono
  rintro g ⟨U,hxU,t,ht,hvan⟩
  exact ⟨U,hxU,t,ht,fun y hy hyA => hvan y hy (hAB hyA)⟩

/-- An actual analytic subset is exactly the nonunit locus of its intrinsic
  reduced vanishing stalk family. -/
theorem analytic_intrinsic_nonunit_iff (X : SourceReducedComplexSpace)
    (A : Set X.obj.left) (hA : X.IsAnalyticSubset A) (x : X.obj.left) :
    intrinsicCentreStalkRange X.obj.left A x ≠ ⊤ ↔ x ∈ A := by
  constructor
  · intro h
    by_contra hx
    exact h (intrinsicCentreStalkRange_eq_top_of_not_mem X univ A isOpen_univ
      (locallyAnalytic_of_analytic hA univ) x (mem_univ x) hx)
  · intro hx htop
    have hle := intrinsicCentreStalkRange_le_maximalIdeal X.obj.left A x hx
    rw [htop] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal (X.obj.left.presheaf.stalk x)).ne_top
      (top_le_iff.mp hle)

/-- A decreasing sequence of actual analytic subsets stabilizes after
  intersecting with any compact set. -/
theorem analytic_descending_stationary_on_compact (X : SourceReducedComplexSpace)
    (A : ℕ → Set X.obj.left) (hA : ∀ n, X.IsAnalyticSubset (A n))
    (hdesc : ∀ n, A (n + 1) ⊆ A n) (K : Set X.obj.left) (hK : IsCompact K) :
    ∃ N : ℕ, ∀ m, N ≤ m → K ∩ A m = K ∩ A N := by
  let J : ℕ → ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x) :=
    fun n => intrinsicCentreStalkRange X.obj.left (A n)
  have hJ : IsAscending X.obj.left J := by
    intro n x
    exact intrinsicCentreStalkRange_anti (hdesc n) x
  have hfg : ∀ n, IsLocallyFinitelyGenerated X.obj.left (J n) := by
    intro n x
    have h := local_intrinsicCentreStalkRange_finitelyGenerated X univ (A n)
      (locallyAnalytic_of_analytic (hA n) univ)
    obtain ⟨U,hxU,r,s,hs⟩ := h x (mem_univ x)
    exact ⟨U,hxU,r,s,fun y hy => hs y hy (mem_univ y)⟩
  obtain ⟨N,W,hKW,hW⟩ := exists_stationary_nhds X hJ hfg K hK
  refine ⟨N,fun m hm => ?_⟩
  ext x
  by_cases hxK : x ∈ K
  · have hEq : J m x = J N x := hW m hm x (hKW hxK)
    simp only [mem_inter_iff,hxK,true_and]
    rw [← analytic_intrinsic_nonunit_iff X _ (hA m) x,
      ← analytic_intrinsic_nonunit_iff X _ (hA N) x]
    change J m x ≠ ⊤ ↔ J N x ≠ ⊤
    rw [hEq]
  · simp [hxK]

/-- If the actual relative nonflat strata are analytic, their intersections
  with any compact set eventually stabilize. This proves the Noether part of
  finite depth without assuming the strata are strictly decreasing. -/
theorem analytic_strata_stationary_on_compact {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B : Set X.obj.left)
    (hA : ∀ n, X.IsAnalyticSubset (strata f B n))
    (K : Set X.obj.left) (hK : IsCompact K) :
    ∃ N : ℕ, ∀ m, N ≤ m → K ∩ strata f B m = K ∩ strata f B N :=
  analytic_descending_stationary_on_compact X (strata f B) hA (strata_succ_subset f B) K hK

/-- If a nonempty analytic stratum cannot equal its relative nonflat locus,
  compactness and the proven Noether stationarity force finite depth. -/
theorem exists_empty_stratum_of_analytic_no_fixed {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B : Set X.obj.left)
    (hA : ∀ n, X.IsAnalyticSubset (strata f B n))
    (hproper : ∀ n, (strata f B n).Nonempty → strata f B (n + 1) ≠ strata f B n) :
    ∃ N, strata f B N = ∅ := by
  obtain ⟨N,hN⟩ := analytic_strata_stationary_on_compact f B hA univ isCompact_univ
  have heq : strata f B (N + 1) = strata f B N := by
    simpa only [univ_inter] using hN (N + 1) (Nat.le_succ N)
  by_contra h
  push Not at h
  exact hproper N (h N) heq

end
end Hironaka.Analytic.Unibranch.HironakaG10AnalyticStrataNoether
