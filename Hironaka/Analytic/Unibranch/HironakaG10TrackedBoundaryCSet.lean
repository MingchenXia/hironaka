import Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryNextStratum
import Hironaka.Analytic.Unibranch.HironakaG10SourceCSet

/-! # Tracked boundaries lie in Hironaka's higher-component set -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryCSet

open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary
  Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryNextStratum
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet

/-- A finite descending filtration places every point in one of its
  successive differences at or above any given level. -/
theorem exists_last_stratum {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (B : Set X.obj.left) (N : ℕ) (hN : strata f B N = ∅)
    (k : ℕ) {x : X.obj.left} (hx : x ∈ strata f B k) :
    ∃ j, k ≤ j ∧ x ∈ strata f B j ∧ x ∉ strata f B (j + 1) := by
  classical
  have hanti : Antitone (strata f B) := antitone_nat_of_succ_le (strata_succ_subset f B)
  have hex : ∃ m : ℕ, x ∉ strata f B (k + m) := by
    refine ⟨N,?_⟩
    intro hmem
    have : x ∈ strata f B N := hanti (Nat.le_add_left N k) hmem
    rw [hN] at this
    exact this
  let m := Nat.find hex
  have hm : m ≠ 0 := by
    intro hm0
    have hnot := Nat.find_spec hex
    change x ∉ strata f B (k + m) at hnot
    rw [hm0, Nat.add_zero] at hnot
    exact hnot hx
  obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hprev : x ∈ strata f B (k + r) := by
    by_contra hnot
    have hlt : r < m := by rw [hr]; exact Nat.lt_succ_self _
    exact (not_le_of_gt hlt) (Nat.find_min' hex hnot)
  have hnext : x ∉ strata f B (k + r + 1) := by
    have h := Nat.find_spec hex
    change x ∉ strata f B (k + m) at h
    simpa only [hr, Nat.add_succ] using h
  exact ⟨k+r, Nat.le_add_right k r, hprev, hnext⟩

/-- The support of every actual tracked boundary is contained in the actual
  source `C_{i+1}`. Finite depth and coverage by native irreducible components
  are explicit Frisch/component inputs. -/
theorem tracked_boundary_subset_cset {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B : Set X.obj.left) {q : ℕ} (Z : Fin q → LocalFlattener f) (i : ℕ)
    (hS : ∀ p, IsLocallyAnalyticOn X (Z p).V (strata f B (i + 1)))
    (N : ℕ) (hN : strata f B N = ∅)
    (hcover : ∀ j x, x ∈ strata f B j →
      ∃ C, IsStratumComponent f B j C ∧ x ∈ C) :
    ∀ p, stratumBoundary f B (Z p).V (Z p).support i ⊆
      Cset f B (fun p => (Z p).support) (i + 1) := by
  intro p x hx
  have hxnext := tracked_boundary_subset_next_stratum f B (Z p) i (hS p) hx
  obtain ⟨j,hj,hxj,hxnext'⟩ := exists_last_stratum f B N hN (i + 2) hxnext
  obtain ⟨C,hC,hxC⟩ := hcover j x hxj
  have hji : i + 1 < j := lt_of_lt_of_le (Nat.lt_succ_self (i + 1)) hj
  have hselected : (j,C) ∈ selectedHigherComponents f B (fun p => (Z p).support) (i + 1) :=
    ⟨hji,hC,p,⟨x,⟨hxC,hxnext'⟩,hx.2⟩⟩
  exact Set.mem_iUnion.mpr ⟨(j,C),Set.mem_iUnion.mpr ⟨hselected,hxC⟩⟩

end Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryCSet
