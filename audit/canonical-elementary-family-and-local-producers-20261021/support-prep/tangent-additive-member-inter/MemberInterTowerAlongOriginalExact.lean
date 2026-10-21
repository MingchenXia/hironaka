import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.Invariant.MemberStrictPartitionExact

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MemberInterTowerAlong

open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupFlatCoordinates
  Hironaka.BlowupMonomialCharts
  Hironaka.BlowupLocalSurjectivity
  Hironaka.BlowupStrictSubmanifold
  Hironaka.BlowupSNCTransform Hironaka.NormalCrossings
  Hironaka.SimultaneousNormalCrossings
  Hironaka.BoundaryCount Hironaka.BlowupTowers
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.HomogenizedGlueingTower

noncomputable section

variable {n : ℕ}

/-! ### One blowup: `(N ∩ H_S)' = N' ∩ ⋂_{i ∈ S} H_i'` -/
section Tower

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)

open Classical in
/-- **A point of `N_T` lies on the strict transform of the intersection of `N` with the original
members whose strict transforms pass through it** (Step 1a: the intersection `N ∩ H_S` a point with
`s(x) = s` lies on). -/
theorem mem_strictAlong_inter_memberInter_self (h𝔪 : 𝔪.IsWellFormed) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) {z : Y} (hz : z ∈ (geoTransformAlong 𝔪 T).N) :
    z ∈ strictAlong T
      (𝔪.N ∩ memberInter 𝔪.E (Finset.univ.filter fun i => z ∈ strictAlong T (𝔪.E.get i))) := by
  rw [strictAlong_inter_memberInter 𝔪 h𝔪 _ T hT]
  exact ⟨hz, fun i hi => (Finset.mem_filter.mp hi).2⟩

end Tower

section Localise

variable {X : CMfd.{u} n}

open TopologicalSpace Hironaka.BlowupTowerTransforms
  Hironaka.CoefficientIdealRestriction

/-- **Localising the centres, several intersections at once** (Step 1a, "moving apart"): if the
centres of `T` lie in the strict transforms of `A ∪ B`, with `B` closed and disjoint from the open
set `U`, then the centres of the restriction of `T` to `U` lie in the strict transforms of `A ∩ U`. -/
theorem centresIn_restrict_of_centresIn_union (U : Opens X) {A B : Set X} (hB : IsClosed B)
    (hUB : Disjoint (U : Set X) B) : {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      CentresIn (A ∪ B) T → CentresIn ((↑) ⁻¹' A : Set U) (restrict U T)
  | _, .refl, _ => trivial
  | _, .step T C _ _, hT => by
    refine ⟨centresIn_restrict_of_centresIn_union U hB hUB T hT.1, fun p hp => ?_⟩
    rw [strictAlong_restrict U T A]
    have hpC : p.1 ∈ strictAlong T A ∪ strictAlong T B := by
      rw [← strictAlong_union]; exact hT.2 hp
    rcases hpC with h | h
    · exact h
    · exact absurd (strictAlong_subset_preimage T hB h) (Set.disjoint_left.mp hUB p.2)

end Localise

end

end Hironaka.MemberInterTowerAlong
