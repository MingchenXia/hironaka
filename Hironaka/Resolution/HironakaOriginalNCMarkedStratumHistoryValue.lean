import Hironaka.Resolution.HironakaOriginalNCMarkedStratum
import Hironaka.Resolution.HironakaOriginalNCOldStratumStrictEquality
import Hironaka.Resolution.HironakaOriginalNCCausalHistoryValue

/-!
# The NEW proper-carrier marked-stratum history value

The actual old-count chronology and literal birth opens/heads/tails are
reused. The auxiliary marked datum is NEW: the genuine marked sum on the
original native carrier with the ambient stratum equations marked one.
It is not the accepted ambient coefficient/remainder causal value.

Every ordinary native test history carrying all original branch tests
internally supplies the fresh auxiliary invariant domain. Auxiliary
canonicality of the actual suffix is NOT an input or a conclusion here;
the unconditional NEW-value joint interpreter is the subsequent producer.
Mathematics first: the implementation mathematical-delta.tex, with the
published ee882850 research proposal left unchanged. No new blueprint
credit or kernel-check claim is made for these definitions/parent adapters.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalNCMarkedStratumHistoryValue

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealOperationsAlong.MarkedIdeal GermIdealOrder
  HironakaOriginalNCMarkedStratum HironakaOriginalNCOldStratumStrictEquality
  HironakaOriginalNCCausalHistoryValue HironakaOriginalNCCountHistory
  HironakaOriginalOldBranchOpenHistory
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
open ResolutionInvariantSpec (IsInvDomain)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The SAME actual birth parent, stratum and E; only the genuine marked-sum auxiliary is new. -/
def markedStratumBirth (M : MarkedIdeal n X) (H : Set X)
    (T : BlowupTower X Y) (y : Y) : MarkedIdeal n (causalBirthOpen H T y) :=
  markedStratum (X := CMfd.of (n := n) (causalBirthOpen H T y))
    (causalBirthParent M H T y) (causalBirthStratum H T y)

/-- The new single causal value, defined before any resolving future is chosen. -/
def markedStratumHistoryValue (M : MarkedIdeal n X) (H : Set X)
    (T : BlowupTower X Y) (y : Y) : ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) :=
  toLex (oldCount H T y,
    if causalBirthPoint H T y ∈
        (geoTransformAlong (markedStratumBirth M H T y) (causalBirthTail H T y)).cosupp then
      ((CanonicalCentres.canonicalInvariant n).inv (markedStratumBirth M H T y)
        (causalBirthTail H T y) (causalBirthPoint H T y) : WithBot (CanonicalCentres.ValTy n))
    else ⊥)

/-- ANY real native parent test/history supplies the actual fresh auxiliary domain.
No desired intersection smoothness, future lower test or future canonicality is a premise. -/
theorem markedStratumBirth_domain {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (y : Y) :
    IsInvDomain k (markedStratumBirth M H T y) ∧
      (markedStratumBirth M H T y).N = (causalBirthParent M H T y).N ∧
      (markedStratumBirth M H T y).E = (causalBirthParent M H T y).E ∧
      (markedStratumBirth M H T y).d = (causalBirthParent M H T y).d := by
  let j := T.length - birthYear H T y
  let K := head T j
  let W := causalBirthOpen H T y
  let MW := causalBirthParent M H T y
  let q := oldCount H T y
  have hK : IsGeoTestTower M K := ((isGeoTestTower_iff_head_tail M T j).mp hT).1
  have hKHistory : IsOriginalBranchTestTower M H K := originalBranchHistory_head M T hHistory j
  have hcK := (current_old_strata_eq_strict M h K hK hKHistory).1
  have hW := boundaryAdapted_open W hcK
  have hKDomain := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM K hK
  have hMW : IsInvDomain k MW := InvDomainTowerAlong.isInvDomain_pullback_val W hKDomain
  have hCount (z : W) :
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z = oldCount H K z.val :=
    (branchMultiplicity_open W (isNormalCrossingsCarrier_of_boundaryAdapted hcK)
      (isNormalCrossingsCarrier_of_boundaryAdapted hW) z).trans
      (oldCount_eq K (isNormalCrossingsCarrier_of_boundaryAdapted hcK) z.val).symm
  have hBound : ∀ z : W,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z ≤ q := by
    intro z
    exact (hCount z).trans_le z.property
  have hZ : IsClosedSubmanifold n (causalBirthStratum H T y) := by
    have hHighest := isClosedSubmanifold_highest_superlevel
      (isNormalCrossingsCarrier_of_boundaryAdapted hW) hBound
    have hSet : causalBirthStratum H T y =
        {z : W | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z} := by
      ext z
      change (q ≤ oldCount H K z.val) ↔
        q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z
      rw [hCount z]
    exact hSet.symm ▸ hHighest
  refine ⟨markedStratum_isInvDomain (X := CMfd.of (n := n) W) MW hMW hZ, rfl, rfl, ?_⟩
  change MW.d * 1 = MW.d
  exact Nat.mul_one MW.d

/-- The literal count-zero auxiliary is whole restricted-equivalent to its SAME native parent. -/
theorem markedStratumBirth_restrictEquiv_parent_of_zero {k : ℕ}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (H : Set X) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (y : Y) (hq : oldCount H T y = 0) :
    RestrictEquiv (markedStratumBirth M H T y) (causalBirthParent M H T y) := by
  let j := T.length - birthYear H T y
  let W := causalBirthOpen H T y
  have hK := ((isGeoTestTower_iff_head_tail M T j).mp hT).1
  have hKD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM (head T j) hK
  have hMW : IsInvDomain k (causalBirthParent M H T y) :=
    InvDomainTowerAlong.isInvDomain_pullback_val W hKD
  have hFull : causalBirthStratum H T y = univ := by
    ext z
    simp only [causalBirthStratum, hq, Nat.zero_le, Set.mem_ofPred_eq, Set.mem_univ]
  exact markedStratum_restrictEquiv_of_carrier_subset (X := CMfd.of (n := n) W)
    (causalBirthParent M H T y) hMW.isWellFormed.isCoherent hMW.one_le_d
    (causalBirthStratum H T y) (by
      intro z _hz
      rw [hFull]
      exact Set.mem_univ z)

end

end Hironaka.HironakaOriginalNCMarkedStratumHistoryValue
