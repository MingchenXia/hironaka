/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.DropMembers
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Invariant.ResolutionInvariantOrder
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Invariant.UnitCosupportExact
import Hironaka.Support.RestrictedIdealExtensionExact

set_option autoImplicit false
set_option linter.unusedSectionVars false

section OriginalDropMembersContext

open Set Filter
open scoped Topology Manifold

universe u

namespace Hironaka.DropMembers

open Hironaka.BlowupSequences NormalCrossings BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupStrictSubmanifold NormalCrossingsComparison CoefficientIdealRestriction HomogenizedGlueingTower

noncomputable section

/-! ### Normal crossings and members missing the centre -/

section NC

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]

/-- **Members missing the centre do not matter for normal crossings**: if `C` has only normal crossings with `E'`, every
member of `E'` is a member of `E` and every member of `E` missing from `E'` is disjoint from `C`, then `C` has only
normal crossings with `E`. -/
theorem hasNormalCrossings_of_forall_disjoint {C : Set X} {E E' : List (Set X)}
    (h : HasNormalCrossings n C E') (hdis : ∀ H ∈ E, H ∉ E' → Disjoint C H) :
    HasNormalCrossings n C E := by
  classical
  intro x hx
  obtain ⟨S₀, S, ⟨Φ, hΦt, hΦ0, hΦA⟩, hS⟩ := h x hx
  -- a member of `E` through `x` is a member of `E'`
  have hmem : ∀ i : Fin E.length, x ∈ E.get i → E.get i ∈ E' := fun i hxi => by
    by_contra hnot
    exact Set.disjoint_left.mp (hdis _ (List.get_mem _ _) hnot) hx hxi
  set idx : Fin E.length → Option (Fin E'.length) := fun i =>
    if h : E.get i ∈ E' then some (List.mem_iff_get.mp h).choose else none
  have hidx : ∀ i (hxi : x ∈ E.get i), ∃ j, idx i = some j ∧ E'.get j = E.get i := fun i hxi => by
    have h := hmem i hxi
    exact ⟨_, dif_pos h, (List.mem_iff_get.mp h).choose_spec⟩
  refine ⟨S₀, fun i => (idx i).elim ∅ S, ⟨Φ, hΦt, hΦ0, ?_⟩, fun i hi => ?_⟩
  · rintro (_ | i) hi y hy hyΦ
    · exact hΦA none hi hy hyΦ
    · obtain ⟨j, hj, hjE⟩ := hidx i hi
      have h1 := hΦA (some j) (by simp only [Option.elim]; rw [hjE]; exact hi) hy hyΦ
      simp only [Option.elim] at h1 ⊢
      rw [hjE] at h1
      rw [hj]
      exact h1
  · obtain ⟨j, hj, hjE⟩ := hidx i hi
    simp only [hj, Option.elim]
    exact hS j (by rw [hjE]; exact hi)

end NC
end
end Hironaka.DropMembers
end OriginalDropMembersContext

section OriginalGermOrderContext

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.GermIdealOrder

open Hironaka.HolomorphicIdealSheaves
open Hironaka.IdealWeightPowers

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

variable {N : Set M} {x : M} {g : M → ℂ}

attribute [-instance] instCommCStarAlgebraComplex in
/-- A holomorphic multiple keeps the order. -/
theorem VanishesToOrderOn.mul_left {c : M → ℂ} (hc : HolomorphicAt n c x) {q : ℕ}
    (hg : VanishesToOrderOn n N x q g) : VanishesToOrderOn n N x q (fun y => c y * g y) := by
  simpa using (vanishesToOrderOn_zero (N := N) hc).mul hg

end
end Hironaka.GermIdealOrder
end OriginalGermOrderContext

section OriginalStrictSubmanifoldContext

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupStrictSubmanifold

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupFibreDirection
  NestedFlattening Hironaka.RegularPatchPullback Hironaka.RegularLocusDense

noncomputable section

variable {n : ℕ}

section Blowup

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **The strict transform of a submanifold containing the centre is a submanifold of the same
dimension**: if `N ⊇ C` is closed and regular of dimension `k_N` at each of its points, every
point of `N' = closure (π⁻¹ (N \ C))` is a regular point of `N'` of dimension `k_N`. -/
theorem regularAtDim_geoStrictTransform (hπ : IsBlowupAlong n C π) {N : Set X}
    (hNc : IsClosed N) {kN : ℕ} (hN : ∀ x ∈ N, RegularAtDim (n := n) N x kN) (hCN : C ⊆ N)
    {z : Y} (hz : z ∈ geoStrictTransform π C N) :
    RegularAtDim (n := n) (geoStrictTransform π C N) z kN := by
  by_cases hzC : π z ∈ C
  · obtain ⟨kC, hkC⟩ := hπ.1.2 (π z) hzC
    have hNz := hN (π z) (hCN hzC)
    exact regularAtDim_geoStrictTransform_of_mem hπ (le_of_regularAtDim_subset hkC hNz hCN) hkC
      hNz hCN hz
  · exact regularAtDim_geoStrictTransform_of_notMem hπ hNc hzC
      (hN (π z) (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hNc hz))

end Blowup
end
end Hironaka.BlowupStrictSubmanifold
end OriginalStrictSubmanifoldContext

section OriginalInvariantOrderContext

open Set Filter
open scoped Topology

namespace Hironaka.ResolutionInvariantOrder

section USC

variable {X Y Λ : Type*} [TopologicalSpace X] [TopologicalSpace Y]

variable {f : X → Λ} {s t : Set X}

/-- **Superlevel sets are closed** (for a closed domain). -/
theorem IsInvUSCOn.isClosed_superlevel [LinearOrder Λ] (hf : IsInvUSCOn f s) (hs : IsClosed s) (l : Λ) :
    IsClosed {x | x ∈ s ∧ l ≤ f x} := by
  refine isOpen_compl_iff.mp (isOpen_iff_mem_nhds.mpr fun y hy => ?_)
  by_cases hys : y ∈ s
  · have hlt : f y < l := lt_of_not_ge fun h => hy ⟨hys, h⟩
    filter_upwards [hf y hys] with z hz hzmem
    exact absurd ((hz hzmem.1).trans_lt hlt) (not_lt.mpr hzmem.2)
  · filter_upwards [hs.isOpen_compl.mem_nhds hys] with z hz hzmem
    exact hz hzmem.1

/-- **The maximum locus is closed** (for a closed domain): the points of `s` whose value is the maximum. -/
theorem IsInvUSCOn.isClosed_maxLocus [LinearOrder Λ] (hf : IsInvUSCOn f s) (hs : IsClosed s) {x₀ : X}
    (hmax : ∀ y ∈ s, f y ≤ f x₀) : IsClosed {x | x ∈ s ∧ f x = f x₀} := by
  have : {x | x ∈ s ∧ f x = f x₀} = {x | x ∈ s ∧ f x₀ ≤ f x} := by
    ext x
    exact ⟨fun h => ⟨h.1, h.2.ge⟩, fun h => ⟨h.1, le_antisymm (hmax x h.1) h.2⟩⟩
  rw [this]
  exact hf.isClosed_superlevel hs _

end USC
end Hironaka.ResolutionInvariantOrder
end OriginalInvariantOrderContext

section OriginalInvariantSeqContext

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ResolutionInvariantSeq

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdealBiholomorphism.MarkedIdeal
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.MarkedIdealRestrictOpen Hironaka.BlowupTowerIsomorphism
  Hironaka.ResolutionInvariantOrder Hironaka.ResolutionDriver
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
open Hironaka.ResolutionInvariantExt (IsEmptyTower)
open Hironaka.ResolutionInvariantDriver (isAdmissibleCentre_of_pullback_val_top
  maxLocus_eq_level interior_maxLocus_eq_empty isCanonical_of_isCanonicalSegment)

noncomputable section

variable {n : ℕ}

section Driver

variable {X : CMfd.{u} n}

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- The same, with the resolution a canonical segment in the sense of `hir:centre-function`. -/
theorem exists_isGeoResolution_isCanonical [CompactSpace X] (R : ResolutionInvariant.{u, v} n k Λ)
    {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsCanonical 𝔪 (R.inv 𝔪) T ∧ IsGeoResolution 𝔪 T := by
  obtain ⟨Y, T, hcan, hres⟩ := exists_isGeoResolution_isCanonicalSegment R h
  exact ⟨Y, T, isCanonical_of_isCanonicalSegment _ T hcan, hres⟩

end Driver
end
end Hironaka.ResolutionInvariantSeq
end OriginalInvariantSeqContext
