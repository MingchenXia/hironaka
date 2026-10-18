/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveBirthBoundaryOverlaps

/-! Actual original-only global birth-indexed boundary subsets, with exact
local pullbacks and genuine local finiteness from variable chart cutoffs. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveLocallyFiniteBoundary
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveOriginalRecipeAtlas
  HironakaSharpActualCurveBirthBoundaryOverlaps HironakaSharpActualCurveGlobalManifold
  HironakaSharpActualCurveLocalRangeBiholomorphism HironakaSharpActualCurveGluedStrictSets
  NormalCrossings
variable {n : ℕ} {X : CMfd.{u} n}
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)

/-- Actual global subsets from the SAME original-only atlas. Every natural
position remains present; there is no supplied global family or comparison. -/
def originalGluedBoundaryReadout (k : ℕ) : Set (originalEndpointManifold hn hW hE hdense hr) :=
  ⋃ i,endpointLocalInclusion (originalEndpointHistories hn hW hE hdense hr) i ''
    localBoundaryReadout (originalEndpointHistories hn hW hE hdense hr) E i k

/-- A genuine quotient representative and OLD transition precede BOTH
membership directions for the independently defined global subset. -/
theorem mem_originalGluedBoundaryReadout_iff (i : X) (k : ℕ)
    (z : (originalEndpointHistories hn hW hE hdense hr).finalSpace i) :
    endpointLocalInclusion (originalEndpointHistories hn hW hE hdense hr) i z∈
        originalGluedBoundaryReadout hn hW hE hdense hr k ↔
      z∈localBoundaryReadout (originalEndpointHistories hn hW hE hdense hr) E i k := by
  let A := originalEndpointHistories hn hW hE hdense hr
  constructor
  · intro hz
    obtain ⟨j,w,hw,heq⟩ := mem_iUnion.mp hz
    obtain ⟨q,hqSource,hqTarget⟩ := ((endpointGlueData A).ι_eq_iff_rel j i w z).mp heq
    change q.val=w at hqSource
    change (transition A j i q).val=z at hqTarget
    have hs : q.val∈localBoundaryReadout A E j k := by rw [hqSource];exact hw
    have ht := (original_transition_localBoundaryReadout hn hW hE hdense hr j i k q).mpr hs
    rwa [hqTarget] at ht
  · intro hz
    exact mem_iUnion.mpr ⟨i,z,hz,rfl⟩

theorem preimage_originalGluedBoundaryReadout (i : X) (k : ℕ) :
    endpointLocalInclusion (originalEndpointHistories hn hW hE hdense hr) i ⁻¹'
        originalGluedBoundaryReadout hn hW hE hdense hr k=
      localBoundaryReadout (originalEndpointHistories hn hW hE hdense hr) E i k := by
  ext z
  exact mem_originalGluedBoundaryReadout_iff hn hW hE hdense hr i k z

theorem originalLocalBiholomorphism_preimage_boundaryReadout (i : X) (k : ℕ) :
    (originalLocalBiholomorphism hn hW hE hdense hr i) ⁻¹'
      ((Subtype.val : localRangeOpen (originalEndpointHistories hn hW hE hdense hr)
        (originalEndpointHistories_cover hn hW hE hdense hr) i →
          originalEndpointManifold hn hW hE hdense hr) ⁻¹'
        originalGluedBoundaryReadout hn hW hE hdense hr k)=
      localBoundaryReadout (originalEndpointHistories hn hW hE hdense hr) E i k := by
  ext z
  exact mem_originalGluedBoundaryReadout_iff hn hW hE hdense hr i k z

/-- The actual quotient topology, not closedness of individual chart
images, proves genuine closedness of EACH constructed global member. -/
theorem isClosed_originalGluedBoundaryReadout (k : ℕ) :
    IsClosed (originalGluedBoundaryReadout hn hW hE hdense hr k) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  rw [←isOpen_compl_iff]
  apply ((endpointGlueData A).isOpen_iff _).mpr
  change ∀ i : X,IsOpen (endpointLocalInclusion A i ⁻¹'
    (originalGluedBoundaryReadout hn hW hE hdense hr k)ᶜ)
  intro i
  have hLocal := (original_localBoundaryReadout_isClosed hn hW hE hdense hr i k).isOpen_compl
  have hEq := congrArg (fun B : Set (A.finalSpace i) => Bᶜ)
    (preimage_originalGluedBoundaryReadout hn hW hE hdense hr i k)
  exact Eq.mpr (congrArg IsOpen hEq) hLocal

/-- The real entire range misses every later position. The cutoff uses
literal FULL history length, including every original and empty birth. -/
theorem originalBoundaryRange_disjoint (i : X) (k : ℕ)
    (hk : E.length+((originalEndpointHistories hn hW hE hdense hr).prefixTower i |>.append
      ((originalEndpointHistories hn hW hE hdense hr).tail i)).length≤k) :
    Disjoint (range (endpointLocalInclusion (originalEndpointHistories hn hW hE hdense hr) i))
      (originalGluedBoundaryReadout hn hW hE hdense hr k) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨z,rfl⟩ hq
  have hz := (mem_originalGluedBoundaryReadout_iff hn hW hE hdense hr i k z).mp hq
  rw [localBoundaryReadout_eq_empty _ E i k hk] at hz
  exact hz

/-- The ACTUAL chart cover and literal chart-dependent finite bounds
give genuine local finiteness of the independently constructed family. -/
theorem locallyFinite_originalGluedBoundaryReadout :
    LocallyFinite (originalGluedBoundaryReadout hn hW hE hdense hr) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  intro q
  obtain ⟨i,z,rfl⟩ := endpointLocalInclusion_jointly_surjective A q
  let V := range (endpointLocalInclusion A i)
  let b := E.length+((A.prefixTower i).append (A.tail i)).length
  have hV : IsOpen V := (endpointLocalInclusion_openEmbedding A i).isOpen_range
  refine ⟨V,hV.mem_nhds ⟨z,rfl⟩,?_⟩
  apply (Finset.range b).finite_toSet.subset
  intro k hk
  change k∈Finset.range b
  rw [Finset.mem_range]
  by_contra hlate
  obtain ⟨p,hp,hpV⟩ := hk
  exact Set.disjoint_left.mp
    (originalBoundaryRange_disjoint hn hW hE hdense hr i k (Nat.le_of_not_gt hlate)) hpV hp

/-- Each literal original position is EXACTLY the previous global strict
set of that SAME original member, with no quotient of indexed positions. -/
theorem originalGluedBoundaryReadout_original (k : Fin E.length) :
    originalGluedBoundaryReadout hn hW hE hdense hr k=
      originalGluedStrictSet hn hW hE hdense hr (E.get k) := by
  unfold originalGluedBoundaryReadout originalGluedStrictSet gluedStrictSet
  simp only [localBoundaryReadout_original]
  rfl

end
end Hironaka.HironakaSharpActualCurveLocallyFiniteBoundary
