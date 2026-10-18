/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveStrictSetOverlaps

/-! Actual strict sets descend using the true gluing relation; closedness
and precise local pullbacks precede global smoothness or divisor descent. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveGluedStrictSets
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveGluedProjection HironakaSharpActualCurveStrictSetOverlaps
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveLocalRangeBiholomorphism
  HironakaSharpActualCurveOriginalRecipeAtlas MemberInterTowerAlong
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

/-- The actual global subset is formed from genuine local strict transforms. -/
def gluedStrictSet (A : ActualEndpointHistories X J) (B : Set X) : Set (endpointGluedSpace A) :=
  ⋃ i, endpointLocalInclusion A i '' localStrictSet A B i

/-- Equality of actual included points gives a TRUE overlap representative;
the OLD transition transports membership before the exact local dictionary. -/
theorem mem_gluedStrictSet_iff (A : ActualEndpointHistories X J) (B : Set X)
    (hB : IsClosed B) (i : J) (z : A.finalSpace i) :
    endpointLocalInclusion A i z ∈ gluedStrictSet A B ↔ z ∈ localStrictSet A B i := by
  constructor
  · intro hz
    obtain ⟨j,w,hw,heq⟩ := mem_iUnion.mp hz
    obtain ⟨q,hqSource,hqTarget⟩ := ((endpointGlueData A).ι_eq_iff_rel j i w z).mp heq
    change q.val=w at hqSource
    change (transition A j i q).val=z at hqTarget
    have hs : q.val ∈ localStrictSet A B j := by rw [hqSource];exact hw
    have ht := (transition_strictSet A B hB j i q).mpr hs
    rwa [hqTarget] at ht
  · intro hz
    exact mem_iUnion.mpr ⟨i,z,hz,rfl⟩

theorem preimage_gluedStrictSet (A : ActualEndpointHistories X J) (B : Set X)
    (hB : IsClosed B) (i : J) :
    endpointLocalInclusion A i ⁻¹' gluedStrictSet A B=localStrictSet A B i := by
  ext z
  exact mem_gluedStrictSet_iff A B hB i z

/-- Closedness follows from the ACTUAL quotient topology and exact whole
local pullbacks, not from a supplied global set or closedness certificate. -/
theorem isClosed_gluedStrictSet (A : ActualEndpointHistories X J) (B : Set X)
    (hB : IsClosed B) : IsClosed (gluedStrictSet A B) := by
  rw [← isOpen_compl_iff]
  apply ((endpointGlueData A).isOpen_iff _).mpr
  intro i
  change IsOpen (endpointLocalInclusion A i ⁻¹' (gluedStrictSet A B)ᶜ)
  rw [preimage_compl,preimage_gluedStrictSet A B hB i]
  exact (isClosed_strictAlong _ (hB.preimage continuous_subtype_val)).isOpen_compl

/-- Genuine finite-history strict containment supplies the entire actual
projection containment; no surjectivity onto the original closed set is asserted. -/
theorem gluedStrictSet_subset_preimage (A : ActualEndpointHistories X J) (B : Set X)
    (hB : IsClosed B) : gluedStrictSet A B ⊆ (gluedProjection A) ⁻¹' B := by
  intro q hq
  obtain ⟨i,z,hz,rfl⟩ := mem_iUnion.mp hq
  change gluedProjection A (endpointLocalInclusion A i z) ∈ B
  rw [gluedProjection_local_full A i z]
  exact strictAlong_subset_preimage _ (hB.preimage continuous_subtype_val) hz

/-- The actual biholomorphism has the OLD inclusion as its whole point map. -/
theorem localBiholomorphism_preimage_gluedStrictSet (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (B : Set X) (hB : IsClosed B) (i : J) :
    (localBiholomorphism A hc i) ⁻¹'
      ((Subtype.val : localRangeOpen A hc i → endpointManifold A hc) ⁻¹' gluedStrictSet A B)=
        localStrictSet A B i := by
  ext z
  exact mem_gluedStrictSet_iff A B hB i z

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)

/-- ONLY the original curve inputs internally construct all local histories,
actual overlap maps, true global manifold and this genuine global subset. -/
def originalGluedStrictSet (B : Set X) : Set (originalEndpointManifold hn hW hE hdense hr) :=
  gluedStrictSet (originalEndpointHistories hn hW hE hdense hr) B

theorem isClosed_originalGluedStrictSet (B : Set X) (hB : IsClosed B) :
    IsClosed (originalGluedStrictSet hn hW hE hdense hr B) :=
  isClosed_gluedStrictSet _ B hB

theorem originalLocalBiholomorphism_preimage_gluedStrictSet (B : Set X)
    (hB : IsClosed B) (i : X) :
    (originalLocalBiholomorphism hn hW hE hdense hr i) ⁻¹'
      ((Subtype.val : localRangeOpen (originalEndpointHistories hn hW hE hdense hr)
        (originalEndpointHistories_cover hn hW hE hdense hr) i →
          originalEndpointManifold hn hW hE hdense hr) ⁻¹'
        originalGluedStrictSet hn hW hE hdense hr B)=
      localStrictSet (originalEndpointHistories hn hW hE hdense hr) B i :=
  localBiholomorphism_preimage_gluedStrictSet _ _ B hB i

end OriginalInput

end
end Hironaka.HironakaSharpActualCurveGluedStrictSets
