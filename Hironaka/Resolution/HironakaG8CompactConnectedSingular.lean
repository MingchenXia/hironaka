import Hironaka.MarkedIdeal.CodimOneSupport
import Hironaka.Resolution.HironakaResolutionSpaceSingular
import Hironaka.Resolution.HironakaG8DiscreteOriginalSingular

/-! Connected components of an analytic set form a locally finite family. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CompactConnectedSingular
noncomputable section
open GlobalComponents

def componentCarriers {M : Type*} [TopologicalSpace M] (A : Set M) : Set (Set M) :=
  (fun x => connectedComponentIn A x) '' A

theorem iUnion_componentCarriers {M : Type*} [TopologicalSpace M] (A : Set M) :
    (⋃ C : componentCarriers A, (C : Set M)) = A := by
  ext x
  constructor
  · intro hx
    obtain ⟨C,hxC⟩ := mem_iUnion.mp hx
    obtain ⟨y,_,hy⟩ := C.property
    rw [← hy] at hxC
    exact connectedComponentIn_subset _ _ hxC
  · intro hx
    exact mem_iUnion.mpr ⟨⟨connectedComponentIn A x,⟨x,hx,rfl⟩⟩,mem_connectedComponentIn hx⟩

theorem disjoint_componentCarriers {M : Type*} [TopologicalSpace M] (A : Set M) :
    Pairwise (fun C D : componentCarriers A => Disjoint (C : Set M) D) := by
  intro C D hCD
  apply Set.disjoint_left.mpr
  intro x hxC hxD
  obtain ⟨y,_,hy⟩ := C.property
  obtain ⟨z,_,hz⟩ := D.property
  rw [← hy] at hxC
  rw [← hz] at hxD
  exact hCD (Subtype.ext (hy.symm.trans ((connectedComponentIn_eq hxC).trans
    ((connectedComponentIn_eq hxD).symm.trans hz))))

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem locallyFinite_componentCarriers {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) :
    LocallyFinite (fun C : componentCarriers A => (C : Set M)) := by
  classical
  let I := globalComponents (n := n) A
  have hNon (B : I) : (B : Set M).Nonempty := by
    obtain ⟨c,hc,hB⟩ := B.property
    rw [hB]
    exact ⟨c,subset_closure (mem_connectedComponentIn hc)⟩
  let f (B : I) : componentCarriers A :=
    ⟨connectedComponentIn A (hNon B).choose,
     ⟨(hNon B).choose,subset_of_mem_globalComponents hA B.property (hNon B).choose_spec,rfl⟩⟩
  have hSub (B : I) : (B : Set M) ⊆ f B :=
    IsPreconnected.subset_connectedComponentIn
      (CodimOneSupport.isPreconnected_of_isComplexAnalyticallyIrreducible
      (isComplexAnalyticallyIrreducible_of_mem_globalComponents hA B.property))
      (hNon B).choose_spec (subset_of_mem_globalComponents hA B.property)
  intro x
  obtain ⟨s,hs,hFin⟩ := locallyFinite_globalComponents hA x
  refine ⟨s,hs,(hFin.image f).subset ?_⟩
  rintro C ⟨y,hyC,hys⟩
  have hyA : y ∈ ⋃₀ globalComponents (n := n) A := by
    rw [sUnion_globalComponents hA]
    exact iUnion_componentCarriers A ▸ mem_iUnion.mpr ⟨C,hyC⟩
  obtain ⟨B,hB,hyB⟩ := mem_sUnion.mp hyA
  refine ⟨⟨B,hB⟩,⟨y,hyB,hys⟩,?_⟩
  obtain ⟨z,_,hz⟩ := C.property
  change y ∈ (C : Set M) at hyC
  rw [← hz] at hyC
  exact Subtype.ext ((connectedComponentIn_eq (hSub ⟨B,hB⟩ hyB)).trans
    ((connectedComponentIn_eq hyC).symm.trans hz))

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq HomogenizedGlueingTower HironakaG8FiniteNativeTestServing
  HironakaUniformHistoricalSuccessorOriginalRegular HironakaEmbeddedAnalytic
  HironakaResolutionSpace NormalCrossings NormalCrossingsInvariance
  HironakaG8GlobalNativeTestAssembly HironakaG8DiscreteOriginalSingular
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaActualLocallyFiniteHistoryOverlap
  HironakaLocallyFiniteResolutionSequence HironakaActualLimitCarrierGeometry
  HironakaG4CompactComponentLimit HironakaActualLimitProtectedOpen HironakaResolutionSpaceLocal
  RestrictEmptyTower HironakaAdmissibleSequence

attribute [local instance] limitChartedSpace
local instance {d : ℕ} {X : CMfd.{0} d} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold d (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

/-- Compact connected components of the original singular set suffice for a
finite original TEST or a locally finite growing original TEST. -/
theorem compact_connected_original_singular_finite_or_proper_limit {d : ℕ} {X : CMfd.{0} (d+1)}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := d+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (d+1) E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hCompact : ∀ x ∈ singularSet (n := d+1) W,
      IsCompact (connectedComponentIn (singularSet (n := d+1) W) x)) :
    (∃ (Y : CMfd.{0} (d+1)) (T : BlowupTower X Y),
      NativeTestState W E T ∧ IsClosedSubmanifold (d+1) (strictTransform (d+1) T.proj W) ∧
      IsProperMap T.proj ∧ Function.Surjective T.proj ∧
      IsIsomorphismOver (d+1) T.proj (singularSet (n := d+1) W)ᶜ) ∨
    ∃ (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)),
      (∀ i, NativeTestState W E (s.stage i).2) ∧
      (∀ x : X, ∃ (V : Opens X) (N : ℕ), x ∈ V ∧ ∀ r,
        ResolutionInvariantExt.IsEmptyTower
          (restrict (openPreimage (s.stage N).2 V) (tailTower s N r))) ∧
      IsClosedSubmanifold (d+1) (limitStrictTransform s hLF W) ∧
      limitStrictTransform s hLF W = strictTransform (d+1) (gluedProjection s hLF) W ∧
      IsProperMap (gluedProjection s hLF) ∧ Function.Surjective (gluedProjection s hLF) ∧
      IsIsomorphismOver (d+1) (gluedProjection s hLF) (singularSet (n := d+1) W)ᶜ ∧
      ContMDiff 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel (d+1)) ∞ (gluedProjection s hLF) := by
  let A := singularSet (n := d+1) W
  have hA : IsComplexAnalyticSubset (n := d+1) A :=
    HironakaResolutionSpaceSingular.isComplexAnalyticSubset_singularSet hW
  apply compact_pieces_original_singular_finite_or_proper_limit W hW E hE hDense
    (fun C : componentCarriers A => (C : Set X))
  · intro C
    obtain ⟨x,hx,hC⟩ := C.property
    rw [← hC]
    exact hCompact x hx
  · exact locallyFinite_componentCarriers hA
  · exact disjoint_componentCarriers A
  · exact (iUnion_componentCarriers A).symm

end
end Hironaka.HironakaG8CompactConnectedSingular
