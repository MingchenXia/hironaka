import Hironaka.Resolution.HironakaG8InitialBoundaryAtlasMarkOne

/-! A locally finite cover by literal finite histories of one physical projection. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8LocallyFinitePhysicalCharts
noncomputable section

open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass
  HironakaG8NoncompactInitialBoundaryAtlas HironakaG8NoncompactInitialBoundaryMembers
  HironakaG8InitialBoundaryAtlasMarkOne HironakaG8SurfaceLimitEndpoint
  HironakaEmbeddedAnalytic HironakaResolutionSpaceLocal NormalCrossings
  HironakaG3REmbeddedGlobalSNC HironakaG4SharpTerminalAtlas
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation

/-- Compact-exhaustion shells cover the base and meet only finitely many
members near each point. Every member fits inside a compact window. -/
theorem exists_locally_finite_compact_enclosed_cover
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SigmaCompactSpace X] :
    ∃ (U : ℕ → Opens X) (K : ℕ → Set X), (∀ k, IsCompact (K k) ∧ (U k : Set X) ⊆ K k) ∧
      (∀ x, ∃ k, x ∈ U k) ∧ LocallyFinite (fun k => (U k : Set X)) := by
  classical
  let L := CompactExhaustion.choice X
  let F : ℕ → Set X
    | 0 => ∅
    | k+1 => L k
  have hF (k : ℕ) : IsClosed (F k) := by
    cases k with
    | zero => exact isClosed_empty
    | succ k => exact (L.isCompact k).isClosed
  let U (k : ℕ) : Opens X := ⟨interior (L (k+1)) \ F k, isOpen_interior.sdiff (hF k)⟩
  refine ⟨U,(fun k => L (k+1)),(fun k => ⟨L.isCompact _,sdiff_subset.trans interior_subset⟩),?_,?_⟩
  · intro x
    have hx : ∃ k, x ∈ interior (L (k+1)) := by
      obtain ⟨k,hk⟩ := L.exists_mem x
      exact ⟨k,L.subset_interior_succ k hk⟩
    refine ⟨Nat.find hx,Nat.find_spec hx,?_⟩
    intro h
    cases hk : Nat.find hx with
    | zero => exact (show x ∉ F 0 from notMem_empty x) (hk ▸ h)
    | succ k =>
      have hFk : x ∈ F (k+1) := hk ▸ h
      have hkx : x ∈ interior (L (k+1)) := L.subset_interior_succ k hFk
      have := Nat.find_min' hx hkx
      omega
  · intro x
    obtain ⟨k,hk⟩ := L.exists_mem x
    let V := interior (L (k+1))
    refine ⟨V,isOpen_interior.mem_nhds (L.subset_interior_succ k hk),?_⟩
    refine (Set.finite_lt_nat (k+2)).subset ?_
    intro i hi
    by_contra h
    change ¬ i < k+2 at h
    have hki : k+2 ≤ i := by omega
    obtain ⟨y,hyU,hyV⟩ := hi
    cases i with
    | zero => omega
    | succ i =>
      exact hyU.2 (L.subset (by omega : k+1 ≤ i) (interior_subset hyV))

/-- One proper projection has a countable, locally finite physical chart cover
on both source and base, retaining exact original TEST on each chart. -/
theorem exists_locally_finite_initial_boundary_markOne_physical_cover
    {m : ℕ} {X : CMfd.{0} (m+1)} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := m+1) W) {E : List (Set X)}
    (hE : IsSNCDivisor (m+1) E) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B)) :
    ∃ (Z : CMfd.{0} (m+1)) (P : Z → X),
      IsGluedFrom (orderedInitialBoundaryClass W E) Z P ∧
      IsClosedSubmanifold (m+1) (strictTransform (m+1) P W) ∧
      IsIsomorphismOver (m+1) P (singularSet (n := m+1) W ∪ (W ∩ ⋃ B ∈ E, B))ᶜ ∧
      (∃ c : ℕ → TowerChart (orderedInitialBoundaryClass W E) Z P,
        (∀ x, ∃ k, x ∈ (c k).U) ∧ (∀ z, ∃ k, z ∈ (c k).V) ∧
        LocallyFinite (fun k => ((c k).U : Set X)) ∧
        LocallyFinite (fun k => ((c k).V : Set Z)) ∧
        (∀ k, ∃ K : Set X, IsCompact K ∧ ((c k).U : Set X) ⊆ K) ∧
        ∀ k, InitialBoundaryChartMarkOne (c k)) ∧
      ∃ Ex : SNCExhaustion Z,
        (∀ k, ∃ c : TowerChart (orderedInitialBoundaryClass W E) Z P,
          Ex.W k = c.V ∧ Ex.B k = fullChartBoundary c E) ∧
        let B : {D : Set Z // Ex.IsGlobalMember D} → Set Z := Subtype.val
        IsLocallyFiniteSNCDivisor (m+1) B ∧ (∀ j, (B j).Nonempty) ∧
        HasNormalCrossingsWithBoundary (strictTransform (m+1) P W) B := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel (m+1)) X
  obtain ⟨U,K,hK,hCover,hLF⟩ := exists_locally_finite_compact_enclosed_cover (X := X)
  obtain ⟨Z,P,hGlue,hWindows,hRead,hSmooth,hIso,hMembers⟩ :=
    exists_locally_finite_initial_boundary_original_markOne_atlas hW hE hDense
  choose c hc using fun k => hWindows (U k) (K k) (hK k).1 (hK k).2
  have hBase : LocallyFinite (fun k => ((c k).U : Set X)) := by
    simpa only [hc] using hLF
  have hTarget : LocallyFinite (fun k => ((c k).V : Set Z)) := by
    simpa only [TowerChart.V_eq] using hBase.preimage_continuous hGlue.1.continuous
  refine ⟨Z,P,hGlue,hSmooth,hIso,⟨c,?_,?_,hBase,hTarget,?_,fun k => hRead (c k)⟩,hMembers⟩
  · intro x
    simpa only [hc] using hCover x
  · intro z
    obtain ⟨k,hk⟩ := hCover (P z)
    exact ⟨k,(c k).mem_V (by simpa only [hc] using hk)⟩
  · intro k
    exact ⟨K k,(hK k).1,by simpa only [hc] using (hK k).2⟩

end
end Hironaka.HironakaG8LocallyFinitePhysicalCharts
