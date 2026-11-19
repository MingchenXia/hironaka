import Hironaka.Resolution.HironakaG3DisjointLocalTowerAtlas
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ComponentChartChain
noncomputable section

open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass

/-- A compact-window chart producer yields nested actual charts exhausting
the inverse image of its component window. -/
theorem component_chart_chain {n : ℕ} {X Z : CMfd.{0} n} {𝒞 K : LocalTowerClass X}
    {P : Z → X} (W : Opens X)
    (hLocal : ∀ (U : Opens X), U ≤ W → ∀ (L : Set X), IsCompact L → (U : Set X) ⊆ L →
      ∃ c : TowerChart 𝒞 Z P, c.U = U ∧ K c.U c.Y c.T) :
    ∃ c : ℕ → TowerChart 𝒞 Z P,
      (∀ k, K (c k).U (c k).Y (c k).T) ∧ (∀ k, (c k).U ≤ W) ∧
      (∀ j k, j ≤ k → ((c j).V : Set Z) ⊆ (c k).V) ∧
      (⋃ k, ((c k).V : Set Z)) = P ⁻¹' (W : Set X) := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  let L := CompactExhaustion.choice X
  have hU : ∀ k : ℕ, ∃ c : TowerChart 𝒞 Z P,
      c.U = ⟨(W : Set X) ∩ interior (L (k+1)),W.isOpen.inter isOpen_interior⟩ ∧ K c.U c.Y c.T := fun k =>
    hLocal _ (fun _ h => h.1) (L (k+1)) (L.isCompact (k+1)) (fun _ h => interior_subset h.2)
  choose c hc hmem using hU
  have hUmono : ∀ {j k : ℕ}, j ≤ k → (c j).U ≤ (c k).U := fun {j k} hjk => by
    rw [hc,hc]
    exact fun _ h => ⟨h.1,interior_mono (L.subset (by omega)) h.2⟩
  have hVmono : ∀ {j k : ℕ}, j ≤ k → ((c j).V : Set Z) ⊆ (c k).V := fun {j k} hjk y hy => by
    have h' : y ∈ ((c j).V : Set Z) := hy
    rw [(c j).V_eq] at h'
    exact (c k).mem_V (hUmono hjk h')
  refine ⟨c,hmem,fun k => by rw [hc]; exact fun _ h => h.1,fun _ _ => hVmono,?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨k,hk⟩ := mem_iUnion.mp hz
    rw [(c k).V_eq,hc] at hk
    exact hk.1
  · intro hz
    obtain ⟨k,hk⟩ := L.exists_mem (P z)
    refine mem_iUnion.mpr ⟨k,(c k).mem_V ?_⟩
    rw [hc]
    exact ⟨hz,L.subset_interior_succ k hk⟩
end
end Hironaka.HironakaG3ComponentChartChain
