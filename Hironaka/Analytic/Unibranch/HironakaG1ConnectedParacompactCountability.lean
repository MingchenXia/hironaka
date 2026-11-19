import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Geometry.Manifold.ChartedSpace

/-! # Derived countability on noncompact connected native smooth pieces

Connectedness and genuine paracompactness turn a locally finite precompact
cover into a countable compact covering.  Actual chart spaces therefore need
no incoming second-countability packet. Blueprint first:
`hironaka-g1-connected-paracompact-countability.tex`.
-/

set_option autoImplicit false
open Set Filter Topology

namespace Hironaka.Analytic.Unibranch.HironakaG1ConnectedParacompactCountability

noncomputable section

private def reachSet {ι : Type*} (N : ι → Set ι) (a : ι) : ℕ → Set ι
  | 0 => {a}
  | n + 1 => reachSet N a n ∪ ⋃ i ∈ reachSet N a n, N i

private theorem reachSet_finite {ι : Type*} (N : ι → Set ι) (hN : ∀ i, (N i).Finite)
    (a : ι) (n : ℕ) : (reachSet N a n).Finite := by
  induction n with
  | zero => exact finite_singleton a
  | succ n hn => exact hn.union (hn.biUnion fun i _ => hN i)

/-- A genuine locally finite precompact refinement and connectedness derive a
countable compact covering, with no global countability assumption. -/
theorem sigmaCompactSpace_of_connected_paracompact (X : Type*) [TopologicalSpace X]
    [ConnectedSpace X] [WeaklyLocallyCompactSpace X] [ParacompactSpace X] :
    SigmaCompactSpace X := by
  choose K hK hKnhds using fun x : X => exists_compact_mem_nhds x
  have hcover : (⋃ x : X, interior (K x)) = univ :=
    iUnion_eq_univ_iff.mpr fun x => ⟨x, mem_interior_iff_mem_nhds.mpr (hKnhds x)⟩
  obtain ⟨V, hVo, hVcover, hVlf, hVsub⟩ :=
    precise_refinement (fun x : X => interior (K x)) (fun _ => isOpen_interior) hcover
  let N : X → Set X := fun i => {j | (V j ∩ K i).Nonempty}
  have hN (i : X) : (N i).Finite := hVlf.finite_nonempty_inter_compact (hK i)
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨i₀, hi₀⟩ := iUnion_eq_univ_iff.mp hVcover x₀
  let R : Set X := ⋃ n : ℕ, reachSet N i₀ n
  have hRcount : R.Countable := countable_iUnion fun n => (reachSet_finite N hN i₀ n).countable
  have hRnext {i j : X} (hi : i ∈ R) (hj : j ∈ N i) : j ∈ R := by
    obtain ⟨n, hn⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨n + 1, Or.inr (mem_iUnion₂.mpr ⟨i, hn, hj⟩)⟩
  let U : Set X := ⋃ i ∈ R, V i
  have hUo : IsOpen U := isOpen_biUnion fun i _ => hVo i
  have hUc : Uᶜ = ⋃ j ∈ Rᶜ, V j := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp hVcover x
      exact mem_iUnion₂.mpr ⟨j, fun hjR => hx (mem_iUnion₂.mpr ⟨j, hjR, hj⟩), hj⟩
    · intro hx hxin
      obtain ⟨j, hjR, hj⟩ := mem_iUnion₂.mp hx
      obtain ⟨i, hiR, hi⟩ := mem_iUnion₂.mp hxin
      exact hjR (hRnext hiR ⟨x, hj, interior_subset (hVsub i hi)⟩)
  have hUne : U.Nonempty := ⟨x₀, mem_iUnion₂.mpr
    ⟨i₀, mem_iUnion.mpr ⟨0, mem_singleton i₀⟩, hi₀⟩⟩
  have hUuniv : U = univ :=
    (show IsClopen U from ⟨isOpen_compl_iff.mp (hUc ▸ isOpen_biUnion fun i _ => hVo i), hUo⟩).eq_univ hUne
  have hKcover : (⋃ i ∈ R, K i) = univ := by
    apply eq_univ_of_univ_subset
    rw [← hUuniv]
    exact iUnion₂_mono fun i _ => (hVsub i).trans interior_subset
  apply isSigmaCompact_univ_iff.mp
  rw [← hKcover]
  exact isSigmaCompact_biUnion hRcount fun i _ => (hK i).isSigmaCompact

/-- Original connected paracompact chart spaces inherit countability from
their genuine locally compact second-countable model. -/
theorem secondCountable_of_connected_paracompact_charted
    (H M : Type*) [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] [LocallyCompactSpace H] [SecondCountableTopology H]
    [ConnectedSpace M] [ParacompactSpace M] : SecondCountableTopology M := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let : SigmaCompactSpace M := sigmaCompactSpace_of_connected_paracompact M
  exact ChartedSpace.secondCountable_of_sigmaCompact H M

end
end Hironaka.Analytic.Unibranch.HironakaG1ConnectedParacompactCountability
