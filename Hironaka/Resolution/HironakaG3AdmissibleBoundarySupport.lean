import Hironaka.Blowup.BlowupTowers
import Hironaka.Resolution.HironakaAdmissibleCalculus
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3AdmissibleBoundarySupport
noncomputable section
open BlowupTowers HironakaAdmissibleSequence HironakaAdmissibleCalculus

theorem admissible_boundary_support_subset {n : ℕ} {X Y : CMfd.{0} n}
    (E₀ : List (Set X)) (F : Set X) (hE : ∀ H ∈ E₀, IsClosed H)
    {f : Y → X} {E : List (Set Y)} (h : IsAdmissibleBlowupSequence n X E₀ F Y f E) :
    (⋃ H ∈ E, H) ⊆ f ⁻¹' ((⋃ H ∈ E₀, H) ∪ F) := by
  obtain ⟨T,N,hEq,hT,_hN,hNF,_hExc⟩ :=
    HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.exists_decomposition h
  intro y hy
  obtain ⟨H,hH,hyH⟩ := mem_iUnion₂.mp hy
  rw [hEq] at hH
  rcases List.mem_append.mp hH with hOld | hBorn
  · obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hOld
    exact Or.inl (mem_iUnion₂.mpr ⟨A,hA,(hT A (hE A hA)).2.1 hyH⟩)
  · exact Or.inr (hNF (mem_iUnion₂.mpr ⟨H,hBorn,hyH⟩))
end
end Hironaka.HironakaG3AdmissibleBoundarySupport
