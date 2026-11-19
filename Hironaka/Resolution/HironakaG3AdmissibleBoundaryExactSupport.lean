import Hironaka.Resolution.HironakaG3AdmissibleBoundarySupport
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3AdmissibleBoundaryExactSupport
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaAdmissibleSequence HironakaAdmissibleCalculus

/-- Admissibility covers the total initial boundary and the exceptional locus. -/
theorem admissible_boundary_covers_preimage_and_exceptional {n : ℕ} {X Y : CMfd.{0} n}
    (E₀ : List (Set X)) (F : Set X) (hE : ∀ H ∈ E₀, IsClosed H)
    {f : Y → X} {E : List (Set Y)} (h : IsAdmissibleBlowupSequence n X E₀ F Y f E) :
    f ⁻¹' (⋃ H ∈ E₀, H) ∪ exceptionalLocus n f ⊆ ⋃ H ∈ E, H := by
  obtain ⟨T,N,hEq,hT,_hN,_hNF,hExc⟩ := IsAdmissibleBlowupSequence.exists_decomposition h
  intro z hz
  rw [hEq]
  rcases hz with hOld | hExceptional
  · obtain ⟨H,hH,hzH⟩ := mem_iUnion₂.mp hOld
    rcases (hT H (hE H hH)).2.2.1 hzH with hTrans | hBorn
    · exact mem_iUnion₂.mpr ⟨T H,List.mem_append_left _ (List.mem_map_of_mem hH),hTrans⟩
    · obtain ⟨B,hB,hzB⟩ := mem_iUnion₂.mp hBorn
      exact mem_iUnion₂.mpr ⟨B,List.mem_append_right _ hB,hzB⟩
  · obtain ⟨B,hB,hzB⟩ := mem_iUnion₂.mp (hExc hExceptional)
    exact mem_iUnion₂.mpr ⟨B,List.mem_append_right _ hB,hzB⟩

/-- An upper bound gives exact support; it is not a consequence of
admissibility alone. -/
theorem admissible_boundary_exact_support_of_upper_bound {n : ℕ} {X Y : CMfd.{0} n}
    (E₀ : List (Set X)) (F : Set X) (hE : ∀ H ∈ E₀, IsClosed H)
    {f : Y → X} {E : List (Set Y)} (h : IsAdmissibleBlowupSequence n X E₀ F Y f E)
    (hUpper : (⋃ H ∈ E, H) ⊆ f ⁻¹' (⋃ H ∈ E₀, H) ∪ exceptionalLocus n f) :
    (⋃ H ∈ E, H) = f ⁻¹' (⋃ H ∈ E₀, H) ∪ exceptionalLocus n f :=
  Subset.antisymm hUpper (admissible_boundary_covers_preimage_and_exceptional E₀ F hE h)
end
end Hironaka.HironakaG3AdmissibleBoundaryExactSupport
