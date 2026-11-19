import Hironaka.Resolution.HironakaG3SeparatorBoundaryFootprint
import Hironaka.Resolution.HironakaG3AdmissibleBoundaryExactSupport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatorBoundaryLower
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass HironakaG3RPureEmbedded
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedMixedBad HironakaG3IndexedMixedGluing
  HironakaG3IndexedMixedChartBoundary HironakaG3IndexedMixedGlobalSNC HironakaG3FiniteMixedBadLocus
  HironakaG3AdmissibleBoundaryExactSupport HironakaAdmissibleSequence HironakaG3REmbeddedGlobalSNC
  RestrictEmptyTower
variable {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X}
variable {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
variable (V : ι → ClosedIrreducibleAnalyticSubvariety n X) (D : κ → Set X)

/-- Every admissible actual chart boundary covers the full visible original
boundary preimage and the exceptional locus on that chart. -/
theorem actual_separator_chart_boundary_lower (hD : IsLocallyFiniteSNCDivisor n D)
    (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (c : TowerChart (indexedMixedClass V D) Z P) (s : Finset ι) (r : Finset κ)
    (hr : ∀ i, (D i ∩ (c.U : Set X)).Nonempty → i ∈ r)
    (Ef : List (Set c.Y))
    (hAdm : IsAdmissibleBlowupSequence n (CMfd.of (n := n) c.U)
      (((r.sort (· ≤ ·)).map D).map ((Subtype.val : c.U → X) ⁻¹' ·))
      ((Subtype.val : c.U → X) ⁻¹' mixedBadLocus
        (fun j : Fin (s.sort (· ≤ ·)).length => V ((s.sort (· ≤ ·)).get j))) c.Y c.T.proj Ef) :
    (P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P) ∩ c.V ⊆
      ⋃ H ∈ mixedChartBoundary V D c Ef, H := by
  let E₀ := ((r.sort (· ≤ ·)).map D).map ((Subtype.val : c.U → X) ⁻¹' ·)
  let F := ((Subtype.val : c.U → X) ⁻¹' mixedBadLocus
    (fun j : Fin (s.sort (· ≤ ·)).length => V ((s.sort (· ≤ ·)).get j)))
  have hE : ∀ H ∈ E₀, IsClosed H := by
    intro H hH
    obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hH
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hA
    exact (hD.2.1 j).preimage continuous_subtype_val
  have hlocal := admissible_boundary_covers_preimage_and_exceptional
    (n := n) (X := CMfd.of (n := n) c.U) (Y := c.Y) (f := c.T.proj) (E := Ef) E₀ F hE hAdm
  intro z hz
  let y := c.φ.symm ⟨z,hz.2⟩
  have hyz : chartIncl c y = z := chartIncl_symm c ⟨z,hz.2⟩
  have hy : y ∈ c.T.proj ⁻¹' (⋃ H ∈ E₀, H) ∪ exceptionalLocus n c.T.proj := by
    rcases hz.1 with hzD | hzExc
    · left
      obtain ⟨j,hj⟩ := mem_iUnion.mp hzD
      have hzU : P z ∈ c.U := by
        have h := hz.2
        rw [c.V_eq] at h
        exact h
      have hjr : j ∈ r := hr j ⟨P z,hj,hzU⟩
      refine mem_iUnion₂.mpr ⟨(Subtype.val : c.U → X) ⁻¹' D j, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨D j,List.mem_map.mpr ⟨j,by simpa using hjr,rfl⟩,rfl⟩
      · change (c.T.proj y : X) ∈ D j
        rw [← proj_chartIncl c y,hyz]
        exact hj
    · right
      rw [exceptionalLocus_chart c hP]
      simpa only [mem_preimage,hyz] using hzExc
  obtain ⟨H,hH,hyH⟩ := mem_iUnion₂.mp (hlocal hy)
  refine mem_iUnion₂.mpr ⟨chartIncl c '' H,?_,?_⟩
  · exact List.mem_map.mpr ⟨H,hH,rfl⟩
  · exact ⟨y,hyH,hyz⟩

/-- Any actual boundary witness has the same lower support via its filtered
same-chart comparison with the admissible witness. -/
theorem separator_chart_witness_boundary_lower
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (hD : IsLocallyFiniteSNCDivisor n D)
    (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (c : TowerChart (indexedMixedClass V D) Z P) (Ef : List (Set c.Y))
    (hEf : MixedBoundaryWitness V D c Ef) :
    (P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P) ∩ c.V ⊆
      ⋃ H ∈ mixedChartBoundary V D c Ef, H := by
  obtain ⟨s,r,Ef',hs,hr,hTree,hOver,hAdm,hSNC,_hDis⟩ := c.mem
  have hEf' : MixedBoundaryWitness V D c Ef' := ⟨s,r,hs,hr,hTree,hOver,hSNC⟩
  have hov := mixed_witness_chart_boundary_overlap V D hDim hDistinct c c Ef' Ef hEf' hEf
  have hLower := actual_separator_chart_boundary_lower V D hD hP c s r hr Ef' hAdm
  intro z hz
  obtain ⟨H,hH,hzH⟩ := mem_iUnion₂.mp (hLower hz)
  have hzU : P z ∈ c.U := by
    have h := hz.2
    rw [c.V_eq] at h
    exact h
  have hzTrace : z ∈ H ∩ P ⁻¹' ((c.U ⊓ c.U : Opens X) : Set X) := ⟨hzH,hzU,hzU⟩
  have hM : H ∩ P ⁻¹' ((c.U ⊓ c.U : Opens X) : Set X) ∈
      ((mixedChartBoundary V D c Ef').map
        (· ∩ P ⁻¹' ((c.U ⊓ c.U : Opens X) : Set X))).filter (fun H => decide H.Nonempty) := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_map.mpr ⟨H,hH,rfl⟩,decide_eq_true ⟨z,hzTrace⟩⟩
  rw [hov] at hM
  obtain ⟨K,hK,hEq⟩ := List.mem_map.mp (List.mem_filter.mp hM).1
  have hzK : z ∈ K := by
    have hzK' : z ∈ K ∩ P ⁻¹' ((c.U ⊓ c.U : Opens X) : Set X) := by rw [hEq]; exact hzTrace
    exact hzK'.1
  exact mem_iUnion₂.mpr ⟨K,hK,hzK⟩

theorem separator_global_boundary_lower
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (hD : IsLocallyFiniteSNCDivisor n D)
    (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (Ex : SNCExhaustion Z)
    (hCharts : ∀ k, ∃ (c : TowerChart (indexedMixedClass V D) Z P) (Ef : List (Set c.Y)),
      MixedBoundaryWitness V D c Ef ∧ Ex.W k = c.V ∧ Ex.B k = mixedChartBoundary V D c Ef) :
    P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P ⊆ ⋃ k, ⋃ H ∈ Ex.B k, H := by
  intro z hz
  obtain ⟨k,hk⟩ := Ex.cover z
  obtain ⟨c,Ef,hEf,hW,hB⟩ := hCharts k
  have hzV : z ∈ c.V := by rw [← hW]; exact hk
  have hzB := separator_chart_witness_boundary_lower V D hDim hDistinct hD hP c Ef hEf ⟨hz,hzV⟩
  exact mem_iUnion.mpr ⟨k,by simpa only [hB] using hzB⟩
end
end Hironaka.HironakaG3SeparatorBoundaryLower
