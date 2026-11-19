import Hironaka.Resolution.HironakaG3AdmissibleBoundarySupport
import Hironaka.Resolution.HironakaG3ActualSeparatedContactAssembly
import Hironaka.Resolution.HironakaG3IndexedMixedBad
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatorBoundaryFootprint
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass HironakaG3RPureEmbedded
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedMixedBad HironakaG3IndexedMixedGluing
  HironakaG3IndexedMixedChartBoundary HironakaG3IndexedMixedGlobalSNC HironakaG3FiniteMixedBadLocus
  HironakaG3AdmissibleBoundarySupport HironakaAdmissibleSequence HironakaG3REmbeddedGlobalSNC
  RestrictEmptyTower

variable {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X}
variable {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
variable (V : ι → ClosedIrreducibleAnalyticSubvariety n X) (D : κ → Set X)

theorem actual_separator_chart_boundary_footprint
    (hD : IsLocallyFiniteSNCDivisor n D)
    (c : TowerChart (indexedMixedClass V D) Z P) (s : Finset ι) (r : Finset κ)
    (Ef : List (Set c.Y))
    (hAdm : IsAdmissibleBlowupSequence n (CMfd.of (n := n) c.U)
      (((r.sort (· ≤ ·)).map D).map ((Subtype.val : c.U → X) ⁻¹' ·))
      ((Subtype.val : c.U → X) ⁻¹' mixedBadLocus
        (fun j : Fin (s.sort (· ≤ ·)).length => V ((s.sort (· ≤ ·)).get j))) c.Y c.T.proj Ef) :
    (⋃ H ∈ mixedChartBoundary V D c Ef, H) ⊆
      P ⁻¹' ((⋃ j, D j) ∪ indexedMixedBad V) := by
  let E₀ := ((r.sort (· ≤ ·)).map D).map ((Subtype.val : c.U → X) ⁻¹' ·)
  let l := s.sort (· ≤ ·)
  let e : Fin l.length ↪ ι := ⟨l.get,(s.sort_nodup (· ≤ ·)).injective_get⟩
  have hE : ∀ H ∈ E₀, IsClosed H := by
    intro H hH
    obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hH
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hA
    exact (hD.2.1 j).preimage continuous_subtype_val
  have hAdm' : IsAdmissibleBlowupSequence n (CMfd.of (n := n) c.U) E₀
      ((Subtype.val : c.U → X) ⁻¹' mixedBadLocus (fun j : Fin l.length => V (l.get j))) c.Y c.T.proj Ef := by
    simpa only [E₀,l] using hAdm
  have hSupp := admissible_boundary_support_subset (n := n) (X := CMfd.of (n := n) c.U) (Y := c.Y)
    (f := c.T.proj) (E := Ef) E₀
    ((Subtype.val : c.U → X) ⁻¹' mixedBadLocus (fun j : Fin l.length => V (l.get j))) hE hAdm'
  intro z hz
  obtain ⟨H,hH,hzH⟩ := mem_iUnion₂.mp hz
  change H ∈ Ef.map (chartIncl c '' ·) at hH
  obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hH
  obtain ⟨y,hy,rfl⟩ := hzH
  have hySupp := hSupp (mem_iUnion₂.mpr ⟨K,hK,hy⟩)
  change P (chartIncl c y) ∈ (⋃ j, D j) ∪ indexedMixedBad V
  rw [proj_chartIncl c y]
  rcases hySupp with hyOld | hyBad
  · left
    obtain ⟨A,hA,hyA⟩ := mem_iUnion₂.mp hyOld
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hA
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hB
    exact mem_iUnion.mpr ⟨j,hyA⟩
  · right
    exact finite_bad_subset_indexed V e hyBad

theorem separator_chart_witness_boundary_footprint
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (hD : IsLocallyFiniteSNCDivisor n D)
    (c : TowerChart (indexedMixedClass V D) Z P) (Ef : List (Set c.Y))
    (hEf : MixedBoundaryWitness V D c Ef) :
    (⋃ H ∈ mixedChartBoundary V D c Ef, H) ⊆
      P ⁻¹' ((⋃ j, D j) ∪ indexedMixedBad V) := by
  obtain ⟨s,r,Ef',hs,hr,hTree,hOver,hAdm,hSNC,_hDis⟩ := c.mem
  have hEf' : MixedBoundaryWitness V D c Ef' := ⟨s,r,hs,hr,hTree,hOver,hSNC⟩
  have hov := mixed_witness_chart_boundary_overlap V D hDim hDistinct c c Ef Ef' hEf hEf'
  have hFoot := actual_separator_chart_boundary_footprint V D hD c s r Ef' hAdm
  intro z hz
  obtain ⟨H,hH,hzH⟩ := mem_iUnion₂.mp hz
  have hzV : z ∈ c.V := by
    change H ∈ Ef.map (chartIncl c '' ·) at hH
    obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hH
    obtain ⟨y,hy,rfl⟩ := hzH
    exact (c.φ y).2
  have hzU : P z ∈ c.U := by
    have hzV' : z ∈ ((c.V : Opens Z) : Set Z) := hzV
    rw [c.V_eq] at hzV'
    exact hzV'
  have hzTrace : z ∈ H ∩ P ⁻¹' ((c.U ⊓ c.U : Opens X) : Set X) := ⟨hzH,hzU,hzU⟩
  have hM : H ∩ P ⁻¹' ((c.U ⊓ c.U : Opens X) : Set X) ∈
      ((mixedChartBoundary V D c Ef).map
        (· ∩ P ⁻¹' ((c.U ⊓ c.U : Opens X) : Set X))).filter (fun H => decide H.Nonempty) := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_map.mpr ⟨H,hH,rfl⟩,decide_eq_true ⟨z,hzTrace⟩⟩
  rw [hov] at hM
  obtain ⟨K,hK,hEq⟩ := List.mem_map.mp (List.mem_filter.mp hM).1
  have hzK : z ∈ K := by
    have hzK' : z ∈ K ∩ P ⁻¹' ((c.U ⊓ c.U : Opens X) : Set X) := by rw [hEq]; exact hzTrace
    exact hzK'.1
  exact hFoot (mem_iUnion₂.mpr ⟨K,hK,hzK⟩)

theorem separator_global_boundary_footprint
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (hD : IsLocallyFiniteSNCDivisor n D)
    (Ex : SNCExhaustion Z)
    (hCharts : ∀ k, ∃ (c : TowerChart (indexedMixedClass V D) Z P) (Ef : List (Set c.Y)),
      MixedBoundaryWitness V D c Ef ∧ Ex.W k = c.V ∧ Ex.B k = mixedChartBoundary V D c Ef) :
    (⋃ k, ⋃ H ∈ Ex.B k, H) ⊆ P ⁻¹' ((⋃ j, D j) ∪ indexedMixedBad V) := by
  intro z hz
  obtain ⟨k,hzk⟩ := mem_iUnion.mp hz
  obtain ⟨c,Ef,hEf,_hW,hB⟩ := hCharts k
  rw [hB] at hzk
  exact separator_chart_witness_boundary_footprint V D hDim hDistinct hD c Ef hEf hzk
end
end Hironaka.HironakaG3SeparatorBoundaryFootprint
