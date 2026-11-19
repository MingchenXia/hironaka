import Hironaka.Resolution.HironakaG8CombExactLocalArrangement
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Analytic.RiemannExtension
import Mathlib.Topology.Baire.Lemmas

set_option autoImplicit false
open Set Filter TopologicalSpace Metric
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8AnalyticSpineCover
noncomputable section

open HironakaG8VariableCombArrangement HironakaG8CombExactLocalArrangement

/-- A genuine finite analytic presentation on the connected complex
model satisfies the identity principle for its whole zero set. -/
theorem analytic_eq_univ_of_interior_nonempty {n : ℕ} {A : Set (ComplexModel n)}
    (hA : IsComplexAnalyticSubset (n := n) A) (hne : (interior A).Nonempty) :
    A = univ := by
  have hClosed : IsClosed (interior A) := by
    rw [← closure_subset_iff_isClosed]
    intro x hx
    obtain ⟨p⟩ := hA x
    have hxU : x ∈ p.coordinateNeighborhood := by
      simpa [complexChartAt,chartAt_self_eq] using p.center_mem_coordinateNeighborhood
    have hEquation (z : ComplexModel n) (hz : z ∈ p.coordinateNeighborhood) :
        z ∈ A ↔ ∀ i, p.generator i z = 0 := by
      exact p.zeroLocus (y := z) (by simp [complexChartAt,chartAt_self_eq])
        (by simpa [complexChartAt,chartAt_self_eq] using hz)
    obtain ⟨r,hr,hBall⟩ := Metric.isOpen_iff.mp p.isOpen_coordinateNeighborhood x hxU
    obtain ⟨y,hyBall,hyA⟩ := mem_closure_iff.mp hx (ball x r) isOpen_ball (mem_ball_self hr)
    have hZero (i : Fin p.generatorCount) : ∀ᶠ z in 𝓝 y, p.generator i z = 0 := by
      filter_upwards [mem_interior_iff_mem_nhds.mp hyA,isOpen_ball.mem_nhds hyBall] with z hz hzBall
      exact (hEquation z (hBall hzBall)).mp hz i
    have hSub : ball x r ⊆ A := by
      intro z hz
      apply (hEquation z (hBall hz)).mpr
      intro i
      exact (RiemannExtension.eventually_eq_zero_of_eventually_eq_zero isOpen_ball
        (convex_ball x r).isPreconnected ((p.generator_holomorphic i).mono hBall)
        hyBall (hZero i) z hz).self_of_nhds
    exact interior_maximal hSub isOpen_ball (mem_ball_self hr)
  have hAll := (show IsClopen (interior A) from ⟨hClosed,isOpen_interior⟩).eq_univ hne
  exact eq_univ_of_univ_subset (hAll ▸ interior_subset)

/-- Countably many actual complex analytic sets cannot cover a nonempty
open patch of the complex model unless one is the entire model. -/
theorem exists_full_analytic_of_open_cover {n : ℕ} {ι : Type*} [Countable ι]
    (F : ι → Set (ComplexModel n)) (hF : ∀ i, IsComplexAnalyticSubset (n := n) (F i))
    (O : Set (ComplexModel n)) (hO : IsOpen O) (hne : O.Nonempty)
    (hCover : O ⊆ ⋃ i, F i) : ∃ i, F i = univ := by
  classical
  by_contra hNone
  have hDense (i : ι) : Dense (F i)ᶜ := by
    have hI : interior (F i) = ∅ := Set.not_nonempty_iff_eq_empty.mp
      (fun h => hNone ⟨i,analytic_eq_univ_of_interior_nonempty (hF i) h⟩)
    rw [dense_iff_closure_eq,closure_compl,hI,compl_empty]
  have hh := dense_iInter_of_isOpen (fun i => (hF i).isClosed.isOpen_compl) hDense
  obtain ⟨z,hZ,hzO⟩ := hh.exists_mem_open hO hne
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hCover hzO)
  exact (mem_iInter.mp hZ i) hi

/-- A holomorphic parameterization of the fixed spine. -/
def spineParameter (z : ComplexModel 1) : Ambient :=
  z 0 • EuclideanSpace.single (2 : Fin 3) (1 : ℂ)

theorem spineParameter_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel 1) 𝓘(ℂ,ComplexModel 3) ∞ spineParameter :=
  (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).contDiff.contMDiff.smul contMDiff_const

theorem spineParameter_anchor (k : ℕ) :
    spineParameter (EuclideanSpace.single (0 : Fin 1) (k : ℂ)) = anchor k := by
  apply PiLp.ext
  intro i
  change (EuclideanSpace.single (0 : Fin 1) (k : ℂ)) 0 *
    (EuclideanSpace.single (2 : Fin 3) (1 : ℂ)) i =
      (EuclideanSpace.single (2 : Fin 3) (k : ℂ)) i
  by_cases h : i = 2 <;> simp [h]

/-- If a countable analytic footprint family covers a nonempty open
patch of the spine, some single footprint contains every anchor. -/
theorem exists_footprint_containing_anchors {ι : Type*} [Countable ι]
    (F : ι → Set Ambient) (hF : ∀ i, IsComplexAnalyticSubset (n := 3) (F i))
    (O : Set (ComplexModel 1)) (hO : IsOpen O) (hne : O.Nonempty)
    (hCover : ∀ z ∈ O, spineParameter z ∈ ⋃ i, F i) :
    ∃ i, ∀ k : ℕ, anchor k ∈ F i := by
  obtain ⟨i,hi⟩ := exists_full_analytic_of_open_cover (fun i => spineParameter ⁻¹' F i)
    (fun i => AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage spineParameter_contMDiff (hF i))
    O hO hne (by
      intro z hz
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hCover z hz)
      exact mem_iUnion.mpr ⟨i,hi⟩)
  refine ⟨i,fun k => ?_⟩
  have hm : EuclideanSpace.single (0 : Fin 1) (k : ℂ) ∈ spineParameter ⁻¹' F i := hi ▸ mem_univ _
  exact spineParameter_anchor k ▸ hm

end
end Hironaka.HironakaG8AnalyticSpineCover

#print axioms Hironaka.HironakaG8AnalyticSpineCover.exists_footprint_containing_anchors
