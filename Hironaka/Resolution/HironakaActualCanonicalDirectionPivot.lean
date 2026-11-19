import Hironaka.Resolution.HironakaActualCanonicalVertexDirectionalInvariance
import Mathlib.Data.Finset.Max

/-! An actual order-adapted pivot in a nonzero invariant direction, preserving all source vertices. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualCanonicalDirectionPivot
noncomputable section
open HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualHomogeneousInitialHS HironakaActualCanonicalVertexDirectionalInvariance
variable {n : ℕ}

/-- A genuine nonzero direction internally selects a maximal actual coordinate monomial. -/
theorem exists_direction_maximal_coordinate (m : MonomialOrder (Fin n))
    (v : Fin n → ℂ) (hv : ∃ i, v i ≠ 0) :
    ∃ f : Fin n, v f ≠ 0 ∧
      ∀ i : Fin n, v i ≠ 0 → m.toSyn (Finsupp.single i 1) ≤ m.toSyn (Finsupp.single f 1) := by
  let s : Finset (Fin n) := Finset.univ.filter (fun i => v i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i,hi⟩ := hv
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
  obtain ⟨f,hf,hmax⟩ := s.exists_max_image (fun i => m.toSyn (Finsupp.single i 1)) hs
  refine ⟨f,(Finset.mem_filter.mp hf).2,?_⟩
  intro i hi
  exact hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩)

/-- Actual directional stability forces every SAME canonical vertex to avoid the maximal direction coordinate. -/
theorem actualInitialVertex_maximal_direction_coordinate_eq_zero
    (m : MonomialOrder (Fin n)) (J : Ideal (MvPowerSeries (Fin n) ℂ))
    (v : Fin n → ℂ)
    (hD : ∀ F ∈ J, (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i F) ∈ J)
    (f : Fin n) (hvf : v f ≠ 0)
    (hmax : ∀ i : Fin n, v i ≠ 0 →
      m.toSyn (Finsupp.single i 1) ≤ m.toSyn (Finsupp.single f 1))
    (a : actualInitialVertices m J) : a.val f=0 := by
  by_contra haf
  have hafpos : 0 < a.val f := Nat.pos_of_ne_zero haf
  let c := a.val-Finsupp.single f 1
  have hsingle : Finsupp.single f 1 ≤ a.val := by
    intro i
    by_cases hi : i=f
    · subst i
      simpa only [Finsupp.single_eq_same] using Nat.succ_le_iff.mpr hafpos
    · simp only [Finsupp.single_eq_of_ne hi,zero_le]
  have hca : c+Finsupp.single f 1=a.val := tsub_add_cancel_of_le hsingle
  have hzero := congrArg (MvPowerSeries.coeff c)
    (directional_pderiv_actualReducedVertexSeries_eq_zero m J v hD a)
  rw [map_sum,map_zero] at hzero
  have hsum : (∑ i : Fin n, MvPowerSeries.coeff c
      (v i • MvPowerSeries.pderiv ℂ i (actualReducedVertexSeries m J a)))=
        v f * ((c f+1 : ℕ) : ℂ) := by
    rw [Finset.sum_eq_single f]
    · rw [map_smul,MvPowerSeries.coeff_pderiv,hca,
        actualReducedVertexSeries_coefficient,one_mul,smul_eq_mul]
      simp only [Nat.cast_add,Nat.cast_one]
    · intro i _hi hif
      by_cases hvi : v i=0
      · simp only [hvi,zero_smul,map_zero]
      · have hne : m.toSyn (Finsupp.single i 1) ≠ m.toSyn (Finsupp.single f 1) := by
          intro he
          have hs := m.toSyn.injective he
          exact hif (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) hs)
        have hlt : m.toSyn (Finsupp.single i 1) < m.toSyn (Finsupp.single f 1) :=
          lt_of_le_of_ne (hmax i hvi) hne
        have hci : m.toSyn (c+Finsupp.single i 1) < m.toSyn a.val := by
          rw [← hca,map_add,map_add]
          simpa only [add_comm] using add_lt_add_left hlt (m.toSyn c)
        rw [map_smul,MvPowerSeries.coeff_pderiv,
          actualReducedVertexSeries_coefficient_lower m J a _ hci,zero_mul,smul_zero]
    · intro hf
      exact (hf (Finset.mem_univ f)).elim
  rw [hsum] at hzero
  have hnat : ((c f+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (c f)
  exact (mul_ne_zero hvf hnat) hzero

/-- Literal vertex exponents with zero in one coordinate give BOTH whole diagram-cylinder directions. -/
theorem actualInitialDiagram_erase_iff_of_vertices_zero
    (m : MonomialOrder (Fin n)) (J : Ideal (MvPowerSeries (Fin n) ℂ)) (f : Fin n)
    (hv : ∀ a : actualInitialVertices m J, a.val f=0) (α : Fin n →₀ ℕ) :
    α ∈ actualInitialDiagram m J ↔ α.erase f ∈ actualInitialDiagram m J := by
  constructor
  · intro hα
    obtain ⟨a,ha,hle⟩ := (mem_actualInitialDiagram_iff_vertex_le m J α).mp hα
    apply (mem_actualInitialDiagram_iff_vertex_le m J (α.erase f)).mpr
    refine ⟨a,ha,?_⟩
    have haf := hv ⟨a,ha⟩
    intro i
    by_cases hi : i=f
    · subst i
      simp [haf]
    · simpa only [Finsupp.erase_ne hi] using hle i
  · intro hα
    apply actualInitialDiagram_upper m J (α.erase f) α hα
    intro i
    by_cases hi : i=f
    · subst i
      simp
    · simp only [Finsupp.erase_ne hi,le_refl]

/-- Initial-ideal directional stability internally selects an actual cylindrical source coordinate. -/
theorem exists_initial_direction_cylindrical_coordinate
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (v : Fin n → ℂ) (hv : ∃ i, v i ≠ 0)
    (hD : ∀ F ∈ actualHomogeneousInitialIdeal K,
      (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i F) ∈ actualHomogeneousInitialIdeal K) :
    ∃ f : Fin n, v f ≠ 0 ∧
      (∀ i : Fin n, v i ≠ 0 → MonomialOrder.degLex.toSyn (Finsupp.single i 1) ≤
        MonomialOrder.degLex.toSyn (Finsupp.single f 1)) ∧
      (∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f=0) ∧
      ∀ α : Fin n →₀ ℕ, α ∈ actualInitialDiagram MonomialOrder.degLex K ↔
        α.erase f ∈ actualInitialDiagram MonomialOrder.degLex K := by
  obtain ⟨f,hvf,hmax⟩ := exists_direction_maximal_coordinate MonomialOrder.degLex v hv
  have hvertices : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f=0 := by
    intro a
    exact actualInitialVertex_maximal_direction_coordinate_eq_zero MonomialOrder.degLex
      (actualHomogeneousInitialIdeal K) v hD f hvf hmax (actualHomogeneousInitialVertex K a)
  exact ⟨f,hvf,hmax,hvertices,
    actualInitialDiagram_erase_iff_of_vertices_zero MonomialOrder.degLex K f hvertices⟩

end
end Hironaka.HironakaActualCanonicalDirectionPivot
