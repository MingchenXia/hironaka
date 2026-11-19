import Hironaka.Resolution.HironakaG8VariableCombArrangement

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology
namespace Hironaka.HironakaG8CombExactLocalArrangement

open HironakaG8VariableCombArrangement

def toothWindow (k : ℕ) : Set Ambient :=
  {z | ‖z 0‖ < 1 ∧ ‖z 2 - (k : ℂ)‖ < 1/2}

noncomputable def anchor (k : ℕ) : Ambient :=
  EuclideanSpace.single (2 : Fin 3) (k : ℂ)

theorem anchor_coords (k : ℕ) :
    anchor k 0 = 0 ∧ anchor k 1 = 0 ∧ anchor k 2 = (k : ℂ) := by
  simp [anchor]

theorem anchor_mem_window (k : ℕ) : anchor k ∈ toothWindow k := by
  obtain ⟨h0,_,h2⟩ := anchor_coords k
  change ‖anchor k 0‖ < 1 ∧ ‖anchor k 2 - (k : ℂ)‖ < 1/2
  rw [h0,h2,sub_self,norm_zero]
  norm_num

theorem toothWindow_isOpen (k : ℕ) : IsOpen (toothWindow k) := by
  let c (i : Fin 3) : Ambient →L[ℂ] ℂ := EuclideanSpace.proj (𝕜 := ℂ) i
  change IsOpen ({z | ‖c 0 z‖ < (1 : ℝ)} ∩ {z | ‖c 2 z - (k : ℂ)‖ < 1/2})
  exact (isOpen_lt (c 0).continuous.norm continuous_const).inter
    (isOpen_lt ((c 2).continuous.sub continuous_const).norm continuous_const)

private theorem cast_separation {j k : ℕ} (h : j ≠ k) : 1 ≤ ‖(j : ℂ) - (k : ℂ)‖ := by
  rw [← Complex.ofReal_natCast,← Complex.ofReal_natCast,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs]
  rcases lt_or_gt_of_ne h with h | h
  · have hh : (j : ℝ)+1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hh : (k : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- The literal open about tooth k meets only its own finite stack. -/
theorem toothPlane_level_of_mem_window {k : ℕ} {j : Tooth} {z : Ambient}
    (hW : z ∈ toothWindow k) (hP : z ∈ toothPlane j) : j.1 = k := by
  by_contra h
  have hSep := cast_separation h
  have hz : z 2 = (j.1 : ℂ) + slope j * z 0 := hP
  have heq : (j.1 : ℂ) - (k : ℂ) = (z 2 - (k : ℂ)) - slope j * z 0 := by rw [hz]; ring
  rw [heq] at hSep
  have hProd : ‖slope j * z 0‖ ≤ (1/4 : ℝ) := by
    rw [norm_mul]
    calc
      _ ≤ (1/4 : ℝ) * 1 := mul_le_mul (slope_norm_le j) hW.1.le (norm_nonneg _) (by norm_num)
      _ = _ := mul_one _
  have ht := norm_sub_le (z 2 - (k : ℂ)) (slope j * z 0)
  have hz2 : ‖z 2 - (k : ℂ)‖ < (1/2 : ℝ) := hW.2
  linarith

/-- The actual analytic comb has an exact finite local union with
k+1 moving affine branches and the two fixed planes near tooth k. -/
theorem comb_exact_window (k : ℕ) :
    comb ∩ toothWindow k =
      ({z : Ambient | z 0 = 0} ∪ {z | z 1 = 0} ∪
        ⋃ j : Fin (k+1), toothPlane ⟨k,j⟩) ∩ toothWindow k := by
  ext z
  constructor
  · rintro ⟨h,hz⟩
    refine ⟨?_,hz⟩
    rcases h with h | h
    · exact Or.inl h
    · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
      have he := toothPlane_level_of_mem_window hz hj
      obtain ⟨a,j⟩ := j
      change a = k at he
      subst a
      exact Or.inr (Set.mem_iUnion.mpr ⟨j,hj⟩)
  · rintro ⟨h,hz⟩
    refine ⟨?_,hz⟩
    rcases h with h | h
    · exact Or.inl h
    · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨k,j⟩,hj⟩)

end Hironaka.HironakaG8CombExactLocalArrangement

#print axioms Hironaka.HironakaG8CombExactLocalArrangement.comb_exact_window
