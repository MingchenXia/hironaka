import Hironaka.Resolution.HironakaCurveAnalyticPredicates
import Hironaka.Resolution.HironakaEmbeddedAnalyticLocal
import Hironaka.Resolution.HironakaG8PlaneArrangementSingular

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8VariableCombArrangement

open HironakaEmbeddedAnalytic HironakaEmbeddedAnalyticLocal HironakaCurveAnalyticPredicates
open scoped BigOperators

abbrev Ambient := ComplexModel 3
abbrev Tooth := Σ k : ℕ, Fin (k+1)

private noncomputable def coord (i : Fin 3) : Ambient →L[ℂ] ℂ :=
  EuclideanSpace.proj (𝕜 := ℂ) i

noncomputable def slope (j : Tooth) : ℂ :=
  ((j.2.val : ℝ) / (4 * ((j.1+1 : ℕ) : ℝ)) : ℝ)

theorem slope_norm_le (j : Tooth) : ‖slope j‖ ≤ 1/4 := by
  have hn : (0 : ℝ) < (j.1+1 : ℕ) := by positivity
  have hj : (j.2.val : ℝ) ≤ (j.1+1 : ℕ) := by exact_mod_cast j.2.isLt.le
  have hpos : (0 : ℝ) ≤ (j.2.val : ℝ) / (4 * ((j.1+1 : ℕ) : ℝ)) := by positivity
  rw [slope,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hpos]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

/-- A locally finite tooth family with an increasing number of distinct
affine hyperplanes passing through each integer point of the common line. -/
def toothPlane (j : Tooth) : Set Ambient :=
  {z | z 2 = (j.1 : ℂ) + slope j * z 0}

def spine : Set Ambient := {z | z 0 = 0 ∧ z 1 = 0}

def comb : Set Ambient := {z | z 0 = 0} ∪ {z | z 1 = 0} ∪ ⋃ j, toothPlane j

private theorem analytic_equation (f : Ambient → ℂ) (hf : Differentiable ℂ f) :
    IsComplexAnalyticSubset (n := 3) {z | f z = 0} := by
  intro x
  refine ⟨⟨1,fun _ => f,univ,isOpen_univ,mem_univ _,?_,
    fun _ => hf.differentiableOn,?_⟩⟩
  · simp [complexChartAt,chartAt_self_eq]
  · intro z _ _
    simp [complexChartAt,chartAt_self_eq]

theorem analytic_toothPlane (j : Tooth) :
    IsComplexAnalyticSubset (n := 3) (toothPlane j) := by
  let f : Ambient → ℂ := fun z => coord 2 z - ((j.1 : ℂ) + slope j * coord 0 z)
  have hf : Differentiable ℂ f :=
    (coord 2).differentiable.sub
      ((differentiable_const _).add ((differentiable_const _).mul (coord 0).differentiable))
  convert analytic_equation f hf using 1
  ext z
  exact sub_eq_zero.symm

theorem locallyFinite_toothPlanes : LocallyFinite toothPlane := by
  intro z
  let U : Set Ambient := {w | ‖coord 0 w‖ < ‖coord 0 z‖+1} ∩
    {w | ‖coord 2 w‖ < ‖coord 2 z‖+1}
  have hOpen : IsOpen U :=
    (isOpen_lt (coord 0).continuous.norm continuous_const).inter
      (isOpen_lt (coord 2).continuous.norm continuous_const)
  have hz : z ∈ U := ⟨by dsimp; linarith,by dsimp; linarith⟩
  obtain ⟨K,hK⟩ := exists_nat_gt (‖coord 2 z‖+1 + (1/4) * (‖coord 0 z‖+1))
  let J : Finset Tooth := (Finset.range K).sigma (fun k => (Finset.univ : Finset (Fin (k+1))))
  refine ⟨U,hOpen.mem_nhds hz,J.finite_toSet.subset ?_⟩
  rintro j ⟨w,hw,hU⟩
  have hwEq : (j.1 : ℂ) = coord 2 w - slope j * coord 0 w := by
    change w 2 = (j.1 : ℂ) + slope j * w 0 at hw
    change (j.1 : ℂ) = w 2 - slope j * w 0
    rw [hw,add_sub_cancel_right]
  have h0 : ‖coord 0 w‖ < ‖coord 0 z‖+1 := hU.1
  have h2 : ‖coord 2 w‖ < ‖coord 2 z‖+1 := hU.2
  have hBound : ‖slope j‖ * ‖coord 0 w‖ ≤ (1/4) * (‖coord 0 z‖+1) :=
    mul_le_mul (slope_norm_le j) h0.le (norm_nonneg _) (by positivity)
  have hLt : (j.1 : ℝ) < (K : ℝ) := calc
    _ = ‖(j.1 : ℂ)‖ := (Complex.norm_natCast _).symm
    _ = ‖coord 2 w - slope j * coord 0 w‖ := congrArg norm hwEq
    _ ≤ ‖coord 2 w‖ + ‖slope j * coord 0 w‖ := norm_sub_le _ _
    _ ≤ ‖coord 2 w‖ + (1/4) * (‖coord 0 z‖+1) := by rw [norm_mul]; exact add_le_add_right hBound _
    _ < ‖coord 2 z‖+1 + (1/4) * (‖coord 0 z‖+1) := add_lt_add_left h2 _
    _ < _ := hK
  change j ∈ J
  simp only [J,Finset.mem_sigma,Finset.mem_univ,and_true,Finset.mem_range]
  exact_mod_cast hLt

theorem analytic_comb : IsComplexAnalyticSubset (n := 3) comb := by
  exact isComplexAnalyticSubset_union
    (isComplexAnalyticSubset_union (analytic_equation (coord 0) (coord 0).differentiable)
      (analytic_equation (coord 1) (coord 1).differentiable))
    (isComplexAnalyticSubset_iUnion_of_locallyFinite _ locallyFinite_toothPlanes analytic_toothPlane)

theorem spine_subset_comb : spine ⊆ comb := fun _ h => Or.inl (Or.inl h.1)

/-- The moving sheets meet the common line exactly at their integer
level, independently of which finite branch at that level is chosen. -/
theorem toothPlane_inter_spine (j : Tooth) :
    toothPlane j ∩ spine = {z | z 0 = 0 ∧ z 1 = 0 ∧ z 2 = (j.1 : ℂ)} := by
  ext z
  simp only [toothPlane,spine,mem_inter_iff,mem_ofPred_eq]
  constructor
  · rintro ⟨h2,h0,h1⟩
    exact ⟨h0,h1,by simpa [h0] using h2⟩
  · rintro ⟨h0,h1,h2⟩
    exact ⟨by simpa [h0] using h2,h0,h1⟩

theorem slope_injective_at (k : ℕ) : Function.Injective (fun j : Fin (k+1) => slope ⟨k,j⟩) := by
  intro a b h
  apply Fin.ext
  have h' := congrArg Complex.re h
  change (a.val : ℝ) / (4 * ((k+1 : ℕ) : ℝ)) =
    (b.val : ℝ) / (4 * ((k+1 : ℕ) : ℝ)) at h'
  have he := (div_left_inj' (by positivity : (4 * ((k+1 : ℕ) : ℝ)) ≠ 0)).mp h'
  exact_mod_cast he

/-- Distinct branches within a stack intersect exactly in the common
axis of that stack. The extra fixed plane cuts this axis at its tooth. -/
theorem two_toothPlanes_inter {k : ℕ} {a b : Fin (k+1)} (hab : a ≠ b) :
    toothPlane ⟨k,a⟩ ∩ toothPlane ⟨k,b⟩ = {z | z 0 = 0 ∧ z 2 = (k : ℂ)} := by
  ext z
  simp only [toothPlane,mem_inter_iff,mem_ofPred_eq]
  constructor
  · intro ⟨ha,hb⟩
    have hEq : slope ⟨k,a⟩ * z 0 = slope ⟨k,b⟩ * z 0 := add_left_cancel (ha.symm.trans hb)
    have h0 : z 0 = 0 := by
      by_contra hn
      exact hab (slope_injective_at k (mul_right_cancel₀ hn hEq))
    exact ⟨h0,by simpa [h0] using ha⟩
  · rintro ⟨h0,hz⟩
    simp [h0,hz]

end Hironaka.HironakaG8VariableCombArrangement

#print axioms Hironaka.HironakaG8VariableCombArrangement.analytic_comb
