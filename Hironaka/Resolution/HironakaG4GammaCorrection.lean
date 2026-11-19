import Hironaka.Resolution.HironakaG4NormalDerivative

/-! Extract a normal correction from a unit-times-vanishing-product trace. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG4GammaCorrection
noncomputable section
open Hironaka.BlowupSequences NormalCrossings HironakaG4NormalDerivative

variable {n : ℕ}

/-- If the selected smooth equation restricts to a unit times a product of
two vanishing factors, subtracting that product after division by the unit
gives a correction vanishing on the carrier with a nonzero normal partial. -/
theorem exists_gamma_normal_correction {f a d : ComplexModel n → ℂ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (h0 : (0 : ComplexModel n) ∈ U)
    (hf : DifferentiableOn ℂ f U) (ha : DifferentiableOn ℂ a U) (hd : DifferentiableOn ℂ d U)
    (hf0 : f 0 = 0) (ha0 : a 0 ≠ 0) (hd0 : d 0 = 0)
    (hdf : fderiv ℂ f 0 ≠ 0) (S : Finset (Fin n)) (t : Fin n)
    (htrace : ∀ z ∈ U, z ∈ coordSubspace S → f z = a z * (z t * d z)) :
    ∃ (V : Set (ComplexModel n)) (g : ComplexModel n → ℂ) (s : Fin n),
      IsOpen V ∧ (0 : ComplexModel n) ∈ V ∧ V ⊆ U ∧ DifferentiableOn ℂ g V ∧ g 0 = 0 ∧
      s ∈ S ∧ fderiv ℂ g 0 (EuclideanSpace.single s 1) ≠ 0 ∧
      (∀ z ∈ V, z ∈ coordSubspace S → g z = 0) ∧
      ∀ z ∈ V, f z = a z * (g z + z t * d z) := by
  let V : Set (ComplexModel n) := U ∩ {z | a z ≠ 0}
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have haAt := (ha z hz.1).differentiableAt (hU.mem_nhds hz.1)
    filter_upwards [hU.mem_nhds hz.1, haAt.continuousAt.eventually_ne hz.2] with w hw hw'
    exact ⟨hw, hw'⟩
  have h0V : (0 : ComplexModel n) ∈ V := ⟨h0, ha0⟩
  let q : ComplexModel n → ℂ := fun z => z t * d z
  let g : ComplexModel n → ℂ := fun z => f z / a z - q z
  have hq : DifferentiableOn ℂ q V := by
    intro z hz
    exact ((EuclideanSpace.proj t).differentiableAt.mul
      ((hd z hz.1).differentiableAt (hU.mem_nhds hz.1))).differentiableWithinAt
  have hg : DifferentiableOn ℂ g V := by
    intro z hz
    have hfAt : DifferentiableAt ℂ f z := (hf z hz.1).differentiableAt (hU.mem_nhds hz.1)
    have haAt : DifferentiableAt ℂ a z := (ha z hz.1).differentiableAt (hU.mem_nhds hz.1)
    have hqAt : DifferentiableAt ℂ q z := (hq z hz).differentiableAt (hV.mem_nhds hz)
    change DifferentiableWithinAt ℂ (fun z => f z * (a z)⁻¹ - q z) V z
    exact (hfAt.mul (haAt.inv hz.2) |>.sub hqAt).differentiableWithinAt
  have hg0 : g 0 = 0 := by simp [g, q, hf0]
  have hvan : ∀ z ∈ V, z ∈ coordSubspace S → g z = 0 := by
    intro z hz hzS
    dsimp only [g]
    rw [htrace z hz.1 hzS]
    dsimp [q]
    have hne : a z ≠ 0 := hz.2
    field_simp [hne]; ring
  have hqderiv : fderiv ℂ q 0 = 0 := by
    ext v
    change fderiv ℂ (fun z : ComplexModel n => (EuclideanSpace.proj t) z * d z) 0 v = 0
    rw [fderiv_fun_mul (EuclideanSpace.proj t).differentiableAt
      ((hd 0 h0).differentiableAt (hU.mem_nhds h0))]
    simp [hd0]
  have hgd : DifferentiableAt ℂ g 0 := (hg 0 h0V).differentiableAt (hV.mem_nhds h0V)
  have hgd_ne : fderiv ℂ g 0 ≠ 0 := by
    intro hzero
    have haD := (ha 0 h0).differentiableAt (hU.mem_nhds h0)
    have hqAt := (hq 0 h0V).differentiableAt (hV.mem_nhds h0V)
    have hprod0 : fderiv ℂ (fun z => a z * (g z + q z)) 0 = 0 := by
      ext v
      change fderiv ℂ (fun z => a z * (g + q) z) 0 v = 0
      rw [fderiv_fun_mul haD (hgd.add hqAt), fderiv_add hgd hqAt]
      simp [hg0, q, hqderiv, hzero]
    have heq : (fun z => a z * (g z + q z)) =ᶠ[𝓝 0] f := by
      filter_upwards [hV.mem_nhds h0V] with z hz
      dsimp [g]
      have hne : a z ≠ 0 := hz.2
      field_simp [hne]; ring
    exact hdf (heq.fderiv_eq.symm.trans hprod0)
  obtain ⟨s, hs, hsne⟩ := exists_nonzero_normal_partial hV h0V hgd S hvan hgd_ne
  refine ⟨V, g, s, hV, h0V, inter_subset_left, hg, hg0, hs, hsne, hvan, ?_⟩
  intro z hz
  dsimp [g, q]
  have hne : a z ≠ 0 := hz.2
  field_simp [hne]; ring

end
end Hironaka.HironakaG4GammaCorrection
