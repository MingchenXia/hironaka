import Hironaka.Resolution.HironakaG8NativeCuspDiagram

/-! A local adapted generator change preserving degree-one/two compression. -/
set_option autoImplicit false
open Set
namespace Hironaka.HironakaG8WeightOneTwoGeneratorChange

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A change of order-one generator by the order-two generator preserves
the weighted pair when the new order-two generator has no linear normal
remainder. All comparisons happen in the actual local ring. -/
theorem span_weight_one_two_of_adapted_change
    {z f u v c d : R} (hf : f ∈ IsLocalRing.maximalIdeal R)
    (hz : z ∈ IsLocalRing.maximalIdeal R) (hu : IsUnit u) (hd : IsUnit d) :
    Ideal.span ({(u*z+v*f)^2, c*z^2+d*f} : Set R) = Ideal.span ({z^2,f} : Set R) := by
  let A : Ideal R := Ideal.span ({(u*z+v*f)^2, c*z^2+d*f} : Set R)
  let B : Ideal R := Ideal.span ({z^2,f} : Set R)
  let e := 2*u*z*v + v^2*f
  let Δ := u^2*d - c*e
  have he : e ∈ IsLocalRing.maximalIdeal R := by
    apply Ideal.add_mem
    · rw [show 2*u*z*v = (2*u*v)*z by ring]
      exact Ideal.mul_mem_left _ _ hz
    · exact Ideal.mul_mem_left _ _ hf
  have hΔ : IsUnit Δ := by
    apply Classical.byContradiction
    intro hNot
    have hΔ : Δ ∈ IsLocalRing.maximalIdeal R := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hNot
    have hm := (IsLocalRing.maximalIdeal R).add_mem hΔ
      ((IsLocalRing.maximalIdeal R).mul_mem_left c he)
    have hm' : u^2*d ∈ IsLocalRing.maximalIdeal R := by
      change (u^2*d - c*e) + c*e ∈ IsLocalRing.maximalIdeal R at hm
      rwa [sub_add_cancel] at hm
    have hNotUnit : ¬ IsUnit (u^2*d) := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hm'
    exact hNotUnit ((hu.pow _).mul hd)
  have ha : (u*z+v*f)^2 ∈ A := Ideal.subset_span (by simp)
  have hb : c*z^2+d*f ∈ A := Ideal.subset_span (by simp)
  have hzB : z^2 ∈ B := Ideal.subset_span (by simp)
  have hfB : f ∈ B := Ideal.subset_span (by simp)
  have heq : (u*z+v*f)^2 = u^2*z^2 + e*f := by dsimp [e]; ring
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro g hg
    rcases (show g = (u*z+v*f)^2 ∨ g = c*z^2+d*f by simpa using hg) with rfl | rfl
    · rw [heq]
      exact B.add_mem (B.mul_mem_left _ hzB) (B.mul_mem_left _ hfB)
    · exact B.add_mem (B.mul_mem_left _ hzB) (B.mul_mem_left _ hfB)
  · have hZ : Δ * z^2 ∈ A := by
      rw [show Δ*z^2 = d*(u*z+v*f)^2 - e*(c*z^2+d*f) by rw [heq]; dsimp [Δ]; ring]
      exact A.sub_mem (A.mul_mem_left _ ha) (A.mul_mem_left _ hb)
    have hF : Δ * f ∈ A := by
      rw [show Δ*f = u^2*(c*z^2+d*f) - c*(u*z+v*f)^2 by rw [heq]; dsimp [Δ]; ring]
      exact A.sub_mem (A.mul_mem_left _ hb) (A.mul_mem_left _ ha)
    apply Ideal.span_le.mpr
    intro g hg
    have hMul : Δ * g ∈ A := by
      rcases (show g = z^2 ∨ g = f by simpa using hg) with rfl | rfl
      · exact hZ
      · exact hF
    obtain ⟨a, ha⟩ := hΔ
    have hm := A.mul_mem_left (↑a⁻¹ : R) hMul
    rwa [← mul_assoc, ← ha, Units.inv_mul, one_mul] at hm

end Hironaka.HironakaG8WeightOneTwoGeneratorChange
