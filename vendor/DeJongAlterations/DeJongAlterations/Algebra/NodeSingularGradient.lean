import DeJongAlterations.Algebra.NodeNonsplitQuadratic

/-!
# The actual nonsplit quadratic gradient ideal

The inverse of the original discriminant recovers the original coordinates
from the two actual gradients, with no division by two.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeSingular

open NodeNonsplit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R]

/-- The first original quadratic gradient. -/
def leftGradient (Q : Quadratic R) (x y : R) : R :=
  2 * Q.a0 * x + Q.a1 * y

/-- The second original quadratic gradient. -/
def rightGradient (Q : Quadratic R) (x y : R) : R :=
  Q.a1 * x + 2 * Q.a2 * y

/-- The actual inverse Hessian recovers the first coordinate. -/
theorem recover_left (Q : Quadratic R) (x y : R) :
    Q.left (leftGradient Q x y) (rightGradient Q x y) = x := by
  calc
    _ = (Q.invDiscriminant * (Q.a1 ^ 2 - 4 * Q.a0 * Q.a2)) * x := by
      unfold Quadratic.left leftGradient rightGradient
      ring
    _ = x := by rw [Q.inverse_discriminant, one_mul]

/-- The actual inverse Hessian recovers the second coordinate. -/
theorem recover_right (Q : Quadratic R) (x y : R) :
    Q.right (leftGradient Q x y) (rightGradient Q x y) = y := by
  calc
    _ = (Q.invDiscriminant * (Q.a1 ^ 2 - 4 * Q.a0 * Q.a2)) * y := by
      unfold Quadratic.right leftGradient rightGradient
      ring
    _ = y := by rw [Q.inverse_discriminant, one_mul]

/-- The two actual gradients generate precisely the original coordinate ideal. -/
theorem gradientIdeal_eq_coordinateIdeal (Q : Quadratic R) (x y : R) :
    Ideal.span {leftGradient Q x y, rightGradient Q x y} = Ideal.span {x, y} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro z (rfl | rfl)
    · exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  · let J : Ideal R := Ideal.span {leftGradient Q x y, rightGradient Q x y}
    have h0 : leftGradient Q x y ∈ J := Ideal.subset_span (by simp)
    have h1 : rightGradient Q x y ∈ J := Ideal.subset_span (by simp)
    apply Ideal.span_le.mpr
    intro z hz
    change z ∈ J
    rcases Set.mem_insert_iff.mp hz with hz | hz
    · rw [hz]
      have hm : Q.left (leftGradient Q x y) (rightGradient Q x y) ∈ J :=
        J.mul_mem_left _ (J.sub_mem (J.mul_mem_left _ h1) (J.mul_mem_left _ h0))
      simpa only [recover_left, J] using hm
    · have hz' : z = y := Set.mem_singleton_iff.mp hz
      rw [hz']
      have hm : Q.right (leftGradient Q x y) (rightGradient Q x y) ∈ J :=
        J.mul_mem_left _ (J.sub_mem (J.mul_mem_left _ h0) (J.mul_mem_left _ h1))
      simpa only [recover_right, J] using hm

end DeJongAlterations.Algebra.NodeSingular
