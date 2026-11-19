import Hironaka.Algebra.NodeNonsplitPresentation

/-! # Internal lifts of the SAME actual residue quadratic, with its discriminant unit -/

noncomputable section

namespace Hironaka.Algebra.NodeEtaleQuadraticLift

open IsLocalRing NodeNonsplit

universe u
variable (T : Type u) [CommRing T] [IsLocalRing T] (Q : Quadratic (ResidueField T))

/-- The first original coefficient is lifted through the SAME native residue map. -/
def coefficient0 : T := Classical.choose (residue_surjective Q.a0)
/-- The middle original coefficient is lifted through the SAME native residue map. -/
def coefficient1 : T := Classical.choose (residue_surjective Q.a1)
/-- The last original coefficient is lifted through the SAME native residue map. -/
def coefficient2 : T := Classical.choose (residue_surjective Q.a2)

theorem coefficient0_residue : residue T (coefficient0 T Q) = Q.a0 :=
  Classical.choose_spec (residue_surjective Q.a0)
theorem coefficient1_residue : residue T (coefficient1 T Q) = Q.a1 :=
  Classical.choose_spec (residue_surjective Q.a1)
theorem coefficient2_residue : residue T (coefficient2 T Q) = Q.a2 :=
  Classical.choose_spec (residue_surjective Q.a2)

/-- The original inverse identity proves the actual native residue discriminant is nonzero. -/
theorem discriminant_ne_zero : Q.a1 ^ 2 - 4 * Q.a0 * Q.a2 ≠ 0 := by
  intro h
  have hi := Q.inverse_discriminant
  rw [h, mul_zero] at hi
  exact zero_ne_one hi

/-- No lifted unit hypothesis is supplied: it is produced from these SAME actual three coefficient lifts. -/
theorem liftedDiscriminant_unit :
    IsUnit ((coefficient1 T Q) ^ 2 - 4 * coefficient0 T Q * coefficient2 T Q) := by
  apply unit_discriminant_of_residue
  rw [coefficient0_residue, coefficient1_residue, coefficient2_residue]
  exact discriminant_ne_zero T Q

/-- The SAME actual lifted quadratic, including its internally obtained actual inverse discriminant. -/
def lift : Quadratic T :=
  Quadratic.ofCoefficients (coefficient0 T Q) (coefficient1 T Q) (coefficient2 T Q)
    (liftedDiscriminant_unit T Q)

/-- The ENTIRE actual native reduction is the SAME original residue quadratic. -/
theorem lift_reduction : (lift T Q).map (residue T) = Q := by
  have h0 : residue T (lift T Q).a0 = Q.a0 := coefficient0_residue T Q
  have h1 : residue T (lift T Q).a1 = Q.a1 := coefficient1_residue T Q
  have h2 : residue T (lift T Q).a2 = Q.a2 := coefficient2_residue T Q
  apply Quadratic.ext
  · exact h0
  · exact h1
  · exact h2
  · apply mul_right_cancel₀ (discriminant_ne_zero T Q)
    have h := ((lift T Q).map (residue T)).inverse_discriminant
    change residue T (lift T Q).invDiscriminant *
      (residue T (lift T Q).a1 ^ 2 - 4 * residue T (lift T Q).a0 * residue T (lift T Q).a2) = 1 at h
    rw [h0, h1, h2] at h
    exact h.trans Q.inverse_discriminant.symm

end Hironaka.Algebra.NodeEtaleQuadraticLift
