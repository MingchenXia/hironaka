import Hironaka.Geometry.CurveFibrationGenericSmoothMarksPoints
import Mathlib.AlgebraicGeometry.ResidueField

/-! The native residue fields of the ORIGINAL marks, with their original coefficients. -/

open CategoryTheory AlgebraicGeometry IsLocalRing
noncomputable section
universe u

namespace Hironaka.Geometry.CurveFibrationGenericSmoothMarks

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- The actual ORIGINAL coefficient map of the native residue-field point. -/
def residueCoefficient (p : C ⟶ Spec (.of k)) (x : C) :
    CommRingCat.of k ⟶ C.residueField x :=
  Spec.preimage (C.fromSpecResidueField x ≫ p)

/-- The native residue field carries precisely the original coefficient action. -/
@[instance_reducible]
def residueAlgebra (p : C ⟶ Spec (.of k)) (x : C) : Algebra k (C.residueField x) :=
  (residueCoefficient p x).hom.toAlgebra

/-- A finite separable ORIGINAL field point has finite separable ACTUAL residue field,
with the coefficient action of its canonical original residue-field point. -/
theorem finite_separable_residue_of_field_point (p : C ⟶ Spec (.of k))
    {E : Type u} [Field E] [Algebra k E] [FiniteDimensional k E]
    [Algebra.IsSeparable k E] (q : Spec (.of E) ⟶ C)
    (hq : q ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k E))) :
    let x := q (closedPoint E)
    let := residueAlgebra p x
    FiniteDimensional k (C.residueField x) ∧ Algebra.IsSeparable k (C.residueField x) := by
  let x := q (closedPoint E)
  let := residueAlgebra p x
  let γ : C.residueField x ⟶ CommRingCat.of E :=
    C.descResidueField (Scheme.stalkClosedPointTo q)
  have hγ : Spec.map γ ≫ C.fromSpecResidueField x = q :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField E C q
  have hco : residueCoefficient p x ≫ γ = CommRingCat.ofHom (algebraMap k E) := by
    apply Spec.map_injective
    rw [Spec.map_comp, residueCoefficient, Spec.map_preimage, ← Category.assoc, hγ, hq]
  let χ : C.residueField x →ₐ[k] E :=
    { γ.hom with
      commutes' c := congrArg (fun g : CommRingCat.of k ⟶ CommRingCat.of E => g c) hco }
  exact ⟨FiniteDimensional.of_injective χ.toLinearMap χ.injective,
    Algebra.IsSeparable.of_algHom k E χ⟩

/-- EACH internally chosen original smooth mark has finite separable native residue field. -/
theorem point_residue_finite_separable {p : C ⟶ Spec (.of k)} {U : C.Opens}
    (z : Point p U) :
    let := residueAlgebra p (point z)
    FiniteDimensional k (C.residueField (point z)) ∧
      Algebra.IsSeparable k (C.residueField (point z)) := by
  let := z.finite
  let := z.separable
  have h := finite_separable_residue_of_field_point p z.map z.over
  dsimp only at h
  have hx : closedPoint z.extension = (⊥ : PrimeSpectrum z.extension) :=
    Subsingleton.elim _ _
  rw [hx] at h
  exact h

end Hironaka.Geometry.CurveFibrationGenericSmoothMarks
