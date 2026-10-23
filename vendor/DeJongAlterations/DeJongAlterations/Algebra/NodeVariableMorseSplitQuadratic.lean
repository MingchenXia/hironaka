import DeJongAlterations.Algebra.NodeVariableMorseLinear
import DeJongAlterations.Algebra.NodeVariableMorseFactors

/-!
# The same original quadratic split over its actual algebraically closed extension

This constructs the actual coordinate automorphism and the actual literal
quotient equivalence. It supplies no descent of an arbitrary original
geometric node to a quadratic model over its original residue field.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeVariableMorse

open NodeNonsplit NodeFormalMorse MvPowerSeries

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {K : Type u} [Field K] [IsAlgClosed K]

/-- The actual substitution by the internally constructed independent factors. -/
def factorLinearEquiv (Q : Quadratic K) : Series K ≃ₐ[K] Series K :=
  let F := quadraticFactors Q
  linearEquiv F.a F.b F.c F.d F.determinant_ne_zero

/-- Its actual product image is precisely the same original quadratic series. -/
theorem factorLinearEquiv_product (Q : Quadratic K) :
    factorLinearEquiv Q ((X 0 : Series K) * X 1) = Q.series := by
  let F := quadraticFactors Q
  change linearEquiv F.a F.b F.c F.d F.determinant_ne_zero ((X 0 : Series K) * X 1) = _
  rw [map_mul, linearEquiv_apply, linearEquiv_apply, linearSubstitution_X, linearSubstitution_X]
  change (C F.a * X 0 + C F.b * X 1) * (C F.c * X 0 + C F.d * X 1) = Q.series
  calc
    _ = C (F.a * F.c) * X 0 ^ 2 + C (F.a * F.d + F.b * F.c) * X 0 * X 1 +
        C (F.b * F.d) * X 1 ^ 2 := by
      simp only [map_mul, map_add]
      ring
    _ = Q.series := by
      rw [F.first_coefficient, F.middle_coefficient, F.last_coefficient]
      rfl

/-- The actual internally constructed automorphism taking the original quadratic to the split product. -/
def splitQuadraticEquiv (Q : Quadratic K) : Series K ≃ₐ[K] Series K :=
  (factorLinearEquiv Q).symm

/-- The same original quadratic, without rescaling its equation, goes to the literal split node. -/
theorem splitQuadraticEquiv_quadratic (Q : Quadratic K) :
    splitQuadraticEquiv Q Q.series = (X 0 : Series K) * X 1 := by
  change (factorLinearEquiv Q).symm Q.series = _
  rw [← factorLinearEquiv_product Q, AlgEquiv.symm_apply_apply]

@[simp]
theorem splitQuadraticEquiv_coefficient (Q : Quadratic K) (a : K) :
    splitQuadraticEquiv Q (C a) = C a := by
  simpa only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using
    (splitQuadraticEquiv Q).commutes a

variable {k : Type v} [Field k] (ρ : k →+* K)

/-- The automorphism for the literal original quadratic under the actual given field map. -/
def extendedQuadraticSplitEquiv (Q : Quadratic k) : Series K ≃ₐ[K] Series K :=
  splitQuadraticEquiv (Q.map ρ)

/-- The original quadratic coefficient triangle is the actual native series coefficient map. -/
theorem extendedQuadraticSplitEquiv_quadratic (Q : Quadratic k) :
    extendedQuadraticSplitEquiv ρ Q (MvPowerSeries.map ρ Q.series) =
      (X 0 : Series K) * X 1 := by
  rw [Quadratic.map_series]
  exact splitQuadraticEquiv_quadratic _

/-- Every actual original coefficient is fixed through the original field map. -/
@[simp]
theorem extendedQuadraticSplitEquiv_coefficient (Q : Quadratic k) (a : k) :
    extendedQuadraticSplitEquiv ρ Q (C (ρ a)) = C (ρ a) :=
  splitQuadraticEquiv_coefficient _ _

/-- The actual literal hypersurface quotient equivalence induced by the actual coordinate automorphism. -/
def extendedQuadraticQuotientEquiv (Q : Quadratic k) :
    (Series K ⧸ Ideal.span {MvPowerSeries.map ρ Q.series}) ≃ₐ[K]
      (Series K ⧸ Ideal.span {(X 0 : Series K) * X 1}) :=
  Ideal.quotientEquivAlg _ _ (extendedQuadraticSplitEquiv ρ Q) (by
    rw [Ideal.map_span, Set.image_singleton]
    apply congrArg Ideal.span
    apply congrArg Set.singleton
    change (X 0 : Series K) * X 1 = extendedQuadraticSplitEquiv ρ Q (MvPowerSeries.map ρ Q.series)
    exact (extendedQuadraticSplitEquiv_quadratic ρ Q).symm)

/-- The whole actual original series quotient triangle. -/
@[simp]
theorem extendedQuadraticQuotientEquiv_mk (Q : Quadratic k) (f : Series K) :
    extendedQuadraticQuotientEquiv ρ Q
      (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ρ Q.series}) f) =
        Ideal.Quotient.mk (Ideal.span {(X 0 : Series K) * X 1})
          (extendedQuadraticSplitEquiv ρ Q f) := rfl

/-- The actual original coefficient quotient triangle. -/
@[simp]
theorem extendedQuadraticQuotientEquiv_coefficient (Q : Quadratic k) (a : k) :
    extendedQuadraticQuotientEquiv ρ Q
      (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.map ρ Q.series}) (C (ρ a))) =
        Ideal.Quotient.mk (Ideal.span {(X 0 : Series K) * X 1}) (C (ρ a)) := by
  rw [extendedQuadraticQuotientEquiv_mk, extendedQuadraticSplitEquiv_coefficient]

end DeJongAlterations.Algebra.NodeVariableMorse
