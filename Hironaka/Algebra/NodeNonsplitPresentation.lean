import Hironaka.Algebra.NodeNonsplitPresentationKernel
import Hironaka.Algebra.NodeNonsplitComplete

/-!
# The actual flat complete quadratic-nodal hypersurface presentation

The only model input is the actual quadratic nodal closed fibre. The original
coefficient map, complete evaluation, surjectivity, and principal kernel are
all constructed internally. Complete nonsplit Morse correction gives the literal
constant-parameter normal form of de Jong §2.23 in this quadratic, equal-residue case.
-/

noncomputable section

namespace Hironaka.Algebra.NodeNonsplit

open MvPowerSeries IsLocalRing NodeFormalMorse NodeFlatPresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsAdicComplete (maximalIdeal A) A]
  (B : Type v) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
  [IsAdicComplete (maximalIdeal B) B]
  (Q : Quadratic A)

/-- The actual error lifted internally from the original flat map and closed-fibre model. -/
def presentationError
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    MvPowerSeries (Fin 2) A := Classical.choose (exists_error_kernel A B Q e)

theorem presentationError_coeff_mem
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (d) :
    coeff d (presentationError A B Q e) ∈ maximalIdeal A :=
  (Classical.choose_spec (exists_error_kernel A B Q e)).1 d

theorem presentationMap_kernel
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    RingHom.ker (presentationMap A B Q e).toRingHom =
      Ideal.span {Q.series - presentationError A B Q e} :=
  (Classical.choose_spec (exists_error_kernel A B Q e)).2

/-- The actual presentation isomorphism induced by the original coefficient-preserving evaluation. -/
def presentationEquiv
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    (MvPowerSeries (Fin 2) A ⧸
      Ideal.span {Q.series - presentationError A B Q e}) ≃ₐ[A] B :=
  (Ideal.quotientEquivAlgOfEq A (presentationMap_kernel A B Q e).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (presentationMap_surjective A B Q e))

@[simp]
theorem presentationEquiv_mk
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B)
    (f : MvPowerSeries (Fin 2) A) :
    presentationEquiv A B Q e (Ideal.Quotient.mk _ f) = presentationMap A B Q e f := by
  unfold presentationEquiv
  simp only [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  rfl

@[simp]
theorem presentationEquiv_coordinate
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (i : Fin 2) :
    presentationEquiv A B Q e (Ideal.Quotient.mk _ (X i)) = coordinateLifts A B Q e i := by
  rw [presentationEquiv_mk, presentationMap_X]

/-- The actual constant parameter constructed by complete Morse iteration. -/
def normalFormParameter
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) : A :=
  NodeNonsplit.completeParameter Q (maximalIdeal A) (presentationError A B Q e)
    (presentationError_coeff_mem A B Q e)

theorem normalFormParameter_mem
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    normalFormParameter A B Q e ∈ maximalIdeal A :=
  NodeNonsplit.completeParameter_mem Q (maximalIdeal A) (presentationError A B Q e)
    (presentationError_coeff_mem A B Q e)

/-- The literal quadratic completed normal form over the original coefficient ring. -/
def normalFormEquiv
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    B ≃ₐ[A] (MvPowerSeries (Fin 2) A ⧸
      Ideal.span {Q.series - C (normalFormParameter A B Q e)}) :=
  (presentationEquiv A B Q e).symm.trans
    (Ideal.quotientEquivAlg _ _
      (NodeNonsplit.completeEquiv Q (maximalIdeal A) (presentationError A B Q e)
        (presentationError_coeff_mem A B Q e)) (by
      rw [Ideal.map_span, Set.image_singleton]
      apply congrArg Ideal.span
      apply congrArg Set.singleton
      change Q.series - C (normalFormParameter A B Q e) =
        NodeNonsplit.completeEquiv Q (maximalIdeal A) (presentationError A B Q e)
          (presentationError_coeff_mem A B Q e) (Q.series - presentationError A B Q e)
      exact (NodeNonsplit.completeEquiv_equation Q (maximalIdeal A) (presentationError A B Q e)
        (presentationError_coeff_mem A B Q e)).symm))

/-- The original coefficient map is preserved by the actual normal-form isomorphism. -/
@[simp]
theorem normalFormEquiv_coefficient
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (a : A) :
    normalFormEquiv A B Q e (algebraMap A B a) =
      Ideal.Quotient.mk _ (C a) := (normalFormEquiv A B Q e).commutes a

/-- No hypersurface presentation or completion equivalence is supplied as an output premise. -/
theorem exists_quadratic_normal_form
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    ∃ h : A, h ∈ maximalIdeal A ∧
      Nonempty (B ≃ₐ[A] (MvPowerSeries (Fin 2) A ⧸ Ideal.span {Q.series - C h})) :=
  ⟨normalFormParameter A B Q e, normalFormParameter_mem A B Q e, ⟨normalFormEquiv A B Q e⟩⟩

/-- The original source hypotheses on the three chosen lifts produce the same-ring normal form. -/
theorem exists_original_quadratic_normal_form (a0 a1 a2 : A)
    (hΔ : (residue A a1) ^ 2 - 4 * residue A a0 * residue A a2 ≠ 0)
    (e : (MvPowerSeries (Fin 2) (CoefficientResidue A) ⧸ Ideal.span {
      C (Ideal.Quotient.mk (maximalIdeal A) a0) * X 0 ^ 2 +
      C (Ideal.Quotient.mk (maximalIdeal A) a1) * X 0 * X 1 +
      C (Ideal.Quotient.mk (maximalIdeal A) a2) * X 1 ^ 2}) ≃ₐ[CoefficientResidue A]
        ClosedFiber A B) :
    ∃ h : A, h ∈ maximalIdeal A ∧ Nonempty (B ≃ₐ[A]
      (MvPowerSeries (Fin 2) A ⧸ Ideal.span {
        C a0 * X 0 ^ 2 + C a1 * X 0 * X 1 + C a2 * X 1 ^ 2 - C h})) := by
  let T : Quadratic A := Quadratic.ofCoefficients a0 a1 a2 (unit_discriminant_of_residue a0 a1 a2 hΔ)
  have he : QuadraticNode (T.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A]
      ClosedFiber A B := e
  exact exists_quadratic_normal_form A B T he

end Hironaka.Algebra.NodeNonsplit
