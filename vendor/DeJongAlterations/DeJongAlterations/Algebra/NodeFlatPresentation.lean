import DeJongAlterations.Algebra.NodeFlatPresentationKernel
import DeJongAlterations.Algebra.NodeFormalMorseComplete

/-!
# The actual flat complete split-nodal hypersurface presentation

The only model input is the actual split nodal closed fibre. The original
coefficient map, complete evaluation, surjectivity, and principal kernel are
all constructed internally. Complete Morse correction gives the literal
constant-parameter normal form of de Jong §2.23 in this split, equal-residue case.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFlatPresentation

open MvPowerSeries IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsAdicComplete (maximalIdeal A) A]
  (B : Type v) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
  [IsAdicComplete (maximalIdeal B) B]

/-- The actual error lifted internally from the original flat map and closed-fibre model. -/
def presentationError
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    MvPowerSeries (Fin 2) A := Classical.choose (exists_error_kernel A B e)

theorem presentationError_coeff_mem
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (d) :
    coeff d (presentationError A B e) ∈ maximalIdeal A :=
  (Classical.choose_spec (exists_error_kernel A B e)).1 d

theorem presentationMap_kernel
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    RingHom.ker (presentationMap A B e).toRingHom =
      Ideal.span {X (0 : Fin 2) * X 1 - presentationError A B e} :=
  (Classical.choose_spec (exists_error_kernel A B e)).2

/-- The actual presentation isomorphism induced by the original coefficient-preserving evaluation. -/
def presentationEquiv
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    (MvPowerSeries (Fin 2) A ⧸
      Ideal.span {X (0 : Fin 2) * X 1 - presentationError A B e}) ≃ₐ[A] B :=
  (Ideal.quotientEquivAlgOfEq A (presentationMap_kernel A B e).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (presentationMap_surjective A B e))

@[simp]
theorem presentationEquiv_mk
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B)
    (f : MvPowerSeries (Fin 2) A) :
    presentationEquiv A B e (Ideal.Quotient.mk _ f) = presentationMap A B e f := by
  unfold presentationEquiv
  simp only [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  rfl

@[simp]
theorem presentationEquiv_coordinate
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (i : Fin 2) :
    presentationEquiv A B e (Ideal.Quotient.mk _ (X i)) = coordinateLifts A B e i := by
  rw [presentationEquiv_mk, presentationMap_X]

/-- The actual constant parameter constructed by complete Morse iteration. -/
def normalFormParameter
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) : A :=
  NodeFormalMorse.completeParameter (maximalIdeal A) (presentationError A B e)
    (presentationError_coeff_mem A B e)

theorem normalFormParameter_mem
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    normalFormParameter A B e ∈ maximalIdeal A :=
  NodeFormalMorse.completeParameter_mem (maximalIdeal A) (presentationError A B e)
    (presentationError_coeff_mem A B e)

/-- The literal split completed normal form over the original coefficient ring. -/
def normalFormEquiv
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    B ≃ₐ[A] (MvPowerSeries (Fin 2) A ⧸
      Ideal.span {X (0 : Fin 2) * X 1 - C (normalFormParameter A B e)}) :=
  (presentationEquiv A B e).symm.trans
    (Ideal.quotientEquivAlg _ _
      (NodeFormalMorse.completeEquiv (maximalIdeal A) (presentationError A B e)
        (presentationError_coeff_mem A B e)) (by
      rw [Ideal.map_span, Set.image_singleton]
      apply congrArg Ideal.span
      apply congrArg Set.singleton
      change X 0 * X 1 - C (normalFormParameter A B e) =
        NodeFormalMorse.completeEquiv (maximalIdeal A) (presentationError A B e)
          (presentationError_coeff_mem A B e) (X 0 * X 1 - presentationError A B e)
      exact (NodeFormalMorse.completeEquiv_equation (maximalIdeal A) (presentationError A B e)
        (presentationError_coeff_mem A B e)).symm))

/-- The original coefficient map is preserved by the actual normal-form isomorphism. -/
@[simp]
theorem normalFormEquiv_coefficient
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (a : A) :
    normalFormEquiv A B e (algebraMap A B a) =
      Ideal.Quotient.mk _ (C a) := (normalFormEquiv A B e).commutes a

/-- No hypersurface presentation or completion equivalence is supplied as an output premise. -/
theorem exists_split_normal_form
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    ∃ h : A, h ∈ maximalIdeal A ∧
      Nonempty (B ≃ₐ[A] (MvPowerSeries (Fin 2) A ⧸ Ideal.span {X (0 : Fin 2) * X 1 - C h})) :=
  ⟨normalFormParameter A B e, normalFormParameter_mem A B e, ⟨normalFormEquiv A B e⟩⟩

end DeJongAlterations.Algebra.NodeFlatPresentation
