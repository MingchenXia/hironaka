import DeJongAlterations.Algebra.NodeEtaleCoefficientsResidue
import Mathlib.RingTheory.Henselian

/-! # The actual Hensel root lifts the original residue extension into the original complete ring -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeEtaleCoefficients

open IsLocalRing Polynomial
open DeJongAlterations.Algebra.ResidueExtensionLift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

attribute [local instance] residueAlgebra idealResidueAlgebra

variable [FiniteDimensional (ResidueField A) (ResidueField B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  [IsAdicComplete (maximalIdeal B) B]

/-- The coefficient polynomial is chosen from the original canonical residue extension. -/
abbrev coefficientPolynomial : A[X] := liftPolynomial (maximalIdeal A) (ResidueField B)

/-- The actual coefficient algebra, with no étale/local/complete replacement supplied as input. -/
abbrev CoefficientRing := Coefficients A (ResidueField B)

omit [IsAdicComplete (maximalIdeal B) B] in
/-- The original coefficient polynomial reduces to the original primitive minimal polynomial in B. -/
theorem coefficientPolynomial_residue :
    ((coefficientPolynomial A B).map (algebraMap A B)).map (residue B) =
      (residuePolynomial (maximalIdeal A) (ResidueField B)).map
        (algebraMap (maximalIdeal A).ResidueField (ResidueField B)) := by
  rw [← liftPolynomial_map, Polynomial.map_map, Polynomial.map_map]
  apply congrArg (fun f : A →+* ResidueField B => (coefficientPolynomial A B).map f)
  ext a
  exact (idealResidueAlgebra_coefficient A B a).symm

/-- Completeness genuinely constructs a root with the specified primitive residue. -/
theorem exists_coefficient_root : ∃ b : B,
    (coefficientPolynomial A B).eval₂ (algebraMap A B) b = 0 ∧
      residue B b = (primitiveBasis (maximalIdeal A) (ResidueField B)).gen := by
  let F := coefficientPolynomial A B
  let G := F.map (algebraMap A B)
  let α := (primitiveBasis (maximalIdeal A) (ResidueField B)).gen
  obtain ⟨b₀, hb₀⟩ := residue_surjective (R := B) α
  have hroot : G.eval b₀ ∈ maximalIdeal B := by
    apply (residue_eq_zero_iff _).mp
    rw [← Polynomial.eval₂_at_apply, hb₀, ← Polynomial.eval_map]
    rw [show G.map (residue B) = _ from coefficientPolynomial_residue A B]
    rw [Polynomial.eval_map]
    exact minpoly.aeval (maximalIdeal A).ResidueField α
  have hderiv : IsUnit (Ideal.Quotient.mk (maximalIdeal B) (G.derivative.eval b₀)) := by
    change IsUnit (residue B (G.derivative.eval b₀))
    apply isUnit_iff_ne_zero.mpr
    rw [← Polynomial.eval₂_at_apply, hb₀, ← Polynomial.eval_map, ← Polynomial.derivative_map]
    rw [show G.map (residue B) = _ from coefficientPolynomial_residue A B]
    rw [Polynomial.derivative_map, Polynomial.eval_map]
    exact (residuePolynomial_separable (maximalIdeal A) (ResidueField B)).aeval_derivative_ne_zero
      (minpoly.aeval (maximalIdeal A).ResidueField α)
  obtain ⟨b, hb, hbb₀⟩ := HenselianRing.is_henselian G
    ((liftPolynomial_monic (maximalIdeal A) (ResidueField B)).map (algebraMap A B)) b₀ hroot hderiv
  refine ⟨b, ?_, ?_⟩
  · rw [← Polynomial.eval_map]
    exact hb
  · have he := (residue_eq_zero_iff _).mpr hbb₀
    rw [map_sub, sub_eq_zero] at he
    exact he.trans hb₀

/-- The chosen actual root is supplied by native Hensel lifting, not a root certificate premise. -/
def coefficientRoot : B := Classical.choose (exists_coefficient_root A B)

theorem coefficientRoot_isRoot :
    (coefficientPolynomial A B).eval₂ (algebraMap A B) (coefficientRoot A B) = 0 :=
  (Classical.choose_spec (exists_coefficient_root A B)).1

@[simp]
theorem coefficientRoot_residue : residue B (coefficientRoot A B) =
    (primitiveBasis (maximalIdeal A) (ResidueField B)).gen :=
  (Classical.choose_spec (exists_coefficient_root A B)).2

/-- The actual map from the literal finite-free étale coefficient algebra into original B. -/
def coefficientMap : CoefficientRing A B →ₐ[A] B :=
  AdjoinRoot.liftAlgHom (coefficientPolynomial A B) (Algebra.ofId A B)
    (coefficientRoot A B) (coefficientRoot_isRoot A B)

@[simp]
theorem coefficientMap_root :
    coefficientMap A B (AdjoinRoot.root (coefficientPolynomial A B)) = coefficientRoot A B :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The full residue triangle commutes on every original element of the actual coefficient ring. -/
theorem coefficientMap_residue :
    (residue B).comp (coefficientMap A B).toRingHom =
      specialization (maximalIdeal A) (ResidueField B) := by
  apply AdjoinRoot.ringHom_ext
  · ext a
    change residue B (coefficientMap A B (algebraMap A (CoefficientRing A B) a)) =
      specialization (maximalIdeal A) (ResidueField B) (algebraMap A (CoefficientRing A B) a)
    rw [AlgHom.commutes, specialization_algebraMap, idealResidueAlgebra_coefficient]
  · change residue B (coefficientMap A B (AdjoinRoot.root (coefficientPolynomial A B))) = _
    rw [coefficientMap_root, coefficientRoot_residue, specialization_root]

/-- The internally constructed map into B is an actual local ring homomorphism. -/
instance coefficientMap_isLocalHom : IsLocalHom (coefficientMap A B).toRingHom := by
  apply ((IsLocalRing.local_hom_TFAE (coefficientMap A B).toRingHom).out 3 0).mp
  intro x hx
  change coefficientMap A B x ∈ maximalIdeal B
  apply (residue_eq_zero_iff _).mp
  have he := RingHom.congr_fun (coefficientMap_residue A B) x
  change residue B (coefficientMap A B x) = specialization (maximalIdeal A) (ResidueField B) x at he
  rw [he]
  rw [coefficients_maximalIdeal] at hx
  exact hx

end DeJongAlterations.Algebra.NodeEtaleCoefficients
