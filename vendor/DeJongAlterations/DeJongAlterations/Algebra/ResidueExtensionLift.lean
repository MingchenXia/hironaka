import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
import Mathlib.RingTheory.Etale.StandardEtale

/-!
# Actual finite free lifts of specified separable residue extensions

A primitive power basis and the actual surjective maximal-ideal residue map
choose the polynomial internally. The algebra is the literal native AdjoinRoot.
-/

noncomputable section

open Polynomial Algebra TensorProduct

namespace DeJongAlterations.Algebra.ResidueExtensionLift

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] (P : Ideal R) [P.IsMaximal]
  (L : Type u) [Field L] [Algebra P.ResidueField L]
  [FiniteDimensional P.ResidueField L] [Algebra.IsSeparable P.ResidueField L]

/-- The actual primitive power basis of the specified finite separable extension. -/
def primitiveBasis : PowerBasis P.ResidueField L := Field.powerBasisOfFiniteOfSeparable _ _

/-- The actual minimal polynomial of its internally chosen primitive element. -/
def residuePolynomial : P.ResidueField[X] := minpoly P.ResidueField (primitiveBasis P L).gen

theorem residuePolynomial_monic : (residuePolynomial P L).Monic :=
  minpoly.monic (Algebra.IsSeparable.isIntegral _ _)

theorem residuePolynomial_natDegree_pos : 0 < (residuePolynomial P L).natDegree :=
  minpoly.natDegree_pos (Algebra.IsSeparable.isIntegral _ _)

theorem residuePolynomial_separable : (residuePolynomial P L).Separable :=
  Algebra.IsSeparable.isSeparable _ _

/-- Coefficients are lifted through the actual closed-point residue map. -/
theorem exists_monic_lift : ∃ F : R[X], F.map (algebraMap R P.ResidueField) =
    residuePolynomial P L ∧ F.natDegree = (residuePolynomial P L).natDegree ∧ F.Monic := by
  apply Polynomial.lifts_and_natDegree_eq_and_monic _ (residuePolynomial_monic P L)
  exact (Polynomial.mem_lifts _).mpr
    (Polynomial.map_surjective _ P.algebraMap_residueField_surjective _)

/-- The chosen actual monic lift of the primitive element's minimal polynomial. -/
def liftPolynomial : R[X] := (exists_monic_lift P L).choose

theorem liftPolynomial_map : (liftPolynomial P L).map (algebraMap R P.ResidueField) =
    residuePolynomial P L := (exists_monic_lift P L).choose_spec.1

theorem liftPolynomial_natDegree : (liftPolynomial P L).natDegree =
    (residuePolynomial P L).natDegree := (exists_monic_lift P L).choose_spec.2.1

theorem liftPolynomial_monic : (liftPolynomial P L).Monic :=
  (exists_monic_lift P L).choose_spec.2.2

/-- The literal finite-free algebra of the lifted monic polynomial. -/
abbrev LiftRing := AdjoinRoot (liftPolynomial P L)

/-- Its actual basis consists of the powers of the adjoined root. -/
def liftBasis : Module.Basis (Fin (liftPolynomial P L).natDegree) R (LiftRing P L) :=
  AdjoinRoot.powerBasisAux' (liftPolynomial_monic P L)

instance liftRing_free : Module.Free R (LiftRing P L) :=
  (liftPolynomial_monic P L).free_adjoinRoot

instance liftRing_finite : Module.Finite R (LiftRing P L) :=
  (liftPolynomial_monic P L).finite_adjoinRoot

/-- The actual primitive minimal-polynomial quotient is the specified field. -/
def residueRootEquiv : AdjoinRoot (residuePolynomial P L) ≃ₐ[P.ResidueField] L :=
  AdjoinRoot.equiv' _ (primitiveBasis P L)
    (by simp only [residuePolynomial, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) (minpoly.aeval _ _)

/-- The full coefficient base-change identity for the actual lifted root algebra. -/
def baseChangeEquiv {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (F : A[X]) :
    B ⊗[A] AdjoinRoot F ≃ₐ[B] AdjoinRoot (F.map (algebraMap A B)) := by
  let q := F.map (Algebra.TensorProduct.includeRight : A →ₐ[A] B ⊗[A] A).toRingHom
  let e := Algebra.TensorProduct.rid A B B
  refine (AdjoinRoot.tensorAlgEquiv F q rfl).trans (AdjoinRoot.mapAlgEquiv e q _ ?_)
  have he : q.map e.toRingHom = F.map (algebraMap A B) := by
    simp only [q, Polynomial.map_map]
    congr 1
    ext a
    simp [e, Algebra.smul_def]
  change Associated (q.map e.toRingHom) (F.map (algebraMap A B))
  rw [he]

/-- The actual tensor-product fibre identifies with the specified extension field. -/
def fibreEquiv : P.Fiber (LiftRing P L) ≃ₐ[P.ResidueField] L :=
  (baseChangeEquiv (B := P.ResidueField) (liftPolynomial P L)).trans
    ((AdjoinRoot.algEquivOfAssociated P.ResidueField _ _
      (by rw [liftPolynomial_map])).trans (residueRootEquiv P L))

@[simp]
theorem baseChangeEquiv_root {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (F : A[X]) : baseChangeEquiv (B := B) F (1 ⊗ₜ AdjoinRoot.root F) =
      AdjoinRoot.root (F.map (algebraMap A B)) := by
  simp [baseChangeEquiv]

@[simp]
theorem fibreEquiv_root : fibreEquiv P L (1 ⊗ₜ AdjoinRoot.root (liftPolynomial P L)) =
    (primitiveBasis P L).gen := by
  simp [fibreEquiv, residueRootEquiv, AdjoinRoot.equiv', AdjoinRoot.algEquivOfAssociated]

/-- The actual coefficient embedding into the specified field. -/
abbrev coefficientAlgebra : Algebra R L :=
  ((algebraMap P.ResidueField L).comp (algebraMap R P.ResidueField)).toAlgebra

omit [FiniteDimensional P.ResidueField L] [Algebra.IsSeparable P.ResidueField L] in
theorem coefficientScalarTower :
    letI := coefficientAlgebra P L
    IsScalarTower R P.ResidueField L := by
  let := coefficientAlgebra P L
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The actual specialization is the full fibre comparison after the native tensor inclusion. -/
def specialization : LiftRing P L →+* L :=
  (fibreEquiv P L).toRingHom.comp
    (Algebra.TensorProduct.includeRight : LiftRing P L →ₐ[R] P.Fiber (LiftRing P L)).toRingHom

@[simp]
theorem specialization_root : specialization P L (AdjoinRoot.root (liftPolynomial P L)) =
    (primitiveBasis P L).gen := fibreEquiv_root P L

@[simp]
theorem specialization_algebraMap (r : R) :
    specialization P L (algebraMap R (LiftRing P L) r) =
      algebraMap P.ResidueField L (algebraMap R P.ResidueField r) := by
  change fibreEquiv P L
    ((Algebra.TensorProduct.includeRight : LiftRing P L →ₐ[R] P.Fiber (LiftRing P L))
      (algebraMap R (LiftRing P L) r)) = _
  rw [AlgHom.commutes]
  exact (fibreEquiv P L).commutes (algebraMap R P.ResidueField r)

/-- The same actual specialization as an algebra map for its internally constructed coefficients. -/
def specializationAlgHom :
    letI := coefficientAlgebra P L
    LiftRing P L →ₐ[R] L := by
  let := coefficientAlgebra P L
  exact { specialization P L with commutes' := specialization_algebraMap P L }

/-- Every polynomial representative specializes by its actual coefficient embedding. -/
theorem specialization_mk (H : R[X]) :
    specialization P L (AdjoinRoot.mk (liftPolynomial P L) H) =
      H.eval₂ ((algebraMap P.ResidueField L).comp (algebraMap R P.ResidueField))
        (primitiveBasis P L).gen := by
  let := coefficientAlgebra P L
  change specializationAlgHom P L (AdjoinRoot.mk (liftPolynomial P L) H) =
    aeval (primitiveBasis P L).gen H
  rw [← AdjoinRoot.aeval_eq]
  simpa only [show specializationAlgHom P L (AdjoinRoot.root (liftPolynomial P L)) =
      (primitiveBasis P L).gen from specialization_root P L] using
    (Polynomial.aeval_algHom_apply (specializationAlgHom P L)
      (AdjoinRoot.root (liftPolynomial P L)) H).symm

/-- The actual specialization is onto, using the actual closed-point residue surjection. -/
theorem specialization_surjective : Function.Surjective (specialization P L) :=
  (fibreEquiv P L).surjective.comp
    (Algebra.TensorProduct.includeRight_surjective (LiftRing P L) P.algebraMap_residueField_surjective)

/-- The actual source derivative whose nonvanishing gives the etale neighbourhood. -/
def derivativeElement : LiftRing P L :=
  AdjoinRoot.mk (liftPolynomial P L) (liftPolynomial P L).derivative

/-- Polynomial differentiation commutes with the actual special-fibre comparison. -/
theorem specialization_derivative : specialization P L (derivativeElement P L) =
    aeval (primitiveBasis P L).gen (residuePolynomial P L).derivative := by
  rw [derivativeElement, specialization_mk, ← Polynomial.eval₂_map,
    ← Polynomial.derivative_map, liftPolynomial_map]
  rfl

theorem specialization_derivative_ne_zero :
    specialization P L (derivativeElement P L) ≠ 0 := by
  rw [specialization_derivative]
  exact (residuePolynomial_separable P L).aeval_derivative_ne_zero (minpoly.aeval _ _)

/-- The actual standard-etale polynomial pair for the lifted derivative open. -/
def derivativeEtalePair : StandardEtalePair R :=
  ⟨liftPolynomial P L, liftPolynomial_monic P L, (liftPolynomial P L).derivative,
    1, 0, 1, by simp⟩

/-- The actual derivative localization is etale over the original arbitrary ring. -/
theorem derivativeLocalization_etale :
    Algebra.Etale R (Localization.Away (derivativeElement P L)) :=
  Algebra.Etale.of_equiv (derivativeEtalePair P L).equivAwayAdjoinRoot

end DeJongAlterations.Algebra.ResidueExtensionLift
