import DeJongAlterations.Algebra.NodeFittingGeneralPolynomial
import DeJongAlterations.Algebra.NodeVariableMorseJacobian
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Original polynomial finitely presented differentials along the canonical formal map

This constructs and computes the actual pullback of the genuine original
polynomial hypersurface Kaehler module. It makes no comparison with an
arbitrary original geometric family's completed coherent module.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingGeneral

open NodeFormalMorse
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R]

/-- Literal original formal hypersurface of the same original polynomial. -/
abbrev FormalHypersurface (f : MvPolynomial (Fin 2) R) :=
  Series R ⧸ Ideal.span {(f : Series R)}

/-- The native inclusion of original polynomials into original formal series. -/
def polynomialSeriesMap : MvPolynomial (Fin 2) R →ₐ[R] Series R where
  __ := MvPolynomial.coeToMvPowerSeries.ringHom
  commutes' r := by
    change ((MvPolynomial.C r : MvPolynomial (Fin 2) R) : Series R) = MvPowerSeries.C r
    exact MvPolynomial.coe_C r

@[simp]
theorem polynomialSeriesMap_apply (f : MvPolynomial (Fin 2) R) :
    polynomialSeriesMap f = (f : Series R) := rfl

/-- The actual canonical map of the original literal hypersurfaces. -/
def polynomialToFormal (f : MvPolynomial (Fin 2) R) :
    PolynomialHypersurface f →ₐ[R] FormalHypersurface f :=
  Ideal.Quotient.liftₐ _
    ((Ideal.Quotient.mkₐ R (Ideal.span {(f : Series R)})).comp polynomialSeriesMap) (by
      change polynomialIdeal f ≤ RingHom.ker
        ((Ideal.Quotient.mkₐ R (Ideal.span {(f : Series R)})).comp polynomialSeriesMap).toRingHom
      apply Ideal.span_le.mpr
      intro g hg
      have he : g = f := Set.mem_singleton_iff.mp hg
      rw [he]
      change Ideal.Quotient.mk (Ideal.span {(f : Series R)}) (f : Series R) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))

@[simp]
theorem polynomialToFormal_mk (f g : MvPolynomial (Fin 2) R) :
    polynomialToFormal f (Ideal.Quotient.mk (polynomialIdeal f) g) =
      Ideal.Quotient.mk (Ideal.span {(f : Series R)}) (g : Series R) := rfl

/-- The actual original coefficient triangle. -/
@[simp]
theorem polynomialToFormal_coefficient (f : MvPolynomial (Fin 2) R) (a : R) :
    polynomialToFormal f (Ideal.Quotient.mk (polynomialIdeal f) (MvPolynomial.C a)) =
      Ideal.Quotient.mk (Ideal.span {(f : Series R)}) (MvPowerSeries.C a) := by
  rw [polynomialToFormal_mk, MvPolynomial.coe_C]

/-- The actual original coordinate triangle. -/
@[simp]
theorem polynomialToFormal_coordinate (f : MvPolynomial (Fin 2) R) (i : Fin 2) :
    polynomialToFormal f (Ideal.Quotient.mk (polynomialIdeal f) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (Ideal.span {(f : Series R)} ) (MvPowerSeries.X i) := by
  rw [polynomialToFormal_mk, MvPolynomial.coe_X]

/-- Native polynomial and formal derivatives of the same original equation commute. -/
@[simp]
theorem polynomialToFormal_derivative (f : MvPolynomial (Fin 2) R) (i : Fin 2) :
    polynomialToFormal f (Ideal.Quotient.mk (polynomialIdeal f) (MvPolynomial.pderiv i f)) =
      Ideal.Quotient.mk (Ideal.span {(f : Series R)}) (MvPowerSeries.pderiv R i (f : Series R)) := by
  rw [polynomialToFormal_mk, MvPowerSeries.pderiv_coe]

instance polynomialHypersurfaceAlgebra (f : MvPolynomial (Fin 2) R) :
    Algebra (PolynomialHypersurface f) (FormalHypersurface f) := (polynomialToFormal f).toAlgebra

instance polynomialHypersurfaceScalarTower (f : MvPolynomial (Fin 2) R) :
    IsScalarTower R (PolynomialHypersurface f) (FormalHypersurface f) := by
  constructor
  intro r a b
  change polynomialToFormal f (r • a) * b = r • (polynomialToFormal f a * b)
  rw [map_smul, smul_mul_assoc]

/-- The actual polynomial-model finitely presented differential module pulled to the original formal node. -/
abbrev FormalModelDifferentials (f : MvPolynomial (Fin 2) R) :=
  FormalHypersurface f ⊗[PolynomialHypersurface f] KaehlerDifferential R (PolynomialHypersurface f)

/-- The actual base-changed original differential map. -/
def formalDifferentialMap (f : MvPolynomial (Fin 2) R) :=
  (polynomialPresentation f).toExtension.toKaehler.baseChange (FormalHypersurface f)

/-- The actual base-changed original conormal map. -/
def formalConormalMap (f : MvPolynomial (Fin 2) R) :=
  (polynomialPresentation f).toExtension.cotangentComplex.baseChange (FormalHypersurface f)

/-- Native right exactness retains the whole original differential kernel. -/
theorem formalDifferential_exact (f : MvPolynomial (Fin 2) R) :
    Function.Exact (formalConormalMap f) (formalDifferentialMap f) :=
  lTensor_exact (FormalHypersurface f)
    (polynomialPresentation f).toExtension.exact_cotangentComplex_toKaehler
    (toKaehler_surjective f)

/-- Every element of the actual pulled differential module is an actual image. -/
theorem formalDifferential_surjective (f : MvPolynomial (Fin 2) R) :
    Function.Surjective (formalDifferentialMap f) :=
  LinearMap.lTensor_surjective (FormalHypersurface f) (toKaehler_surjective f)

/-- The actual original relation vector after scalar extension. -/
def formalGradientVector (f : MvPolynomial (Fin 2) R) :
    FormalHypersurface f ⊗[PolynomialHypersurface f] (polynomialPresentation f).toExtension.CotangentSpace :=
  1 ⊗ₜ gradientVector f

/-- The whole actual base-changed conormal image is generated by the original relation vector. -/
theorem formalConormal_range (f : MvPolynomial (Fin 2) R) :
    LinearMap.range (formalConormalMap f) =
      Submodule.span (FormalHypersurface f) {formalGradientVector f} := by
  have he : LinearMap.range (formalConormalMap f) =
      (LinearMap.range (polynomialPresentation f).toExtension.cotangentComplex).baseChange
        (FormalHypersurface f) := by
    apply Submodule.restrictScalars_injective (PolynomialHypersurface f)
    exact LinearMap.lTensor_range
      (g := (polynomialPresentation f).toExtension.cotangentComplex) (FormalHypersurface f)
  rw [he, cotangentComplex_range, Submodule.baseChange_span, Set.image_singleton]
  rfl

/-- The actual pulled differential kernel is precisely the original single relation. -/
theorem formalDifferential_kernel (f : MvPolynomial (Fin 2) R) :
    LinearMap.ker (formalDifferentialMap f) =
      Submodule.span (FormalHypersurface f) {formalGradientVector f} := by
  rw [LinearMap.exact_iff.mp (formalDifferential_exact f), formalConormal_range]

/-- The genuine pulled finitely presented differential module is the actual original one-relation cokernel. -/
def formalDifferentialQuotientEquiv (f : MvPolynomial (Fin 2) R) :
    ((FormalHypersurface f ⊗[PolynomialHypersurface f] (polynomialPresentation f).toExtension.CotangentSpace) ⧸
      Submodule.span (FormalHypersurface f) {formalGradientVector f}) ≃ₗ[FormalHypersurface f]
        FormalModelDifferentials f :=
  (Submodule.quotEquivOfEq _ _ (formalDifferential_kernel f).symm).trans
    ((formalDifferentialMap f).quotKerEquivOfSurjective (formalDifferential_surjective f))

/-- The actual original two-dimensional cotangent basis after scalar extension. -/
def formalCotangentBasis (f : MvPolynomial (Fin 2) R) :=
  (polynomialPresentation f).cotangentSpaceBasis.baseChange (FormalHypersurface f)

/-- The original relation-column coordinates are transported through the actual coefficient map. -/
theorem formalGradient_coordinate (f : MvPolynomial (Fin 2) R) (i : Fin 2) :
    (formalCotangentBasis f).repr (formalGradientVector f) i =
      algebraMap (PolynomialHypersurface f) (FormalHypersurface f)
        ((polynomialPresentation f).cotangentSpaceBasis.repr (gradientVector f) i) := by
  simp [formalCotangentBasis, formalGradientVector, Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def]

/-- The actual first determinantal ideal of the pulled original one-relation presentation. -/
def formalPresentationFirstFittingIdeal (f : MvPolynomial (Fin 2) R) : Ideal (FormalHypersurface f) :=
  Ideal.span {(formalCotangentBasis f).repr (formalGradientVector f) 0,
    (formalCotangentBasis f).repr (formalGradientVector f) 1}

/-- The actual first presentation minors commute with this actual scalar extension. -/
theorem formalPresentationFirstFittingIdeal_eq_map (f : MvPolynomial (Fin 2) R) :
    formalPresentationFirstFittingIdeal f =
      (presentationFirstFittingIdeal f).map (algebraMap (PolynomialHypersurface f) (FormalHypersurface f)) := by
  unfold formalPresentationFirstFittingIdeal presentationFirstFittingIdeal
  rw [formalGradient_coordinate, formalGradient_coordinate, Ideal.map_span,
    Set.image_insert_eq, Set.image_singleton]

/-- Each actual pulled relation coordinate is the native original formal partial derivative. -/
theorem formalGradient_coordinate_derivative (f : MvPolynomial (Fin 2) R) (i : Fin 2) :
    (formalCotangentBasis f).repr (formalGradientVector f) i =
      Ideal.Quotient.mk (Ideal.span {(f : Series R)}) (MvPowerSeries.pderiv R i (f : Series R)) := by
  rw [formalGradient_coordinate, gradientVector_coordinate]
  change polynomialToFormal f (Ideal.Quotient.mk (polynomialIdeal f) (MvPolynomial.pderiv i f)) = _
  exact polynomialToFormal_derivative f i

/-- The actual original formal derivative-image ideal. -/
def formalDerivativeIdeal (f : MvPolynomial (Fin 2) R) : Ideal (FormalHypersurface f) :=
  Ideal.span {Ideal.Quotient.mk (Ideal.span {(f : Series R)})
      (MvPowerSeries.pderiv R (0 : Fin 2) (f : Series R)),
    Ideal.Quotient.mk (Ideal.span {(f : Series R)})
      (MvPowerSeries.pderiv R (1 : Fin 2) (f : Series R))}

/-- The actual pulled presentation minors are the original native formal derivative images. -/
theorem formalPresentationFirstFittingIdeal_eq_derivatives (f : MvPolynomial (Fin 2) R) :
    formalPresentationFirstFittingIdeal f = formalDerivativeIdeal f := by
  unfold formalPresentationFirstFittingIdeal formalDerivativeIdeal
  rw [formalGradient_coordinate_derivative, formalGradient_coordinate_derivative]

end DeJongAlterations.Algebra.NodeFittingGeneral
