/-
Copyright (c) 2026. All rights reserved.
-/
import Hironaka.Algebra.ImperfectFieldExampleCurve
import Hironaka.Geometry.ImperfectFieldExample
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Module.Torsion.Free

/-!
# The actual regular curve is not smooth

For the native ring `k[y][x]/(x²-(y³-t))`, the actual differential `dx`
is nonzero and annihilated by `2*x`. A derivation to the explicitly
constructed cube-root residue field detects its nonvanishing.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial AlgebraicGeometry CategoryTheory
open Hironaka.Algebra.ImperfectFieldExample

namespace Hironaka.Geometry.ImperfectFieldExampleCurve

section QuotientDerivation

variable {k P M : Type*} [CommRing k] [CommRing P] [Algebra k P]
    (I : Ideal P) [AddCommGroup M] [Module k M] [Module P M]
    [Module (P ⧸ I) M] [IsScalarTower k P M] [IsScalarTower P (P ⧸ I) M]
    [IsScalarTower k (P ⧸ I) M]

/-- A derivation killing an ideal descends to the actual quotient, with its actual module action. -/
def quotientDerivation (D : Derivation k P M)
    (hD : I.restrictScalars k ≤ LinearMap.ker D.toLinearMap) :
    Derivation k (P ⧸ I) M := by
  let d : (P ⧸ I) →ₗ[k] M := (I.restrictScalars k).liftQ D.toLinearMap hD
  refine Derivation.mk' d ?_
  intro x y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  change D (x * y) = (Ideal.Quotient.mk I x) • D y + (Ideal.Quotient.mk I y) • D x
  simpa only [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul] using D.leibniz x y

omit [IsScalarTower k P M] [IsScalarTower k (P ⧸ I) M] in
@[simp]
theorem quotientDerivation_mk (D : Derivation k P M)
    (hD : I.restrictScalars k ≤ LinearMap.ker D.toLinearMap) (x : P) :
    quotientDerivation I D hD (Ideal.Quotient.mk I x) = D x := rfl

end QuotientDerivation

/-- The actual residue map `x ↦ 0`, `y ↦ t^(1/3)` into the explicit field extension. -/
def residueMap : CurveRing →ₐ[BaseField] RootField :=
  AdjoinRoot.liftAlgHom quadraticEquation (Polynomial.aeval root) 0 (by
    change (X ^ 2 - C cubic).eval₂ (Polynomial.aeval root).toRingHom 0 = 0
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, zero_pow (by decide : 2 ≠ 0), zero_sub]
    rw [neg_eq_zero]
    change (Polynomial.aeval root) (X ^ 3 - C alpha) = 0
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, root_cubed, sub_self])

instance curvePolynomialAlgebra : Algebra CoefficientRing[X] CurveRing :=
  (AdjoinRoot.mk quadraticEquation).toAlgebra

instance curvePolynomialScalarTower : IsScalarTower BaseField CoefficientRing[X] CurveRing :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance curveRing_charP : CharP CurveRing 3 :=
  charP_of_injective_algebraMap (algebraMap BaseField CurveRing).injective 3

instance residueAlgebra : Algebra CurveRing RootField := residueMap.toRingHom.toAlgebra

instance residueScalarTower : IsScalarTower BaseField CurveRing RootField :=
  IsScalarTower.of_algHom residueMap

def residuePolynomialMap : CoefficientRing[X] →ₐ[BaseField] RootField :=
  residueMap.comp ((AdjoinRoot.mkₐ quadraticEquation).restrictScalars BaseField)

instance residuePolynomialAlgebra : Algebra CoefficientRing[X] RootField :=
  residuePolynomialMap.toRingHom.toAlgebra

instance residuePolynomialScalarTower : IsScalarTower BaseField CoefficientRing[X] RootField :=
  IsScalarTower.of_algHom residuePolynomialMap

instance residueQuotientScalarTower : IsScalarTower CoefficientRing[X] CurveRing RootField :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

@[simp]
theorem residueMap_curveX : residueMap curveX = 0 := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp]
theorem residueMap_curveY : residueMap curveY = root := by
  simp [curveY, residueMap]

@[simp]
theorem residuePolynomialMap_X : residuePolynomialMap X = 0 := by
  change residueMap curveX = 0
  exact residueMap_curveX

def ambientDerivative : Derivation BaseField CoefficientRing[X] RootField :=
  (Algebra.linearMap CoefficientRing[X] RootField).compDer
    (Polynomial.derivative'.restrictScalars BaseField)

@[simp]
theorem ambientDerivative_apply (H : CoefficientRing[X]) :
    ambientDerivative H = residuePolynomialMap H.derivative := rfl

theorem ambientDerivative_relation : ambientDerivative quadraticEquation = 0 := by
  rw [ambientDerivative_apply]
  have hd : quadraticEquation.derivative = (2 : CoefficientRing[X]) * X := by
    simp [quadraticEquation, one_add_one_eq_two, C_ofNat]
  rw [hd, map_mul, residuePolynomialMap_X, mul_zero]

theorem ambientDerivative_kills_ideal :
    (Ideal.span ({quadraticEquation} : Set CoefficientRing[X])).restrictScalars BaseField ≤
      LinearMap.ker ambientDerivative.toLinearMap := by
  intro H hH
  obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton.mp hH
  change ambientDerivative (quadraticEquation * Q) = 0
  rw [Derivation.leibniz, ambientDerivative_relation, smul_zero, add_zero]
  change residuePolynomialMap quadraticEquation * ambientDerivative Q = 0
  have he : residuePolynomialMap quadraticEquation = 0 := by
    change residueMap (AdjoinRoot.mk quadraticEquation quadraticEquation) = 0
    simp
  rw [he, zero_mul]

/-- The actual quotient derivation detecting `dx`. -/
def curveDerivative : Derivation BaseField CurveRing RootField :=
  by
    let : Module (CoefficientRing[X] ⧸ Ideal.span {quadraticEquation}) RootField :=
      inferInstanceAs (Module CurveRing RootField)
    let : IsScalarTower CoefficientRing[X]
        (CoefficientRing[X] ⧸ Ideal.span {quadraticEquation}) RootField :=
      inferInstanceAs (IsScalarTower CoefficientRing[X] CurveRing RootField)
    let : IsScalarTower BaseField
        (CoefficientRing[X] ⧸ Ideal.span {quadraticEquation}) RootField :=
      inferInstanceAs (IsScalarTower BaseField CurveRing RootField)
    exact quotientDerivation (Ideal.span {quadraticEquation}) ambientDerivative
      ambientDerivative_kills_ideal

@[simp]
theorem curveDerivative_curveX : curveDerivative curveX = 1 := by
  change ambientDerivative X = 1
  simp

theorem differential_curveX_ne_zero : KaehlerDifferential.D BaseField CurveRing curveX ≠ 0 := by
  intro h
  have hd := congrArg curveDerivative.liftKaehlerDifferential h
  simp only [Derivation.liftKaehlerDifferential_comp_D, curveDerivative_curveX, map_zero,
    one_ne_zero] at hd

theorem differential_curveX_torsion :
    (2 * curveX) • KaehlerDifferential.D BaseField CurveRing curveX = 0 := by
  have h := congrArg (KaehlerDifferential.D BaseField CurveRing) curveX_sq_eq_curveY_cube
  simp only [Derivation.leibniz_pow, map_sub, Derivation.map_algebraMap, sub_zero,
    Nat.reduceSub, pow_one] at h
  have hthree : (3 : CurveRing) = 0 := CharP.cast_eq_zero _ 3
  simpa only [← Nat.cast_smul_eq_nsmul CurveRing, Nat.cast_ofNat, hthree,
    zero_smul, smul_smul, zero_mul] using h

theorem curveRing_not_smooth : ¬ Algebra.Smooth BaseField CurveRing := by
  intro h
  let : Algebra.Smooth BaseField CurveRing := h
  have htwo : (2 : CurveRing) ≠ 0 := (CharP.cast_eq_zero_iff CurveRing 3 2).not.mpr (by decide)
  have htorsionFree : Module.IsTorsionFree CurveRing Ω[CurveRing⁄BaseField] := inferInstance
  have hz := (Module.isTorsionFree_iff_smul_eq_zero.mp htorsionFree)
    (2 * curveX) (KaehlerDifferential.D BaseField CurveRing curveX) differential_curveX_torsion
  exact hz.elim (mul_ne_zero htwo curveX_ne_zero) differential_curveX_ne_zero

/-- The literal structure morphism of the paper's characteristic-three curve. -/
def curveStructure : Spec (.of CurveRing) ⟶ Spec (.of BaseField) :=
  Spec.map (CommRingCat.ofHom (algebraMap BaseField CurveRing))

theorem specCurve_isRegular : IsRegularScheme (Spec (.of CurveRing)) := by
  intro x
  let p : PrimeSpectrum CurveRing := x
  let : p.asIdeal.IsPrime := p.isPrime
  exact IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (CommRingCat.of CurveRing) p).symm.commRingCatIsoToRingEquiv

theorem curveStructure_not_smooth : ¬ Smooth curveStructure := by
  intro h
  exact curveRing_not_smooth (RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp h))

end Hironaka.Geometry.ImperfectFieldExampleCurve
