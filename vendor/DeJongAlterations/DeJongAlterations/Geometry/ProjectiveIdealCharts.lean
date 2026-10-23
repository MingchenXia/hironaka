/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Algebra.ProjectiveIdealChartLocalization
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
/- Reused from EnvelopeProperty/Projective/HomogeneousChart.lean; SHA256 ac9bd968f3c41fd082d6c6c97a5bfc135773411fb74f06cea5fa65cf60a098a7. -/


/-!
# Actual homogeneous coordinate charts of polynomial Proj

For an arbitrary commutative coefficient ring, the genuine degree-zero homogeneous
localization at a coordinate is identified with the existing affine coordinate ring.
The two inverses hold on the entire rings. The resulting actual Mathlib Proj scheme
chart and section-ring isomorphisms preserve the true fraction section map and germs.

This module supplies algebraic scheme and section interfaces. A comparison of native
valued scheme points with normalized graded seminorms is a separate producer.
-/

open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory Opposite
noncomputable section
namespace DeJongAlterations.Geometry.ProjectiveIdeal
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type*} [CommRing R] {n : ℕ}

abbrev ProjectiveGrading (R : Type*) [CommRing R] (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

abbrev HomogeneousChartRing (R : Type*) [CommRing R] (j : Fin (n + 1)) :=
  HomogeneousLocalization.Away (ProjectiveGrading R n)
    (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)

def homogeneousCoefficientZero (R : Type*) [CommRing R] (n : ℕ) :
    R →+* ProjectiveGrading R n 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Fin (n + 1)) r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

def homogeneousChartCoefficients (j : Fin (n + 1)) : R →+* HomogeneousChartRing R j :=
  (HomogeneousLocalization.fromZeroRingHom (ProjectiveGrading R n) (.powers (MvPolynomial.X j))).comp
    (homogeneousCoefficientZero R n)

@[instance_reducible]
def homogeneousChartAlgebra (j : Fin (n + 1)) : Algebra R (HomogeneousChartRing R j) :=
  (homogeneousChartCoefficients j).toAlgebra

private local instance homogeneousChartBaseAlgebra (j : Fin (n + 1)) :
    Algebra R (HomogeneousChartRing R j) := homogeneousChartAlgebra j

def homogeneousChartVal (j : Fin (n + 1)) : HomogeneousChartRing R j →ₐ[R]
    Localization.Away (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) where
  __ := algebraMap (HomogeneousChartRing R j) (Localization.Away (MvPolynomial.X j))
  commutes' r := by
    change HomogeneousLocalization.val (homogeneousChartCoefficients j r) = _
    change Localization.mk (C r : MvPolynomial (Fin (n + 1)) R)
      (1 : Submonoid.powers (X j)) = (algebraMap R (Localization.Away (X j))) r
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin (n + 1)) R)]
    rfl

def homogeneousChartCoordinate (j : Fin (n + 1)) (i : ChartIndex j) : HomogeneousChartRing R j :=
  HomogeneousLocalization.Away.mk (ProjectiveGrading R n)
    (show (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ∈ ProjectiveGrading R n 1 from
      MvPolynomial.isHomogeneous_X R j) 1 (MvPolynomial.X i.1)
    (by simpa using MvPolynomial.isHomogeneous_X R i.1)

def homogeneousChartRatioHom (j : Fin (n + 1)) :
    CoordinateRing R j →ₐ[R] HomogeneousChartRing R j :=
  MvPolynomial.aeval (homogeneousChartCoordinate j)

/-- The genuine homogeneous ratios agree with the existing ordinary chart map on every polynomial. -/
theorem homogeneousChartVal_comp_ratioHom (j : Fin (n + 1)) :
    (homogeneousChartVal (R := R) j).comp (homogeneousChartRatioHom j) = chartRatioHom j := by
  ext i
  simp only [AlgHom.comp_apply, homogeneousChartRatioHom, MvPolynomial.aeval_X]
  change (homogeneousChartCoordinate (R := R) j i).val = _
  rw [homogeneousChartCoordinate, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  simp only [chartRatioHom, MvPolynomial.aeval_X]

def homogeneousChartDehom (j : Fin (n + 1)) :
    HomogeneousChartRing R j →ₐ[R] CoordinateRing R j :=
  (coordinateDehomLocalization j).comp (homogeneousChartVal j)

/-- Dehomogenization of every genuine homogeneous fraction is the original form at Xj=1. -/
theorem homogeneousChartDehom_mk (j : Fin (n + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ ProjectiveGrading R n (d • (1 : ℕ))) :
    homogeneousChartDehom j (HomogeneousLocalization.Away.mk (ProjectiveGrading R n)
      (show (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ∈ ProjectiveGrading R n 1 from
        MvPolynomial.isHomogeneous_X R j) d F hF) = coordinateDehom j F := by
  have h := congrArg (coordinateDehomLocalization (R := R) j)
    (IsLocalization.mk'_spec
      (Localization.Away (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)) F
      (⟨MvPolynomial.X j ^ d, d, rfl⟩ : Submonoid.powers (MvPolynomial.X j)))
  simp only [map_mul, coordinateDehomLocalization_algebraMap, map_pow] at h
  simp only [coordinateDehom, MvPolynomial.aeval_X, coordinateDehomCoord_self, one_pow, mul_one] at h
  change coordinateDehomLocalization j
    (Localization.mk F (⟨MvPolynomial.X j ^ d, d, rfl⟩ : Submonoid.powers (MvPolynomial.X j))) = _
  rw [Localization.mk_eq_mk']
  exact h

/-- The genuine homogeneous degree-zero localization embeds in the full ordinary localization. -/
theorem homogeneousChartVal_injective (j : Fin (n + 1)) :
    Function.Injective (homogeneousChartVal (R := R) j) :=
  HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X j))

/-- The actual affine polynomial ring is recovered on every polynomial. -/
theorem homogeneousChartDehom_comp_ratioHom (j : Fin (n + 1)) :
    (homogeneousChartDehom (R := R) j).comp (homogeneousChartRatioHom j) =
      AlgHom.id R (CoordinateRing R j) := by
  ext i
  simp only [AlgHom.comp_apply, homogeneousChartRatioHom, MvPolynomial.aeval_X,
    homogeneousChartCoordinate, homogeneousChartDehom_mk]
  simp [coordinateDehom]

/-- The inverse identity holds on every homogeneous fraction, hence on the whole ring. -/
theorem homogeneousChartRatioHom_comp_dehom (j : Fin (n + 1)) :
    (homogeneousChartRatioHom (R := R) j).comp (homogeneousChartDehom j) =
      AlgHom.id R (HomogeneousChartRing R j) := by
  apply AlgHom.ext
  intro z
  obtain ⟨d, F, hF, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (ProjectiveGrading R n) (MvPolynomial.isHomogeneous_X R j) z
  rw [AlgHom.comp_apply, homogeneousChartDehom_mk]
  apply homogeneousChartVal_injective j
  change homogeneousChartVal j (homogeneousChartRatioHom j (coordinateDehom j F)) =
    Localization.mk F (⟨MvPolynomial.X j ^ d, d, rfl⟩ : Submonoid.powers (MvPolynomial.X j))
  rw [← AlgHom.comp_apply, homogeneousChartVal_comp_ratioHom, Localization.mk_eq_mk']
  have hs := chartRatioHom_dehom_mul_pow j
    (show F.IsHomogeneous d from by simpa using hF)
  have ht := IsLocalization.mk'_spec
    (Localization.Away (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)) F
    (⟨MvPolynomial.X j ^ d, d, rfl⟩ : Submonoid.powers (MvPolynomial.X j))
  rw [map_pow] at ht
  exact (IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away (MvPolynomial.X j))
    (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) d).mul_right_cancel (hs.trans ht.symm)

/-- The actual homogeneous degree-zero coordinate algebra is the existing affine coordinate ring. -/
def homogeneousChartEquiv (j : Fin (n + 1)) :
    HomogeneousChartRing R j ≃ₐ[R] CoordinateRing R j :=
  { homogeneousChartDehom j with
    invFun := homogeneousChartRatioHom j
    left_inv z := AlgHom.congr_fun (homogeneousChartRatioHom_comp_dehom j) z
    right_inv a := AlgHom.congr_fun (homogeneousChartDehom_comp_ratioHom j) a }

/-- The actual Mathlib Proj scheme of the total-degree graded polynomial ring. -/
def NativeProjectiveScheme (R : Type*) [CommRing R] (n : ℕ) : Scheme :=
  AlgebraicGeometry.Proj (ProjectiveGrading R n)

/-- The actual coordinate-open subset of that scheme. -/
def nativeCoordinateOpen (j : Fin (n + 1)) : (NativeProjectiveScheme R n).Opens :=
  ProjectiveSpectrum.basicOpen (ProjectiveGrading R n) (MvPolynomial.X j)

/-- Actual Proj structure-sheaf construction identifies the open with the spectrum of the degree-zero localization. -/
def nativeHomogeneousChartSchemeIso (j : Fin (n + 1)) :
    (nativeCoordinateOpen (R := R) j).toScheme ≅ Spec (CommRingCat.of (HomogeneousChartRing R j)) :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso
    (AlgebraicGeometry.projIsoSpec (ProjectiveGrading R n) (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X R j) (by decide : 0 < (1 : ℕ)))

/-- The coordinate open is genuinely affine, without an assumed chart certificate. -/
theorem nativeCoordinateOpen_isAffine (j : Fin (n + 1)) :
    IsAffineOpen (nativeCoordinateOpen (R := R) j) :=
  IsAffine.of_isIso (nativeHomogeneousChartSchemeIso j).hom

/-- The actual projective coordinate chart is the spectrum of the existing coordinate ring. -/
def nativeCoordinateSchemeIso (j : Fin (n + 1)) :
    (nativeCoordinateOpen (R := R) j).toScheme ≅ Spec (CommRingCat.of (CoordinateRing R j)) :=
  (nativeHomogeneousChartSchemeIso j).trans
    (Scheme.Spec.mapIso (homogeneousChartEquiv (R := R) j).toRingEquiv.toCommRingCatIso.symm.op)

/-- Genuine local sections are compared through the actual Proj affine scheme isomorphism. -/
def nativeHomogeneousChartSectionsIso (j : Fin (n + 1)) :
    CommRingCat.of (HomogeneousChartRing R j) ≅
      Γ(NativeProjectiveScheme R n, nativeCoordinateOpen j) :=
  (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousChartRing R j))).symm.trans
    ((Scheme.Γ.mapIso (nativeHomogeneousChartSchemeIso (R := R) j).op).trans
      (nativeCoordinateOpen (R := R) j).topIso)

/-- The actual section ring of a coordinate open is isomorphic to the existing affine coordinate ring. -/
def nativeCoordinateSectionsIso (j : Fin (n + 1)) :
    CommRingCat.of (CoordinateRing R j) ≅
      Γ(NativeProjectiveScheme R n, nativeCoordinateOpen j) :=
  (homogeneousChartEquiv (R := R) j).toRingEquiv.toCommRingCatIso.symm.trans
    (nativeHomogeneousChartSectionsIso j)

set_option backward.isDefEq.respectTransparency false in
/-- The section comparison is the true homogeneous-fraction section map, on the whole ring. -/
theorem nativeHomogeneousChartSectionsIso_hom (j : Fin (n + 1)) :
    (nativeHomogeneousChartSectionsIso (R := R) j).hom =
      ProjectiveSpectrum.Proj.awayToSection (ProjectiveGrading R n) (MvPolynomial.X j) := by
  dsimp only [nativeHomogeneousChartSectionsIso, Iso.trans, Iso.symm, Functor.mapIso, Iso.op]
  change (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousChartRing R j))).inv ≫
    (ProjectiveSpectrum.Proj.toSpec (ProjectiveGrading R n) (MvPolynomial.X j)).c.app
      (op (⊤ : (Spec (CommRingCat.of (HomogeneousChartRing R j))).Opens)) ≫
        (nativeCoordinateOpen (R := R) j).topIso.hom = _
  have h := ProjectiveSpectrum.Proj.toOpen_toSpec_val_c_app
    (ProjectiveGrading R n) (MvPolynomial.X j)
      (op (⊤ : (Spec (CommRingCat.of (HomogeneousChartRing R j))).Opens))
  simp only [homOfLE_refl, op_id] at h
  have h' : (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousChartRing R j))).inv ≫
      (ProjectiveSpectrum.Proj.toSpec (ProjectiveGrading R n) (MvPolynomial.X j)).c.app
        (op (⊤ : (Spec (CommRingCat.of (HomogeneousChartRing R j))).Opens)) =
      ProjectiveSpectrum.Proj.awayToΓ (ProjectiveGrading R n) (MvPolynomial.X j) := by
    convert h using 1
    · erw [CategoryTheory.Functor.map_id, Category.id_comp]
    · erw [CategoryTheory.Functor.map_id, Category.comp_id]
  erw [← Category.assoc, h']
  change (ProjectiveSpectrum.Proj.awayToSection (ProjectiveGrading R n) (MvPolynomial.X j) ≫
    (nativeCoordinateOpen (R := R) j).topIso.inv) ≫
      (nativeCoordinateOpen (R := R) j).topIso.hom = _
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Actual section germs preserve the true homogeneous fraction into the genuine projective stalk. -/
theorem nativeHomogeneousChartSectionsIso_germ (j : Fin (n + 1))
    (p : NativeProjectiveScheme R n) (hp : p ∈ nativeCoordinateOpen (R := R) j) :
    (nativeHomogeneousChartSectionsIso (R := R) j).hom ≫
      (NativeProjectiveScheme R n).presheaf.germ (nativeCoordinateOpen j) p hp =
        CommRingCat.ofHom (HomogeneousLocalization.mapId (ProjectiveGrading R n)
          (Submonoid.powers_le.mpr hp)) ≫
            (AlgebraicGeometry.Proj.stalkIso' (ProjectiveGrading R n) p).toCommRingCatIso.inv := by
  erw [nativeHomogeneousChartSectionsIso_hom]
  exact ProjectiveSpectrum.Proj.awayToSection_germ (ProjectiveGrading R n) (MvPolynomial.X j) p hp

end DeJongAlterations.Geometry.ProjectiveIdeal
