import DeJongAlterations.Geometry.ProjectiveIdealCharts

/-!
# Actual native projective coordinate overlap algebra

All coordinate transitions are constructed in the homogeneous localization
at the product of the two selected coordinates.
-/

open MvPolynomial HomogeneousLocalization
open DeJongAlterations.Geometry.ProjectiveIdeal

noncomputable section

namespace DeJongAlterations.Algebra.Segre

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {d : ℕ}

/-- The actual homogeneous coordinate ring of an intersection of two projective coordinate opens. -/
abbrev CoordinateOverlapRing (R : Type u) [CommRing R] {d : ℕ}
    (i k : Fin (d + 1)) :=
  Away (ProjectiveGrading R d)
    ((MvPolynomial.X i : MvPolynomial (Fin (d + 1)) R) * MvPolynomial.X k)

/-- The actual coefficient map on the native coordinate overlap ring. -/
def overlapCoefficients (i k : Fin (d + 1)) : R →+* CoordinateOverlapRing R i k :=
  (fromZeroRingHom (ProjectiveGrading R d)
    (.powers ((MvPolynomial.X i : MvPolynomial (Fin (d + 1)) R) * MvPolynomial.X k))).comp
    (homogeneousCoefficientZero R d)

/-- The canonical coefficient algebra on the actual native coordinate overlap. -/
@[instance_reducible]
def overlapAlgebra (i k : Fin (d + 1)) : Algebra R (CoordinateOverlapRing R i k) :=
  (overlapCoefficients i k).toAlgebra

attribute [local instance] overlapAlgebra

/-- The actual first-chart coordinate restriction into its native overlap ring. -/
def overlapLeft (i k : Fin (d + 1)) :
    CoordinateRing R i →ₐ[R] CoordinateOverlapRing R i k where
  __ := (awayMap (ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R k) rfl).comp
    (homogeneousChartRatioHom i).toRingHom
  commutes' r := by
    change awayMap (ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R k) rfl
      (homogeneousChartRatioHom i (algebraMap R (CoordinateRing R i) r)) =
        overlapCoefficients i k r
    rw [(homogeneousChartRatioHom i).commutes]
    exact awayMap_fromZeroRingHom _ _ _ _

/-- The actual second-chart coordinate restriction into the same native overlap ring. -/
def overlapRight (i k : Fin (d + 1)) :
    CoordinateRing R k →ₐ[R] CoordinateOverlapRing R i k where
  __ := (awayMap (ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R i)
      (mul_comm _ _)).comp
    (homogeneousChartRatioHom k).toRingHom
  commutes' r := by
    change awayMap (ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R i)
      (mul_comm _ _) (homogeneousChartRatioHom k (algebraMap R (CoordinateRing R k) r)) =
        overlapCoefficients i k r
    rw [(homogeneousChartRatioHom k).commutes]
    exact awayMap_fromZeroRingHom _ _ _ _

/-- Every normalized coordinate, including the pivot, is the actual homogeneous fraction. -/
theorem homogeneousChartRatioHom_coordinate (i l : Fin (d + 1)) :
    homogeneousChartRatioHom i (coordinateDehomCoord (R := R) i l) =
      Away.mk (ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R i)
        1 (MvPolynomial.X l) (by simpa using MvPolynomial.isHomogeneous_X R l) := by
  apply (homogeneousChartEquiv (R := R) i).injective
  change homogeneousChartDehom i
      (homogeneousChartRatioHom i (coordinateDehomCoord (R := R) i l)) =
    homogeneousChartDehom i (Away.mk (ProjectiveGrading R d)
      (MvPolynomial.isHomogeneous_X R i) 1 (MvPolynomial.X l) _)
  rw [← AlgHom.comp_apply, homogeneousChartDehom_comp_ratioHom, AlgHom.id_apply,
    homogeneousChartDehom_mk]
  simp [coordinateDehom]

/-- Changing projective coordinate pivot gives the actual cross-multiplication identity. -/
theorem overlap_coordinate_cross (i k l : Fin (d + 1)) :
    overlapRight (R := R) i k (coordinateDehomCoord k l) *
        overlapLeft i k (coordinateDehomCoord i k) =
      overlapLeft i k (coordinateDehomCoord i l) := by
  apply HomogeneousLocalization.val_injective
  simp only [val_mul]
  change
    (awayMap (ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R i) (mul_comm _ _)
        (homogeneousChartRatioHom k (coordinateDehomCoord k l))).val *
      (awayMap (ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R k) rfl
        (homogeneousChartRatioHom i (coordinateDehomCoord i k))).val =
    (awayMap (ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R k) rfl
        (homogeneousChartRatioHom i (coordinateDehomCoord i l))).val
  simp only [homogeneousChartRatioHom_coordinate, awayMap_mk, Away.val_mk, pow_one,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- The change-of-pivot coordinate is an actual unit on the overlap. -/
theorem overlapLeft_pivot_isUnit (i k : Fin (d + 1)) :
    IsUnit (overlapLeft (R := R) i k (coordinateDehomCoord i k)) := by
  apply IsUnit.of_mul_eq_one (overlapRight i k (coordinateDehomCoord k i))
  simpa [mul_comm] using overlap_coordinate_cross (R := R) i k i

variable {T : Type u} [CommRing T]

/-- The native overlap algebra over the entire first homogeneous chart ring. -/
@[instance_reducible]
def overlapChartAlgebra (i k : Fin (d + 1)) :
    Algebra (HomogeneousChartRing R i) (CoordinateOverlapRing R i k) :=
  (awayMap (ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R k) rfl).toAlgebra

attribute [local instance] overlapChartAlgebra

/-- The actual overlap is the native localization of the entire first homogeneous chart. -/
theorem overlapChart_isLocalization (i k : Fin (d + 1)) :
    IsLocalization.Away
      (Away.isLocalizationElem (𝒜 := ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R i)
        (MvPolynomial.isHomogeneous_X R k)) (CoordinateOverlapRing R i k) :=
  Away.isLocalization_mul (MvPolynomial.isHomogeneous_X R i)
    (MvPolynomial.isHomogeneous_X R k) rfl (by decide : (1 : ℕ) ≠ 0)

attribute [local instance] overlapChart_isLocalization

/-- An actual chart ring map with invertible change of pivot extends canonically to the native overlap. -/
def overlapLift (i k : Fin (d + 1)) (f : CoordinateRing R i →+* T)
    (hu : IsUnit (f (coordinateDehomCoord i k))) :
    CoordinateOverlapRing R i k →+* T := by
  have hv : IsUnit ((f.comp (homogeneousChartDehom i).toRingHom)
      (Away.isLocalizationElem (𝒜 := ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R i)
        (MvPolynomial.isHomogeneous_X R k))) := by
    change IsUnit (f (homogeneousChartDehom i
      (Away.mk (ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R i) 1
        ((MvPolynomial.X k) ^ 1) _)))
    simpa only [homogeneousChartDehom_mk, coordinateDehom, map_pow,
      MvPolynomial.aeval_X, pow_one] using hu
  exact IsLocalization.Away.lift
    (Away.isLocalizationElem (𝒜 := ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R i)
      (MvPolynomial.isHomogeneous_X R k)) hv

/-- The constructed extension has the actual localization triangle on the entire homogeneous chart ring. -/
theorem overlapLift_awayMap (i k : Fin (d + 1)) (f : CoordinateRing R i →+* T)
    (hu : IsUnit (f (coordinateDehomCoord i k))) (z : HomogeneousChartRing R i) :
    overlapLift i k f hu
        (awayMap (ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R k) rfl z) =
      f (homogeneousChartDehom i z) := by
  unfold overlapLift
  apply IsLocalization.Away.lift_eq

/-- The constructed overlap extension restricts to the original whole-ring affine chart map. -/
theorem overlapLift_left (i k : Fin (d + 1)) (f : CoordinateRing R i →+* T)
    (hu : IsUnit (f (coordinateDehomCoord i k))) (z : CoordinateRing R i) :
    overlapLift i k f hu (overlapLeft i k z) = f z := by
  change overlapLift i k f hu (awayMap (ProjectiveGrading R d)
      (MvPolynomial.isHomogeneous_X R k) rfl (homogeneousChartRatioHom i z)) = _
  rw [overlapLift_awayMap, ← AlgHom.comp_apply, homogeneousChartDehom_comp_ratioHom]
  rfl

/-- The actual overlap extension sends every coordinate for a second pivot to its normalized value. -/
theorem overlapLift_right_coordinate (i k l : Fin (d + 1))
    (f : CoordinateRing R i →+* T) (g : CoordinateRing R k →+* T)
    (hu : IsUnit (f (coordinateDehomCoord i k)))
    (hc : f (coordinateDehomCoord i l) =
      g (coordinateDehomCoord k l) * f (coordinateDehomCoord i k)) :
    overlapLift i k f hu (overlapRight i k (coordinateDehomCoord k l)) =
      g (coordinateDehomCoord k l) := by
  apply hu.mul_right_cancel
  rw [← overlapLift_left i k f hu (coordinateDehomCoord i k), ← map_mul,
    overlap_coordinate_cross, overlapLift_left, hc, overlapLift_left]

/-- Cross-multiplication and coefficient compatibility identify the entire second chart map. -/
theorem overlapLift_comp_right (i k : Fin (d + 1))
    (f : CoordinateRing R i →+* T) (g : CoordinateRing R k →+* T)
    (hu : IsUnit (f (coordinateDehomCoord i k)))
    (hcoeff : ∀ r : R, f (MvPolynomial.C r) = g (MvPolynomial.C r))
    (hcross : ∀ l, f (coordinateDehomCoord i l) =
      g (coordinateDehomCoord k l) * f (coordinateDehomCoord i k)) :
    (overlapLift i k f hu).comp (overlapRight i k).toRingHom = g := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change overlapLift i k f hu (overlapRight i k (algebraMap R (CoordinateRing R k) r)) = _
    rw [(overlapRight i k).commutes, ← (overlapLeft i k).commutes, overlapLift_left]
    exact hcoeff r
  · intro l
    simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coordinateDehomCoord_ne] using
      overlapLift_right_coordinate i k l.val f g hu (hcross l.val)

end DeJongAlterations.Algebra.Segre
