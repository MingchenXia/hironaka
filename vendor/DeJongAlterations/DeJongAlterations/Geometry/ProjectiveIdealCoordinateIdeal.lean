/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Geometry.ProjectiveIdealQuotient
import DeJongAlterations.Geometry.ProjectiveIdealCharts
import DeJongAlterations.Algebra.ProjectiveIdealPolynomialGrading
/- Reused from EnvelopeProperty/Projective/NativeQuotient.lean; SHA256 4d7865d3eb2e5c8ae61f42a66d343291e47652ed4a5c719643e5bd26b186514f. Prefix ends before `private local instance nativeQuotientClosedImmersion`. -/


/-!
# Exact coordinate ideals of the actual homogeneous quotient

The two pure original chart-kernel proofs identify entire ideals, including nilpotents. Analytic comparison statements are omitted.
-/

open scoped Classical Topology
open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace DeJongAlterations.Geometry.ProjectiveIdeal
variable {R : Type u} [CommRing R] {n : ℕ}
private local instance nativeQuotientChartAlgebra (j : Fin (n + 1)) :
    Algebra R (HomogeneousChartRing R j) := homogeneousChartAlgebra j

/-- The entire original coordinate dehomogenization image is the true homogeneous quotient away kernel in affine coordinates. -/
theorem homogeneousQuotient_coordinateKernel (J : HomogeneousIdeal (ProjectiveGrading R n))
    (j : Fin (n + 1)) :
    (RingHom.ker (Away.map (GradedQuotient.gradedMk (ProjectiveGrading R n) J.toIdeal)
      (MvPolynomial.X j))).comap (homogeneousChartRatioHom j).toRingHom =
        J.toIdeal.map (coordinateDehom j).toRingHom := by
  apply le_antisymm
  · intro a ha
    change Away.map (GradedQuotient.gradedMk (ProjectiveGrading R n) J.toIdeal) (X j)
      (homogeneousChartRatioHom j a) = 0 at ha
    obtain ⟨d, F, hF, hrep⟩ := Away.mk_surjective
      (ProjectiveGrading R n) (MvPolynomial.isHomogeneous_X R j) (homogeneousChartRatioHom j a)
    rw [← hrep] at ha
    obtain ⟨m, hm⟩ := (GradedQuotient.awayMap_mk_eq_zero_iff (ProjectiveGrading R n) J
      (MvPolynomial.isHomogeneous_X R j) d F hF).mp ha
    have he : coordinateDehom j F = a := by
      rw [← homogeneousChartDehom_mk j d F hF, hrep]
      exact AlgHom.congr_fun (homogeneousChartDehom_comp_ratioHom j) a
    rw [← he]
    have h := Ideal.mem_map_of_mem (coordinateDehom j).toRingHom hm
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow,
      coordinateDehom, MvPolynomial.aeval_X, coordinateDehomCoord_self, one_pow, one_mul] using h
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    change Away.map (GradedQuotient.gradedMk (ProjectiveGrading R n) J.toIdeal) (X j)
      (homogeneousChartRatioHom j (coordinateDehom j F)) = 0
    rw [← MvPolynomial.sum_homogeneousComponent F, map_sum, map_sum, map_sum]
    apply Finset.sum_eq_zero
    intro d _hd
    have hFd : homogeneousComponent d F ∈ J.toIdeal :=
      MvPolynomial.homogeneousComponent_mem_of_mem J.isHomogeneous hF d
    have h := (GradedQuotient.awayMap_mk_eq_zero_iff (ProjectiveGrading R n) J
      (MvPolynomial.isHomogeneous_X R j) d (homogeneousComponent d F)
      (by simpa using MvPolynomial.homogeneousComponent_mem d F)).mpr ⟨0, by simpa using hFd⟩
    have he : homogeneousChartRatioHom j (coordinateDehom j (homogeneousComponent d F)) =
        Away.mk (ProjectiveGrading R n) (MvPolynomial.isHomogeneous_X R j) d
          (homogeneousComponent d F) (by simpa using MvPolynomial.homogeneousComponent_mem d F) := by
      rw [← homogeneousChartDehom_mk j d (homogeneousComponent d F),
        ← AlgHom.comp_apply, homogeneousChartRatioHom_comp_dehom, AlgHom.id_apply]
    rw [he]
    exact h

end DeJongAlterations.Geometry.ProjectiveIdeal

namespace DeJongAlterations.Geometry.ProjectiveIdeal
variable {R : Type u} [CommRing R] {n : ℕ}
private local instance nativeQuotientSectionChartAlgebra (j : Fin (n + 1)) :
    Algebra R (HomogeneousChartRing R j) := homogeneousChartAlgebra j

set_option backward.isDefEq.respectTransparency false in
/-- The genuine projective quotient kernel sheaf on an actual coordinate open is exactly the original dehomogenized ideal on the whole coordinate ring. -/
theorem homogeneousQuotient_coordinateSectionIdeal (J : HomogeneousIdeal (ProjectiveGrading R n))
    (j : Fin (n + 1)) :
    ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).ideal
      ⟨nativeCoordinateOpen j,
        Proj.isAffineOpen_basicOpen (ProjectiveGrading R n) (X j) (MvPolynomial.isHomogeneous_X R j)
          (by decide : 0 < (1 : ℕ))⟩).comap (nativeCoordinateSectionsIso j).hom.hom =
            J.toIdeal.map (coordinateDehom j).toRingHom := by
  have he : (nativeCoordinateSectionsIso (R := R) j).hom =
      CommRingCat.ofHom (homogeneousChartRatioHom j).toRingHom ≫
        Proj.awayToSection (ProjectiveGrading R n) (X j) := by
    rw [nativeCoordinateSectionsIso, Iso.trans_hom, nativeHomogeneousChartSectionsIso_hom]
    rfl
  rw [he, CommRingCat.hom_comp, ← Ideal.comap_comap]
  erw [GradedQuotient.quotientIdealSheaf_awayToSection_comap (ProjectiveGrading R n) J
    (by decide : 0 < (1 : ℕ)) (MvPolynomial.isHomogeneous_X R j)]
  exact homogeneousQuotient_coordinateKernel J j


end DeJongAlterations.Geometry.ProjectiveIdeal

namespace DeJongAlterations.Geometry.ProjectiveIdeal
variable {R : Type*} [CommRing R] {n : ℕ}
/- Coordinate-cover proof reused from Projective/NativeComparison.lean lines 212--215;
source SHA256 ab7f15203f07e21de6c44582e39fb0a0ed968e71dee8a138def6058de8d3e645. -/
/-- The true coordinate opens cover native polynomial Proj. -/
theorem iSup_nativeCoordinateOpen_eq_top :
    (⨆ j : Fin (n + 1), nativeCoordinateOpen (R := R) j) = ⊤ := by
  apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
  rw [irrelevant_eq_idealOfVars, MvPolynomial.idealOfVars]
end DeJongAlterations.Geometry.ProjectiveIdeal
