/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Geometry.ProjectiveIdealPushforward
import DeJongAlterations.Geometry.ProjectiveIdealFinite
/- Reused from EnvelopeProperty/Projective/IdealExtension.lean; SHA256 1261574a4755aecc6d5caa68a0b34579053ae00a296d4f46e90f092069014abc. -/


/-!
# Actual homogeneous ambient representations through genuine projective embeddings

Extend the ORIGINAL source ideal through its true closed subscheme composite,
construct the actual ambient homogeneous ideal, and pull it back along the real
closed immersion. Entire ideal data and actual finite homogeneous generators
are retained. No radical, representation witness, Noetherian assumption in the
unrestricted construction, or descent along a proper modification is used.
-/

open scoped Classical
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace DeJongAlterations.Geometry.ProjectiveIdeal
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {n : ℕ} {Z : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The original source ideal is exactly the actual geometric pullback of its constructed ambient homogeneous quotient kernel. -/
theorem homogeneousRepresentative_comap_eq_of_isClosedImmersion
    (I : Z.IdealSheafData) (j : Z ⟶ NativeProjectiveScheme R n) [IsClosedImmersion j] :
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n)
      (nativeHomogeneousRepresentative (I.map j))).comap j = I := by
  rw [nativeHomogeneousRepresentative_quotientIdealSheaf,
    Scheme.IdealSheafData.comap_map_of_isClosedImmersion]

/-- Every actual source ideal has a genuine homogeneous ambient ideal through a true polynomial projective embedding. -/
theorem exists_homogeneous_ideal_comap_quotientIdealSheaf_eq_of_isClosedImmersion
    (I : Z.IdealSheafData) (j : Z ⟶ NativeProjectiveScheme R n) [IsClosedImmersion j] :
    ∃ J : HomogeneousIdeal (ProjectiveGrading R n),
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j = I :=
  ⟨nativeHomogeneousRepresentative (I.map j),
    homogeneousRepresentative_comap_eq_of_isClosedImmersion I j⟩

set_option backward.isDefEq.respectTransparency false in
/-- Genuine finite generation of the actual ambient extension coordinate ideals gives finite original homogeneous generators for the exact source ideal pullback. -/
theorem exists_finite_homogeneous_generators_comap_quotientIdealSheaf_eq_of_coordinate_fg
    (I : Z.IdealSheafData) (j : Z ⟶ NativeProjectiveScheme R n) [IsClosedImmersion j]
    (hfg : ∀ a : Fin (n + 1), (nativeCoordinateIdeal (I.map j) a).FG) :
    ∃ (J : HomogeneousIdeal (ProjectiveGrading R n))
      (s : Finset (MvPolynomial (Fin (n + 1)) R)),
      (∀ F ∈ s, ∃ d : ℕ, F.IsHomogeneous d) ∧
      Ideal.span (s : Set (MvPolynomial (Fin (n + 1)) R)) = J.toIdeal ∧
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j = I := by
  obtain ⟨J, s, hhom, hspan, hJ⟩ :=
    exists_finite_homogeneous_generators_quotientIdealSheaf_of_coordinate_fg (I.map j) hfg
  refine ⟨J, s, hhom, hspan, ?_⟩
  rw [hJ, Scheme.IdealSheafData.comap_map_of_isClosedImmersion]

/-- A genuinely Noetherian coefficient ring gives actual finite homogeneous ambient generators for every original source ideal under a true projective embedding. -/
theorem exists_finite_homogeneous_generators_comap_quotientIdealSheaf_eq_of_isClosedImmersion
    [IsNoetherianRing R] (I : Z.IdealSheafData) (j : Z ⟶ NativeProjectiveScheme R n)
    [IsClosedImmersion j] :
    ∃ (J : HomogeneousIdeal (ProjectiveGrading R n))
      (s : Finset (MvPolynomial (Fin (n + 1)) R)),
      (∀ F ∈ s, ∃ d : ℕ, F.IsHomogeneous d) ∧
      Ideal.span (s : Set (MvPolynomial (Fin (n + 1)) R)) = J.toIdeal ∧
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j = I :=
  exists_finite_homogeneous_generators_comap_quotientIdealSheaf_eq_of_coordinate_fg I j
    (nativeCoordinateIdeal_fg (I.map j))

end DeJongAlterations.Geometry.ProjectiveIdeal
