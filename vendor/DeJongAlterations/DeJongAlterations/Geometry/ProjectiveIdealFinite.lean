/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Geometry.ProjectiveIdealRepresentation
/- Reused from EnvelopeProperty/Projective/IdealRepresentationFinite.lean; SHA256 1da575e817a25d8e483bd28c29da72ecefb8eee8f99a1ddaa5cde738a383f9b3. -/


/-!
# Finite homogeneous representatives of actual projective ideal sheaves

Actual finite generation of the original coordinate ideals suffices: the
original homogeneous numerator and true overlap-clearing producers construct
finite homogeneous polynomial generators with exactly the original quotient
kernel sheaf. The base need not be Noetherian. Genuine Noetherian coefficient
rings discharge coordinate finite generation as a separate corollary. No
analytic coherent-sheaf identification or recovery of a previous graded ideal
is asserted.
-/

open scoped Classical
open CategoryTheory AlgebraicGeometry MvPolynomial
noncomputable section
universe u
namespace DeJongAlterations.Geometry.ProjectiveIdeal
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {n : ℕ}

/-- Actual generator membership has an original homogeneous representative in the whole original chart construction. -/
theorem exists_homogeneousRepresentative_coordinate_lift
    (I : (NativeProjectiveScheme R n).IdealSheafData) (j : Fin (n + 1))
    {a : CoordinateRing R j} (ha : a ∈ nativeCoordinateIdeal I j) :
    ∃ (F : MvPolynomial (Fin (n + 1)) R) (d : ℕ),
      F.IsHomogeneous d ∧ F ∈ nativeHomogeneousRepresentative I ∧ coordinateDehom j F = a := by
  obtain ⟨d, F, hF, he⟩ := exists_homogeneous_coordinateDehom j a
  obtain ⟨N, hN⟩ := exists_nativeHomogeneousRepresentative_power_mem I j hF (he ▸ ha)
  refine ⟨X j ^ N * F, N + d, (MvPolynomial.isHomogeneous_X_pow j N).mul hF, hN, ?_⟩
  have hX : coordinateDehom (R := R) j (X j) = 1 := by
    simp only [coordinateDehom, MvPolynomial.aeval_X, coordinateDehomCoord_self]
  simp only [map_mul, map_pow, hX, one_pow, one_mul, he]

set_option backward.isDefEq.respectTransparency false in
/-- Genuine finite generation of the original coordinate ideals produces actual finite homogeneous generators with the entire original quotient kernel sheaf. -/
theorem exists_finite_homogeneous_generators_quotientIdealSheaf_of_coordinate_fg
    (I : (NativeProjectiveScheme R n).IdealSheafData)
    (hfg : ∀ j : Fin (n + 1), (nativeCoordinateIdeal I j).FG) :
    ∃ (J : HomogeneousIdeal (ProjectiveGrading R n))
      (s : Finset (MvPolynomial (Fin (n + 1)) R)),
      (∀ F ∈ s, ∃ d : ℕ, F.IsHomogeneous d) ∧
      Ideal.span (s : Set (MvPolynomial (Fin (n + 1)) R)) = J.toIdeal ∧
      GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J = I := by
  choose m f hf using fun j => Submodule.fg_iff_exists_fin_generating_family.mp (hfg j)
  let T := Σ j : Fin (n + 1), Fin (m j)
  have hmem (t : T) : f t.1 t.2 ∈ nativeCoordinateIdeal I t.1 := by
    rw [← hf t.1]
    exact Submodule.subset_span ⟨t.2, rfl⟩
  choose G d hG hGin hGe using fun t : T =>
    exists_homogeneousRepresentative_coordinate_lift I t.1 (hmem t)
  let J : HomogeneousIdeal (ProjectiveGrading R n) :=
    ⟨Ideal.span (Set.range G), Ideal.homogeneous_span _ _ (by
      rintro F ⟨t, rfl⟩
      exact ⟨d t, hG t⟩)⟩
  have hJ : J.toIdeal ≤ (nativeHomogeneousRepresentative I).toIdeal := by
    apply Ideal.span_le.mpr
    rintro F ⟨t, rfl⟩
    exact hGin t
  have hEq (j : Fin (n + 1)) :
      J.toIdeal.map (coordinateDehom j).toRingHom = nativeCoordinateIdeal I j := by
    refine le_antisymm ((Ideal.map_mono hJ).trans (nativeHomogeneousRepresentative_dehom_le I j)) ?_
    have hf' : Ideal.span (Set.range (f j)) = nativeCoordinateIdeal I j := hf j
    rw [← hf']
    apply Ideal.span_le.mpr
    rintro a ⟨i, rfl⟩
    rw [← hGe ⟨j, i⟩]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨⟨j, i⟩, rfl⟩)
  refine ⟨J, (Set.finite_range G).toFinset, ?_, ?_, ?_⟩
  · intro F hF
    obtain ⟨t, rfl⟩ := (Set.Finite.mem_toFinset (Set.finite_range G)).mp hF
    exact ⟨d t, hG t⟩
  · simp only [Set.Finite.coe_toFinset]
    rfl
  · apply Scheme.IdealSheafData.ext_of_iSup_eq_top
      (fun j : Fin (n + 1) => ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩)
      iSup_nativeCoordinateOpen_eq_top
    intro j
    apply Ideal.comap_injective_of_surjective
      (nativeCoordinateSectionsIso (R := R) j).hom.hom
      (nativeCoordinateSectionsIso (R := R) j).commRingCatIsoToRingEquiv.surjective
    rw [homogeneousQuotient_coordinateSectionIdeal, hEq]
    rfl

/-- True finite generation of original coordinate ideals gives an actual finitely generated homogeneous representative. -/
theorem exists_finite_homogeneous_ideal_quotientIdealSheaf_of_coordinate_fg
    (I : (NativeProjectiveScheme R n).IdealSheafData)
    (hfg : ∀ j : Fin (n + 1), (nativeCoordinateIdeal I j).FG) :
    ∃ J : HomogeneousIdeal (ProjectiveGrading R n),
      J.toIdeal.FG ∧ GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J = I := by
  obtain ⟨J, s, _hs, he, hI⟩ :=
    exists_finite_homogeneous_generators_quotientIdealSheaf_of_coordinate_fg I hfg
  exact ⟨J, ⟨s, he⟩, hI⟩

/-- A genuinely Noetherian coefficient ring makes each entire actual coordinate ideal finitely generated. -/
theorem nativeCoordinateIdeal_fg [IsNoetherianRing R]
    (I : (NativeProjectiveScheme R n).IdealSheafData) (j : Fin (n + 1)) :
    (nativeCoordinateIdeal I j).FG := IsNoetherian.noetherian _

/-- Over a genuinely Noetherian base every actual projective ideal sheaf has actual finite homogeneous polynomial generators. -/
theorem exists_finite_homogeneous_generators_quotientIdealSheaf [IsNoetherianRing R]
    (I : (NativeProjectiveScheme R n).IdealSheafData) :
    ∃ (J : HomogeneousIdeal (ProjectiveGrading R n))
      (s : Finset (MvPolynomial (Fin (n + 1)) R)),
      (∀ F ∈ s, ∃ d : ℕ, F.IsHomogeneous d) ∧
      Ideal.span (s : Set (MvPolynomial (Fin (n + 1)) R)) = J.toIdeal ∧
      GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J = I :=
  exists_finite_homogeneous_generators_quotientIdealSheaf_of_coordinate_fg I
    (nativeCoordinateIdeal_fg I)

/-- Over a genuinely Noetherian base every actual projective ideal sheaf has an actual finitely generated homogeneous representative. -/
theorem exists_finite_homogeneous_ideal_quotientIdealSheaf [IsNoetherianRing R]
    (I : (NativeProjectiveScheme R n).IdealSheafData) :
    ∃ J : HomogeneousIdeal (ProjectiveGrading R n),
      J.toIdeal.FG ∧ GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J = I :=
  exists_finite_homogeneous_ideal_quotientIdealSheaf_of_coordinate_fg I (nativeCoordinateIdeal_fg I)

end DeJongAlterations.Geometry.ProjectiveIdeal
