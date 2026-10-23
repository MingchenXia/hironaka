/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.ProjectiveIdealExtension

/-!
# Exact same-degree representations of actual projective ideal sheaves

The original native ideal is first represented by actual finite homogeneous
forms, using the pure reused EnvelopeProperty proof chain. Multiplication by
coordinate powers then makes every form have the same degree while preserving
all whole coordinate ideals and hence the actual original ideal sheaf.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

namespace DeJongAlterations.Geometry.ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {n : ℕ}

/-- A finite homogeneous presentation can be replaced by forms of one degree,
with equality of the actual native quotient kernel ideal sheaves. -/
theorem exists_sameDegree_homogeneous_ideal
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (s : Finset (MvPolynomial (Fin (n + 1)) R))
    (hhom : ∀ F ∈ s, ∃ d : ℕ, F.IsHomogeneous d)
    (hs : Ideal.span (s : Set (MvPolynomial (Fin (n + 1)) R)) = J.toIdeal) :
    ∃ (d : ℕ) (t : Finset (MvPolynomial (Fin (n + 1)) R))
      (J' : HomogeneousIdeal (ProjectiveGrading R n)),
      (∀ F ∈ t, F.IsHomogeneous d) ∧
      Ideal.span (t : Set (MvPolynomial (Fin (n + 1)) R)) = J'.toIdeal ∧
      GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J' =
        GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J := by
  classical
  let A := {F : MvPolynomial (Fin (n + 1)) R // F ∈ s}
  choose deg hdeg using fun a : A => hhom a.1 a.2
  let d := Finset.univ.sup deg
  have hd (a : A) : deg a ≤ d := Finset.le_sup (f := deg) (Finset.mem_univ a)
  let G : A × Fin (n + 1) → MvPolynomial (Fin (n + 1)) R :=
    fun a => X a.2 ^ (d - deg a.1) * a.1.1
  have hG (a : A × Fin (n + 1)) : (G a).IsHomogeneous d := by
    have H := (MvPolynomial.isHomogeneous_X_pow a.2 (d - deg a.1)).mul (hdeg a.1)
    simpa only [Nat.sub_add_cancel (hd a.1)] using H
  let J' : HomogeneousIdeal (ProjectiveGrading R n) :=
    ⟨Ideal.span (Set.range G), Ideal.homogeneous_span _ _ (by
      rintro F ⟨a, rfl⟩
      exact ⟨d, hG a⟩)⟩
  have hmap (j : Fin (n + 1)) :
      J'.toIdeal.map (coordinateDehom j).toRingHom =
        J.toIdeal.map (coordinateDehom j).toRingHom := by
    rw [← hs]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      apply Ideal.span_le.mpr
      rintro F ⟨a, rfl⟩
      change coordinateDehom j (G a) ∈
        (Ideal.span (s : Set (MvPolynomial (Fin (n + 1)) R))).map
          (coordinateDehom j).toRingHom
      dsimp only [G]
      rw [map_mul, map_pow]
      exact Ideal.mul_mem_left _ _
        (Ideal.mem_map_of_mem (coordinateDehom j).toRingHom (Ideal.subset_span a.1.2))
    · rw [Ideal.map_le_iff_le_comap]
      apply Ideal.span_le.mpr
      intro F hF
      have hmem : G (⟨F, hF⟩, j) ∈ J'.toIdeal :=
        Ideal.subset_span ⟨(⟨F, hF⟩, j), rfl⟩
      have H := Ideal.mem_map_of_mem (coordinateDehom j).toRingHom hmem
      change coordinateDehom j F ∈ J'.toIdeal.map (coordinateDehom j).toRingHom
      simpa only [G, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow,
        coordinateDehom, MvPolynomial.aeval_X,
        coordinateDehomCoord_self, one_pow, one_mul] using H
  have hsheaf : GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J' =
      GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J := by
    apply Scheme.IdealSheafData.ext_of_iSup_eq_top
      (fun j : Fin (n + 1) => ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩)
      iSup_nativeCoordinateOpen_eq_top
    intro j
    apply Ideal.comap_injective_of_surjective (nativeCoordinateSectionsIso (R := R) j).hom.hom
      (nativeCoordinateSectionsIso (R := R) j).commRingCatIsoToRingEquiv.surjective
    rw [homogeneousQuotient_coordinateSectionIdeal, homogeneousQuotient_coordinateSectionIdeal,
      hmap]
  refine ⟨d, (Set.finite_range G).toFinset, J', ?_, ?_, hsheaf⟩
  · intro F hF
    obtain ⟨a, rfl⟩ := (Set.Finite.mem_toFinset (Set.finite_range G)).mp hF
    exact hG a
  · simp only [Set.Finite.coe_toFinset]
    rfl

/-- Every actual projective ideal sheaf has finite same-degree ambient forms
whose native homogeneous quotient kernel pulls back to the entire original ideal. -/
theorem exists_sameDegree_homogeneous_generators_of_isClosedImmersion
    [IsNoetherianRing R] {X : Scheme.{u}} (D : X.IdealSheafData)
    (j : X ⟶ projectiveSpace R n) [IsClosedImmersion j] :
    ∃ (d : ℕ) (s : Finset (MvPolynomial (Fin (n + 1)) R))
      (J : HomogeneousIdeal (ProjectiveGrading R n)),
      (∀ F ∈ s, F.IsHomogeneous d) ∧
      Ideal.span (s : Set (MvPolynomial (Fin (n + 1)) R)) = J.toIdeal ∧
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j = D := by
  obtain ⟨J, s, hhom, hs, hD⟩ :=
    exists_finite_homogeneous_generators_comap_quotientIdealSheaf_eq_of_isClosedImmersion D j
  obtain ⟨d, t, J', hdeg, hspan, heq⟩ := exists_sameDegree_homogeneous_ideal J s hhom hs
  exact ⟨d, t, J', hdeg, hspan, by rw [heq]; exact hD⟩

end DeJongAlterations.Geometry.ProjectiveIdeal
