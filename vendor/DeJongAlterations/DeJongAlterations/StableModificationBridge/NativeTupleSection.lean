import DeJongAlterations.StableModificationBridge.NativeTupleRatio

/-!
# Actual pullback of whole native coordinate sections

The coordinate fraction is transported through the genuine original affine scheme morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace DeJongAlterations.StableModificationBridge.NativeTupleSection

open Geometry.FiniteProjective Geometry.ProjectiveIdeal NativeTupleRatio

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R A : Type u} [CommRing R] [CommRing A] {N : ℕ}

/-- Native homogeneous fraction sections have the original whole affine-chart triangle over
an arbitrary coefficient ring. -/
@[reassoc]
theorem nativeAwayToSection_spec (i : Fin (N + 1)) :
    Spec.map (Proj.awayToSection (projectiveSpaceGrading R N) (X i)) ≫
      Proj.awayι (projectiveSpaceGrading R N) (X i)
        (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one =
      (nativeCoordinateOpen_isAffine (R := R) i).fromSpec := by
  let U := nativeCoordinateOpen (R := R) i
  let hU := nativeCoordinateOpen_isAffine (R := R) i
  let : IsIso U.toSpecΓ := by
    rw [← hU.isoSpec_hom]
    infer_instance
  apply (cancel_epi U.toSpecΓ).mp
  rw [← Category.assoc]
  change (Proj.basicOpenIsoSpec (projectiveSpaceGrading R N) (X i)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one).hom ≫
      ((Proj.basicOpenIsoSpec (projectiveSpaceGrading R N) (X i)
        (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one).inv ≫ U.ι) =
      U.toSpecΓ ≫ hU.fromSpec
  rw [Iso.hom_inv_id_assoc, hU.toSpecΓ_fromSpec]

/-- The whole actual affine tuple pullback is the marker chart homomorphism, with the original
global-section comparison of the source spectrum. -/
theorem marker_appLE_comp (r : R →+* A) (a : Fin (N + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (N + 1)) (hi : a i = 1)
    (htop : (⊤ : (Spec (.of A)).Opens) ≤ affineTupleMap r a ha ⁻¹ᵁ nativeCoordinateOpen i) :
    Proj.awayToSection (projectiveSpaceGrading R N) (X i) ≫
        (affineTupleMap r a ha).appLE (nativeCoordinateOpen i) ⊤ htop =
      CommRingCat.ofHom (markerHom r a ha i hi) ≫ (Scheme.ΓSpecIso (.of A)).inv := by
  let hV := nativeCoordinateOpen_isAffine (R := R) i
  let hU := isAffineOpen_top (Spec (.of A))
  have hsource : hU.fromSpec = Spec.map (Scheme.ΓSpecIso (.of A)).inv := by
    rw [IsAffineOpen.fromSpec_top]
    apply (cancel_mono (Spec (.of A)).toSpecΓ).mp
    rw [Scheme.isoSpec_inv_toSpecΓ, SpecMap_ΓSpecIso_inv_toSpecΓ]
  have H := hV.SpecMap_appLE_fromSpec (affineTupleMap r a ha) hU htop
  rw [← nativeAwayToSection_spec i, hsource] at H
  conv_rhs at H => rw [affineTupleMap_factor_marker r a ha i hi]
  apply Spec.map_injective
  apply (cancel_mono (Proj.awayι (projectiveSpaceGrading R N) (X i)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one)).mp
  simpa only [Spec.map_comp, Category.assoc] using H

/-- The actual coordinate section is exactly its genuine homogeneous degree-zero fraction. -/
theorem nativeFormSection_X (i j : Fin (N + 1)) :
    nativeFormSection (R := R) i (X j) =
      Proj.awayToSection (projectiveSpaceGrading R N) (X i)
        (HomogeneousLocalization.Away.mk (projectiveSpaceGrading R N)
          (MvPolynomial.isHomogeneous_X R i) 1 (X j)
          (by simpa only [one_smul, projectiveSpaceGrading,
            MvPolynomial.mem_homogeneousSubmodule] using MvPolynomial.isHomogeneous_X R j)) := by
  rw [nativeFormSection, nativeCoordinateSectionsIso, Iso.trans_hom,
    nativeHomogeneousChartSectionsIso_hom]
  change Proj.awayToSection (projectiveSpaceGrading R N) (X i)
      (homogeneousChartRatioHom i (coordinateDehom i (X j))) = _
  rw [homogeneousChartRatioHom_dehom_of_isHomogeneous i (MvPolynomial.isHomogeneous_X R j)]

/-- The native whole coordinate-section pullback of a unit-marker tuple is its original
coefficient, with no reduction of the source or field restriction. -/
theorem marker_appLE_ratio (r : R →+* A) (a : Fin (N + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (N + 1)) (hi : a i = 1)
    (htop : (⊤ : (Spec (.of A)).Opens) ≤ affineTupleMap r a ha ⁻¹ᵁ nativeCoordinateOpen i)
    (j : Fin (N + 1)) :
    (affineTupleMap r a ha).appLE (nativeCoordinateOpen i) ⊤ htop
      (nativeFormSection i (X j)) = (Scheme.ΓSpecIso (.of A)).inv (a j) := by
  rw [nativeFormSection_X]
  have H := ConcreteCategory.congr_hom (marker_appLE_comp r a ha i hi htop)
    (HomogeneousLocalization.Away.mk (projectiveSpaceGrading R N)
      (MvPolynomial.isHomogeneous_X R i) 1 (X j)
      (by simpa only [one_smul, projectiveSpaceGrading,
        MvPolynomial.mem_homogeneousSubmodule] using MvPolynomial.isHomogeneous_X R j))
  change _ = (Scheme.ΓSpecIso (.of A)).inv (markerHom r a ha i hi _) at H
  rw [markerHom_ratio] at H
  exact H

end DeJongAlterations.StableModificationBridge.NativeTupleSection
