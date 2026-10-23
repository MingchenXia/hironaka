import DeJongAlterations.StableModificationBridge.NativeTupleSection
import DeJongAlterations.StableModification.Projectivity.SectionsMap
import DeJongAlterations.StableModification.Projectivity.LineBundleOps

/-!
# Whole original coefficient ratios of a generated section map

The equalities are on the entire actual affine section rings, over arbitrary coefficient rings.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Opposite

namespace DeJongAlterations.StableModificationBridge.GeneratedSectionRatio

open Geometry.FiniteProjective Geometry.ProjectiveIdeal Geometry.BlowupProjectiveEmbedding
  NativeTupleRatio NativeTupleSection StableModification.Projectivity

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {N : ℕ}

/-- If the original whole morphism from an affine open is a unit-marker tuple map, its entire
native coordinate-section pullback is the original tuple coefficient. -/
theorem affine_marker_ratio (g : X ⟶ projectiveSpace R N) (V : X.affineOpens)
    (r : R →+* Γ(X, V.1)) (a : Fin (N + 1) → Γ(X, V.1))
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (N + 1)) (hi : a i = 1)
    (hmap : V.2.fromSpec ≫ g = affineTupleMap r a ha)
    (hV : V.1 ≤ g ⁻¹ᵁ nativeCoordinateOpen i) (j : Fin (N + 1)) :
    g.appLE (nativeCoordinateOpen i) V.1 hV (nativeFormSection i (MvPolynomial.X j)) = a j := by
  have H := (nativeCoordinateOpen_isAffine (R := R) i).SpecMap_appLE_fromSpec g V.2 hV
  rw [← nativeAwayToSection_spec i, hmap, affineTupleMap_factor_marker r a ha i hi] at H
  have He : Proj.awayToSection (projectiveSpaceGrading R N) (MvPolynomial.X i) ≫
      g.appLE (nativeCoordinateOpen i) V.1 hV = CommRingCat.ofHom (markerHom r a ha i hi) := by
    apply Spec.map_injective
    apply (cancel_mono (Proj.awayι (projectiveSpaceGrading R N) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one)).mp
    simpa only [Spec.map_comp, Category.assoc] using H
  rw [nativeFormSection_X]
  have Hv := ConcreteCategory.congr_hom He
    (HomogeneousLocalization.Away.mk (projectiveSpaceGrading R N)
      (MvPolynomial.isHomogeneous_X R i) 1 (MvPolynomial.X j)
      (by simpa only [one_smul, projectiveSpaceGrading,
        MvPolynomial.mem_homogeneousSubmodule] using MvPolynomial.isHomogeneous_X R j))
  change _ = markerHom r a ha i hi _ at Hv
  rw [markerHom_ratio] at Hv
  exact Hv

/-- An original unit coefficient gives the whole native coordinate quotient identity. -/
theorem affine_unit_ratio (g : X ⟶ projectiveSpace R N) (V : X.affineOpens)
    (r : R →+* Γ(X, V.1)) (a : Fin (N + 1) → Γ(X, V.1))
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (N + 1)) (hi : IsUnit (a i))
    (hmap : V.2.fromSpec ≫ g = affineTupleMap r a ha)
    (hV : V.1 ≤ g ⁻¹ᵁ nativeCoordinateOpen i) (j : Fin (N + 1)) :
    g.appLE (nativeCoordinateOpen i) V.1 hV (nativeFormSection i (MvPolynomial.X j)) * a i =
      a j := by
  obtain ⟨u, hu⟩ := hi
  let b : Fin (N + 1) → Γ(X, V.1) := fun j => (u⁻¹ : Γ(X, V.1)ˣ) * a j
  let hb := generator_span_unit ⊤ a ha u⁻¹
  have hbi : b i = 1 := by
    dsimp only [b]
    rw [← hu, Units.inv_mul]
  have hmapb : V.2.fromSpec ≫ g = affineTupleMap r b hb :=
    hmap.trans (affineTupleMap_unit r a ha u⁻¹).symm
  have H := affine_marker_ratio g V r b hb i hbi hmapb hV j
  rw [H, ← hu]
  change ((↑u⁻¹ : Γ(X, V.1)) * a j) * ↑u = a j
  rw [mul_right_comm, Units.inv_mul, one_mul]

/-- On an actual affine open in an original line-bundle chart, the entire native generated
map pulls each coordinate ratio back to the corresponding original section coefficient ratio. -/
theorem toProjectiveSpace_ratio {L : LineBundleData X} {m : ℤ}
    (p : X ⟶ Spec (.of R)) {s : Fin (N + 1) → L.Sections m ⊤}
    (hs : LineBundleData.Generates s) (V : X.affineOpens) (k : L.ι) (hVk : V.1 ≤ L.U k)
    (i : Fin (N + 1)) (hVi : V.1 ≤ (s i).nonvanishingLocus) (j : Fin (N + 1)) :
    (LineBundleData.toProjectiveSpace p hs).appLE (nativeCoordinateOpen i) V.1
        (by rw [LineBundleData.toProjectiveSpace_preimage_coordinate]; exact hVi)
        (nativeFormSection i (MvPolynomial.X j)) * LineBundleData.localValue (s i) k hVk =
      LineBundleData.localValue (s j) k hVk := by
  let a : Fin (N + 1) → Γ(X, V.1) := fun j => LineBundleData.localValue (s j) k hVk
  have hi : IsUnit (a i) := by
    apply isUnit_of_basicOpen_eq
    rw [LineBundleData.basicOpen_localValue]
    exact inf_eq_left.mpr hVi
  have hmap : V.2.fromSpec ≫ LineBundleData.toProjectiveSpace p hs =
      affineTupleMap (affineBaseCoefficients p V) a (LineBundleData.localSpan hs V k hVk) := by
    rw [IsAffineOpen.fromSpec, Category.assoc, LineBundleData.toProjectiveSpace_restrict]
    change V.2.isoSpec.inv ≫ (V.2.isoSpec.hom ≫ _) = _
    rw [Iso.inv_hom_id_assoc]
  exact affine_unit_ratio _ V (affineBaseCoefficients p V) a
    (LineBundleData.localSpan hs V k hVk) i hi hmap _ j

end DeJongAlterations.StableModificationBridge.GeneratedSectionRatio
