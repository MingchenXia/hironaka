import DeJongAlterations.Geometry.FiniteProjectiveAffineMap
import DeJongAlterations.Geometry.PrincipalBlowup
import DeJongAlterations.Geometry.AffineBlowupIsomorphism
import DeJongAlterations.Geometry.ProjectiveSpaceBaseChange

/-!
# Exact inverse coordinate opens of the native affine tuple map

Over every commutative ring, the unit-ideal Rees chart of a coefficient is
exactly the inverse image of its principal open under the actual structure
isomorphism. Thus the native tuple map has its stated coordinate preimages.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial MvPolynomial

namespace DeJongAlterations.Geometry.FiniteProjective

open BlowupProjectiveEmbedding UnitIdealBlowup ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R A : Type u} [CommRing R] [CommRing A] {m : ℕ}

/-- The degree-one unit chart is the whole actual unit-ideal blowup, over every ring. -/
theorem unitIdeal_oneChart_eq_top :
    affineBlowupChartOpen (⊤ : Ideal A) 1 (by trivial) = ⊤ := by
  apply top_unique
  rw [← iSup_affineBlowupChartOpen (⊤ : Ideal A)]
  apply iSup_le
  intro a
  have H : reesDegreeOne (⊤ : Ideal A) a a.property =
      algebraMap A (reesAlgebra (⊤ : Ideal A)) a * reesDegreeOne ⊤ 1 (by trivial) := by
    apply Subtype.ext
    change Polynomial.monomial 1 (a : A) = Polynomial.C (a : A) * Polynomial.monomial 1 1
    simp
  change Proj.basicOpen _ (reesDegreeOne (⊤ : Ideal A) a a.property) ≤
    Proj.basicOpen _ (reesDegreeOne (⊤ : Ideal A) 1 _)
  rw [H, Proj.basicOpen_mul]
  exact inf_le_right

/-- Actual unit-ideal blowup coefficient charts retain their original principal opens. -/
theorem unitIdeal_structure_preimage_basicOpen (a : A) :
    affineBlowupStructure (⊤ : Ideal A) ⁻¹ᵁ PrimeSpectrum.basicOpen a =
      affineBlowupChartOpen ⊤ a (by trivial) := by
  rw [affineBlowupStructure_preimage_basicOpen]
  have ha : reesDegreeOne (⊤ : Ideal A) a (by trivial) =
      algebraMap A (reesAlgebra (⊤ : Ideal A)) a * reesDegreeOne ⊤ 1 (by trivial) := by
    apply Subtype.ext
    change Polynomial.monomial 1 a = Polynomial.C a * Polynomial.monomial 1 1
    simp
  change _ = Proj.basicOpen _ (reesDegreeOne (⊤ : Ideal A) a _)
  rw [ha, Proj.basicOpen_mul]
  change _ = _ ⊓ affineBlowupChartOpen (⊤ : Ideal A) 1 _
  rw [unitIdeal_oneChart_eq_top, inf_top_eq]

/-- The native coefficient-field tuple map has its exact actual coordinate preimage. -/
theorem affineTupleMap_preimage_coordinate (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) :
    affineTupleMap r a ha ⁻¹ᵁ nativeCoordinateOpen i = PrimeSpectrum.basicOpen (a i) := by
  rw [affineTupleMap, Scheme.Hom.comp_preimage, affineProjectiveMap,
    Scheme.Hom.comp_preimage, ProjectiveSpaceBaseChange.nativeCoefficientMap_preimage_coordinateOpen]
  change (unitIdealBlowupIso A).inv ⁻¹ᵁ
      (Proj.map (generatorPolynomialMap ⊤ a ha).toGradedRingHom _ ⁻¹ᵁ
        Proj.basicOpen (projectiveSpaceGrading A m) (MvPolynomial.X i)) = _
  rw [Proj.map_preimage_basicOpen]
  have hx : (generatorPolynomialMap (⊤ : Ideal A) a ha).toGradedRingHom (MvPolynomial.X i) =
      reesDegreeOne ⊤ (a i) (by trivial) := by
    change DeJongAlterations.Algebra.ReesPresentation.reesPolynomialEval ⊤ a _
      (MvPolynomial.X i) = _
    simp only [DeJongAlterations.Algebra.ReesPresentation.reesPolynomialEval, MvPolynomial.aeval_X]
  rw [hx]
  change (unitIdealBlowupIso A).inv ⁻¹ᵁ affineBlowupChartOpen ⊤ (a i) _ = _
  rw [← unitIdeal_structure_preimage_basicOpen]
  change ((unitIdealBlowupIso A).inv ≫ (unitIdealBlowupIso A).hom) ⁻¹ᵁ
    PrimeSpectrum.basicOpen (a i) = _
  rw [Iso.inv_hom_id]
  rfl

end DeJongAlterations.Geometry.FiniteProjective
