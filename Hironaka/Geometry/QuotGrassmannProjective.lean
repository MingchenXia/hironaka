import Hironaka.Algebra.PluckerQuotHomogeneous
import Hironaka.Geometry.ProjectiveIdealQuotient
import Hironaka.Geometry.ProjectiveIdealCoordinateIdeal
import Hironaka.Geometry.ProjectiveModification

/-!
# The actual projective scheme defined by the original homogeneous minor relations

All coordinates, the homogeneous ideal, the native graded quotient, its literal
closed immersion and projective structure map are constructed internally. The
actual standard affine opens with injective original pivot selectors cover it.
Identification with the normalized affine matrix charts and gluing the global
universal quotient remain separate proofs; scheme representability is not assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι κ : Type u)
  [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- The internally determined finite ambient projective dimension. -/
def pluckerDimension : ℕ := Fintype.card (ι → ι ⊕ κ) - 1

/-- The original finite projective coordinates enumerate all original maximal-minor selectors. -/
def coordinateSelector : Fin (pluckerDimension ι κ + 1) ≃ (ι → ι ⊕ κ) := by
  let : Nonempty (ι → ι ⊕ κ) := ⟨Sum.inl⟩
  have hcard : 1 ≤ Fintype.card (ι → ι ⊕ κ) := Nat.succ_le_of_lt Fintype.card_pos
  exact (Equiv.cast (congrArg Fin (Nat.sub_add_cancel hcard))).trans (Fintype.equivFin _).symm

/-- The actual homogeneous ideal of all original generic maximal-minor identities. -/
def pluckerIdeal : HomogeneousIdeal (projectiveSpaceGrading R (pluckerDimension ι κ)) :=
  minorRelationIdeal R ι (ι ⊕ κ) (Fin (pluckerDimension ι κ + 1)) (coordinateSelector ι κ)

/-- The native projective spectrum of the literal homogeneous minor-relation quotient. -/
def projectiveModel : Scheme.{u} :=
  Proj (GradedQuotient.grading (projectiveSpaceGrading R (pluckerDimension ι κ))
    (pluckerIdeal R ι κ).toIdeal)

/-- The literal closed Plücker-coordinate immersion into the actual ambient projective space. -/
def projectiveInclusion : projectiveModel R ι κ ⟶ projectiveSpace R (pluckerDimension ι κ) :=
  GradedQuotient.quotientSchemeMap (projectiveSpaceGrading R (pluckerDimension ι κ))
    (pluckerIdeal R ι κ)

instance projectiveInclusion_isClosedImmersion : IsClosedImmersion (projectiveInclusion R ι κ) :=
  inferInstanceAs (IsClosedImmersion (GradedQuotient.quotientSchemeMap _ _))

/-- The actual original coefficient structure morphism of the constructed projective model. -/
def projectiveStructure : projectiveModel R ι κ ⟶ Spec (.of R) :=
  projectiveInclusion R ι κ ≫ projectiveSpaceStructure R (pluckerDimension ι κ)

/-- Projectivity is proved using the literal constructed closed immersion and coefficient map. -/
theorem projectiveStructure_isProjective : IsProjectiveOver (projectiveStructure R ι κ) :=
  ⟨pluckerDimension ι κ, projectiveInclusion R ι κ, inferInstance, rfl⟩

instance projectiveStructure_isProper : IsProper (projectiveStructure R ι κ) :=
  (projectiveStructure_isProjective R ι κ).isProper

/-- An actual native homogeneous-coordinate open of the same constructed projective model. -/
def coordinateOpen (j : Fin (pluckerDimension ι κ + 1)) : (projectiveModel R ι κ).Opens :=
  Proj.basicOpen
    (GradedQuotient.grading (projectiveSpaceGrading R (pluckerDimension ι κ))
      (pluckerIdeal R ι κ).toIdeal)
    (GradedQuotient.gradedMk (projectiveSpaceGrading R (pluckerDimension ι κ))
      (pluckerIdeal R ι κ).toIdeal (MvPolynomial.X j))

/-- The original literal projective inclusion preserves the entire original coordinate open. -/
theorem preimage_coordinateOpen (j : Fin (pluckerDimension ι κ + 1)) :
    projectiveInclusion R ι κ ⁻¹ᵁ nativeCoordinateOpen j = coordinateOpen R ι κ j :=
  by
    dsimp only [projectiveInclusion, GradedQuotient.quotientSchemeMap,
      nativeCoordinateOpen, coordinateOpen]
    exact Proj.map_preimage_basicOpen _ _ _

/-- Every actual homogeneous coordinate open is genuinely affine. -/
theorem coordinateOpen_isAffine (j : Fin (pluckerDimension ι κ + 1)) :
    IsAffineOpen (coordinateOpen R ι κ j) := by
  let e := Proj.basicOpenIsoSpec
    (GradedQuotient.grading (projectiveSpaceGrading R (pluckerDimension ι κ))
      (pluckerIdeal R ι κ).toIdeal)
    (GradedQuotient.gradedMk (projectiveSpaceGrading R (pluckerDimension ι κ))
      (pluckerIdeal R ι κ).toIdeal (MvPolynomial.X j))
    ((GradedQuotient.gradedMk (projectiveSpaceGrading R (pluckerDimension ι κ))
      (pluckerIdeal R ι κ).toIdeal).map_mem
      (MvPolynomial.isHomogeneous_X R j)) (by decide : 0 < (1 : ℕ))
  dsimp only [coordinateOpen]
  exact IsAffine.of_isIso e.hom

/-- These are the actual standard opens of one native scheme and cover that whole scheme. -/
theorem iSup_coordinateOpen_eq_top :
    ⨆ j, coordinateOpen R ι κ j = ⊤ := by
  simp_rw [← preimage_coordinateOpen]
  rw [← Scheme.Hom.preimage_iSup, iSup_nativeCoordinateOpen_eq_top]
  exact Scheme.Hom.preimage_top _

/-- Noninjective original selectors give empty opens of the actual quotient scheme. -/
theorem coordinateOpen_eq_bot_of_not_injective (j : Fin (pluckerDimension ι κ + 1))
    (hj : ¬ Function.Injective (coordinateSelector ι κ j)) :
    coordinateOpen R ι κ j = ⊥ := by
  have hmem : MvPolynomial.X j ∈ (pluckerIdeal R ι κ).toIdeal :=
    X_mem_minorRelationIdeal_of_not_injective R ι (ι ⊕ κ)
      (Fin (pluckerDimension ι κ + 1)) (coordinateSelector ι κ) j hj
  have hz : GradedQuotient.gradedMk (projectiveSpaceGrading R (pluckerDimension ι κ))
      (pluckerIdeal R ι κ).toIdeal (MvPolynomial.X j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  dsimp only [coordinateOpen]
  rw [hz, Proj.basicOpen_zero]

/-- Genuine injective-pivot affine opens cover the entire constructed projective scheme. -/
theorem iSup_pivotOpen_eq_top :
    ⨆ j : {j : Fin (pluckerDimension ι κ + 1) //
      Function.Injective (coordinateSelector ι κ j)}, coordinateOpen R ι κ j.val = ⊤ := by
  apply top_le_iff.mp
  rw [← iSup_coordinateOpen_eq_top R ι κ]
  apply iSup_le
  intro j
  by_cases hj : Function.Injective (coordinateSelector ι κ j)
  · exact le_iSup_of_le ⟨j, hj⟩ le_rfl
  · rw [coordinateOpen_eq_bot_of_not_injective R ι κ j hj]
    exact bot_le

end Hironaka.Geometry.QuotGrassmann
