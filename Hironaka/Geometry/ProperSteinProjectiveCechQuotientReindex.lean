/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProjectiveIdealQuotient
import Hironaka.Geometry.ProjClosedImmersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Actual variable equivalences preserve the WHOLE original homogeneous quotient

The native coordinate rename pattern is adapted from same-workspace
`EnvelopeProperty/EnvelopeProperty/PolynomialProjReindex.lean`,
SHA256 16d61bd6e10d29bceedcf9819a45dc9bb338e7a3de26aad77cf49d9c00c0b538.
Its analytic/valued-point tail and ALL other-project imports are excluded.
The actual quotient algebra/graded transports below retain the original ideal.
-/

universe u v w
open CategoryTheory AlgebraicGeometry
open Hironaka.Geometry.ProjectiveIdeal
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual original polynomial variable rename retains EVERY original natural degree. -/
def polynomialRenameGraded {K : Type u} {σ : Type v} {τ : Type w} [CommRing K] (e : σ ≃ τ) :
    MvPolynomial.homogeneousSubmodule σ K →+*ᵍ MvPolynomial.homogeneousSubmodule τ K where
  __ := MvPolynomial.rename e
  map_mem := fun h => h.rename_isHomogeneous

/-- The WHOLE original homogeneous ideal has its actual quotient coefficient-algebra rename equivalence. -/
def polynomialRenameQuotientEquiv {K : Type u} {σ : Type v} {τ : Type w} [CommRing K]
    (e : σ ≃ τ) (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) :
    (MvPolynomial σ K ⧸ J.toIdeal) ≃ₐ[K]
      (MvPolynomial τ K ⧸ (J.map (polynomialRenameGraded e)).toIdeal) :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv K e) rfl

/-- The actual forward quotient rename preserves EVERY original homogeneous degree. -/
def polynomialRenameQuotientGraded {K : Type u} {σ : Type v} {τ : Type w} [CommRing K]
    (e : σ ≃ τ) (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) :
    GradedQuotient.grading (MvPolynomial.homogeneousSubmodule σ K) J.toIdeal →+*ᵍ
      GradedQuotient.grading (MvPolynomial.homogeneousSubmodule τ K)
        (J.map (polynomialRenameGraded e)).toIdeal where
  __ := (polynomialRenameQuotientEquiv e J).toRingHom
  map_mem := by
    intro d q hq
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hq
    exact Submodule.mem_map.mpr ⟨MvPolynomial.rename e a, ha.rename_isHomogeneous, rfl⟩

/-- The actual inverse quotient rename preserves EVERY original homogeneous degree. -/
def polynomialRenameQuotientInverseGraded {K : Type u} {σ : Type v} {τ : Type w} [CommRing K]
    (e : σ ≃ τ) (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) :
    GradedQuotient.grading (MvPolynomial.homogeneousSubmodule τ K)
        (J.map (polynomialRenameGraded e)).toIdeal →+*ᵍ
      GradedQuotient.grading (MvPolynomial.homogeneousSubmodule σ K) J.toIdeal where
  __ := (polynomialRenameQuotientEquiv e J).symm.toRingHom
  map_mem := by
    intro d q hq
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hq
    refine Submodule.mem_map.mpr ⟨MvPolynomial.rename e.symm a, ha.rename_isHomogeneous, ?_⟩
    apply (polynomialRenameQuotientEquiv e J).injective
    change (polynomialRenameQuotientEquiv e J)
      (Ideal.Quotient.mk _ (MvPolynomial.rename e.symm a)) =
      (polynomialRenameQuotientEquiv e J)
        ((polynomialRenameQuotientEquiv e J).symm (Ideal.Quotient.mk _ a))
    rw [AlgEquiv.apply_symm_apply]
    change Ideal.Quotient.mk _ (MvPolynomial.rename e (MvPolynomial.rename e.symm a)) = Ideal.Quotient.mk _ a
    simp only [MvPolynomial.rename_rename, Equiv.self_comp_symm, MvPolynomial.rename_id]
    rfl

/-- Actual coordinate universe transport gives a genuine isomorphism of the SAME original quotient schemes. -/
def polynomialQuotientReindexIso {K : Type u} {σ : Type} {τ : Type u} [CommRing K]
    (e : σ ≃ τ) (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) :
    Proj (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule σ K) J.toIdeal) ≅
      Proj (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule τ K)
        (J.map (polynomialRenameGraded e)).toIdeal) where
  hom := Proj.map (polynomialRenameQuotientInverseGraded e J)
    (ProjClosedImmersion.irrelevant_le_map_of_surjective _ (polynomialRenameQuotientEquiv e J).symm.surjective)
  inv := Proj.map (polynomialRenameQuotientGraded e J)
    (ProjClosedImmersion.irrelevant_le_map_of_surjective _ (polynomialRenameQuotientEquiv e J).surjective)
  hom_inv_id := by
    rw [← Proj.map_comp]
    have h : (polynomialRenameQuotientInverseGraded e J).comp (polynomialRenameQuotientGraded e J) =
        GradedRingHom.id (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule σ K) J.toIdeal) := by
      ext q
      exact (polynomialRenameQuotientEquiv e J).symm_apply_apply q
    simpa only [h] using (Proj.map_id
      (𝒜 := GradedQuotient.grading (MvPolynomial.homogeneousSubmodule σ K) J.toIdeal))
  inv_hom_id := by
    rw [← Proj.map_comp]
    have h : (polynomialRenameQuotientGraded e J).comp (polynomialRenameQuotientInverseGraded e J) =
        GradedRingHom.id (GradedQuotient.grading (MvPolynomial.homogeneousSubmodule τ K)
          (J.map (polynomialRenameGraded e)).toIdeal) := by
      ext q
      exact (polynomialRenameQuotientEquiv e J).apply_symm_apply q
    simpa only [h] using (Proj.map_id
      (𝒜 := GradedQuotient.grading (MvPolynomial.homogeneousSubmodule τ K)
        (J.map (polynomialRenameGraded e)).toIdeal))

end
end Hironaka.Geometry.ProperSteinProjectiveCech
