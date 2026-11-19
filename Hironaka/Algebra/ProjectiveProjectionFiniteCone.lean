import Hironaka.Algebra.ProjectiveProjectionFiniteCentre

/-!
# Finiteness of the original homogeneous coordinate quotient over partial coordinates

The monic relation is internally obtained from avoidance of the actual
standard projective centre. The original quotient and coefficient map
are retained, including nilpotents and the empty subscheme.
-/

noncomputable section

open MvPolynomial AlgebraicGeometry

namespace Hironaka.Algebra.ProjectiveProjectionFinite

open Geometry.ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (J : HomogeneousIdeal (ProjectiveGrading k (n + 1)))

/-- The original homogeneous coordinate quotient ring. -/
abbrev CoordinateQuotient := MvPolynomial (Fin (n + 2)) k ⧸ J.toIdeal

/-- The literal original partial-coordinate coefficient homomorphism. -/
def partialCoordinateMap : MvPolynomial (Fin (n + 1)) k →ₐ[k] CoordinateQuotient k n J :=
  (Ideal.Quotient.mkₐ k J.toIdeal).comp (MvPolynomial.rename Fin.succ)

@[simp]
theorem partialCoordinateMap_X (i : Fin (n + 1)) :
    partialCoordinateMap k n J (X i) = Ideal.Quotient.mk J.toIdeal (X i.succ) := by
  simp [partialCoordinateMap]

/-- The coefficient structure is the original partial-coordinate map. -/
@[instance_reducible]
def partialCoordinateAlgebra : Algebra (MvPolynomial (Fin (n + 1)) k) (CoordinateQuotient k n J) :=
  (partialCoordinateMap k n J).toRingHom.toAlgebra

/-- The original quotient has a single remaining algebra generator, the original class of X0. -/
theorem adjoin_discardedCoordinate_eq_top :
    letI := partialCoordinateAlgebra k n J
    Algebra.adjoin (MvPolynomial (Fin (n + 1)) k)
      {Ideal.Quotient.mk J.toIdeal (X 0)} = (⊤ : Subalgebra _ (CoordinateQuotient k n J)) := by
  let := partialCoordinateAlgebra k n J
  let S := Algebra.adjoin (MvPolynomial (Fin (n + 1)) k) {Ideal.Quotient.mk J.toIdeal (X 0)}
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hX (i : Fin (n + 2)) : Ideal.Quotient.mk J.toIdeal (X i) ∈ S := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Algebra.subset_adjoin (Set.mem_singleton _)
    · have h := S.algebraMap_mem (X j)
      change partialCoordinateMap k n J (X j) ∈ S at h
      simpa only [partialCoordinateMap_X] using h
  induction F using MvPolynomial.induction_on with
  | C a =>
    have h := S.algebraMap_mem (MvPolynomial.C a)
    change partialCoordinateMap k n J (MvPolynomial.C a) ∈ S at h
    rw [partialCoordinateMap, AlgHom.comp_apply, MvPolynomial.rename_C] at h
    exact h
  | add F G hF hG => simpa only [map_add] using S.add_mem hF hG
  | mul_X F i hF => simpa only [map_mul] using S.mul_mem hF (hX i)

/-- The polynomial in the discarded variable evaluates to its exact original quotient class. -/
theorem univariate_aeval_eq (F : MvPolynomial (Fin (n + 2)) k) :
    letI := partialCoordinateAlgebra k n J
    Polynomial.aeval (Ideal.Quotient.mk J.toIdeal (X 0)) (MvPolynomial.finSuccEquiv k (n + 1) F) =
      Ideal.Quotient.mk J.toIdeal F := by
  let := partialCoordinateAlgebra k n J
  have h : (Polynomial.eval₂RingHom (algebraMap (MvPolynomial (Fin (n + 1)) k)
      (CoordinateQuotient k n J)) (Ideal.Quotient.mk J.toIdeal (X 0))).comp
      (MvPolynomial.finSuccEquiv k (n + 1)).toRingHom = Ideal.Quotient.mk J.toIdeal := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change Polynomial.eval₂ _ _ (MvPolynomial.finSuccEquiv k (n + 1) (C a)) = _
      rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.eval₂_C]
      change partialCoordinateMap k n J (C a) = _
      rw [partialCoordinateMap, AlgHom.comp_apply, MvPolynomial.rename_C]
      rfl
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change Polynomial.eval₂ _ _ (MvPolynomial.finSuccEquiv k (n + 1) (X 0)) = _
        rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.eval₂_X]
      · change Polynomial.eval₂ _ _ (MvPolynomial.finSuccEquiv k (n + 1) (X j.succ)) = _
        rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.eval₂_C]
        exact partialCoordinateMap_X k n J j
  exact DFunLike.congr_fun h F

/-- Avoidance of the actual standard centre makes the original discarded coordinate integral. -/
theorem discardedCoordinate_isIntegral
    (hout : centrePoint k n ∉ ProjectiveSpectrum.zeroLocus _ (J.toIdeal : Set _)) :
    letI := partialCoordinateAlgebra k n J
    IsIntegral (MvPolynomial (Fin (n + 1)) k) (Ideal.Quotient.mk J.toIdeal (X 0)) := by
  let := partialCoordinateAlgebra k n J
  obtain ⟨d, F, hFJ, hFhom, hFmon⟩ := exists_monic_homogeneous_form k n J hout
  refine ⟨MvPolynomial.finSuccEquiv k (n + 1) F, hFmon, ?_⟩
  change Polynomial.aeval _ _ = 0
  rw [univariate_aeval_eq]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hFJ

/-- The original quotient is genuinely finite over its actual partial-coordinate ring,
with no supplied relation, integrality, or module-finiteness certificate. -/
theorem partialCoordinateMap_finite
    (hout : centrePoint k n ∉ ProjectiveSpectrum.zeroLocus _ (J.toIdeal : Set _)) :
    (partialCoordinateMap k n J).toRingHom.Finite := by
  let := partialCoordinateAlgebra k n J
  let S := Algebra.adjoin (MvPolynomial (Fin (n + 1)) k) {Ideal.Quotient.mk J.toIdeal (X 0)}
  let : Module.Finite (MvPolynomial (Fin (n + 1)) k) S :=
    Algebra.finite_adjoin_simple_of_isIntegral (discardedCoordinate_isIntegral k n J hout)
  exact Module.Finite.of_surjective S.val.toLinearMap (by
    intro z
    refine ⟨⟨z, ?_⟩, rfl⟩
    change z ∈ Algebra.adjoin (MvPolynomial (Fin (n + 1)) k) _
    rw [adjoin_discardedCoordinate_eq_top]
    trivial)

end Hironaka.Algebra.ProjectiveProjectionFinite
