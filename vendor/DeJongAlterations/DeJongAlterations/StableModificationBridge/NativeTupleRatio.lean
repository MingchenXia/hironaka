import DeJongAlterations.Geometry.FiniteProjectiveAffineClosed

/-!
# The whole native chart homomorphism of an affine tuple

The unit-marker chart is identified using the literal unit-ideal Rees coefficient map. The
factorization retains the entire original scheme map, including nilpotents and coefficients.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace DeJongAlterations.StableModificationBridge.NativeTupleRatio

open Geometry.FiniteProjective Geometry.ProjectiveIdeal Geometry.BlowupProjectiveEmbedding
  Geometry.UnitIdealBlowup

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R A : Type u} [CommRing R] [CommRing A] {N : ℕ}

/-- The original coefficient ring is the whole degree-zero unit-marker Rees chart ring. -/
def markerEquiv (r : R →+* A) (a : Fin (N + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (N + 1)) (hi : a i = 1) :
    A ≃+* HomogeneousLocalization.Away (reesGrading (⊤ : Ideal A))
      (tupleGradedMap r a ha (X i)) :=
  RingEquiv.ofBijective (unitChartCoefficients (tupleGradedMap r a ha (X i))) (by
    have hb : tupleGradedMap r a ha (X i) = reesDegreeOne (⊤ : Ideal A) 1 (by trivial) := by
      rw [tupleGradedMap_X, hi]
    rw [hb]
    exact unitChartCoefficients_bijective)

/-- The whole original tuple homomorphism on the unit-marker coordinate chart. -/
def markerHom (r : R →+* A) (a : Fin (N + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (N + 1)) (hi : a i = 1) :
    HomogeneousLocalization.Away (projectiveSpaceGrading R N) (X i) →+* A :=
  (markerEquiv r a ha i hi).symm.toRingHom.comp
    (HomogeneousLocalization.Away.map (tupleGradedMap r a ha) (X i))

/-- Every original coordinate ratio maps to its original tuple entry on the marker chart. -/
theorem markerHom_ratio (r : R →+* A) (a : Fin (N + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (N + 1)) (hi : a i = 1)
    (j : Fin (N + 1)) :
    markerHom r a ha i hi
      (HomogeneousLocalization.Away.mk (projectiveSpaceGrading R N)
        (MvPolynomial.isHomogeneous_X R i) 1 (X j)
        (by simpa only [one_smul, projectiveSpaceGrading,
          MvPolynomial.mem_homogeneousSubmodule] using MvPolynomial.isHomogeneous_X R j)) =
      a j := by
  change (markerEquiv r a ha i hi).symm
    (HomogeneousLocalization.Away.map (tupleGradedMap r a ha) (X i) _) = _
  rw [tupleAwayMap_ratio r a ha i hi j]
  exact (markerEquiv r a ha i hi).symm_apply_apply (a j)

/-- Equality of the entire native tuple morphism with its actual unit-marker chart factor. -/
theorem affineTupleMap_factor_marker (r : R →+* A) (a : Fin (N + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (N + 1)) (hi : a i = 1) :
    affineTupleMap r a ha =
      Spec.map (CommRingCat.ofHom (markerHom r a ha i hi)) ≫
        Proj.awayι (projectiveSpaceGrading R N) (X i)
          (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one := by
  let f := tupleGradedMap r a ha
  let b := f (X i)
  let j := Proj.awayι (reesGrading (⊤ : Ideal A)) b
    (f.map_mem (MvPolynomial.isHomogeneous_X R i)) Nat.zero_lt_one
  let c := unitChartCoefficients b
  have hc : j ≫ (unitIdealBlowupIso A).hom = Spec.map (CommRingCat.ofHom c) := by
    dsimp only [j, unitIdealBlowupIso_hom, affineBlowupStructure]
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl
  have hcomm : Spec.map (CommRingCat.ofHom c) ≫ affineTupleMap r a ha =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f (X i))) ≫
        Proj.awayι (projectiveSpaceGrading R N) (X i)
          (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one := by
    rw [← hc, affineTupleMap, affineProjectiveMap_eq_tupleGradedMap]
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact Proj.awayι_comp_map f (tupleGradedMap_irrelevant r a ha)
      Nat.zero_lt_one (X i) (MvPolynomial.isHomogeneous_X R i)
  have hcomp : c.comp (markerHom r a ha i hi) =
      HomogeneousLocalization.Away.map f (X i) := by
    apply RingHom.ext
    intro x
    change (markerEquiv r a ha i hi)
      ((markerEquiv r a ha i hi).symm (HomogeneousLocalization.Away.map f (X i) x)) = _
    exact (markerEquiv r a ha i hi).apply_symm_apply _
  have : IsIso (Spec.map (CommRingCat.ofHom c)) := by
    apply (isIso_SpecMap_iff).mpr
    exact (markerEquiv r a ha i hi).bijective
  apply (cancel_epi (Spec.map (CommRingCat.ofHom c))).mp
  rw [hcomm, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact congrArg CommRingCat.ofHom hcomp.symm

end DeJongAlterations.StableModificationBridge.NativeTupleRatio
