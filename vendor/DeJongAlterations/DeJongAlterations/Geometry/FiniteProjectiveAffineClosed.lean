import DeJongAlterations.Geometry.FiniteProjectiveAffineCharts
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Closed coordinate restrictions of the native affine tuple map

The whole homogeneous localization of the unit-ideal Rees algebra at T is
canonically the coefficient ring. Actual tuple ratios provide preimages of
the original algebra generators, proving surjectivity of the genuine Proj
chart map and hence a closed immersion on a unit-marker coordinate open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace DeJongAlterations.Geometry.FiniteProjective

open ProjectiveIdeal BlowupProjectiveEmbedding UnitIdealBlowup

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R A : Type u} [CommRing R] [CommRing A] {m : ℕ}

/-- The actual coefficient map into a homogeneous localization of the unit Rees algebra. -/
def unitChartCoefficients (b : reesAlgebra (⊤ : Ideal A)) :
    A →+* HomogeneousLocalization.Away (reesGrading (⊤ : Ideal A)) b :=
  (HomogeneousLocalization.fromZeroRingHom (reesGrading (⊤ : Ideal A)) (.powers b)).comp
    (reesConstants ⊤)

/-- The literal coefficient map into the T-chart is bijective over every commutative ring. -/
theorem unitChartCoefficients_bijective :
    Function.Bijective (unitChartCoefficients (reesDegreeOne (⊤ : Ideal A) 1 (by trivial))) := by
  let t := reesDegreeOne (⊤ : Ideal A) 1 (by trivial)
  let ht := reesDegreeOne_mem (⊤ : Ideal A) 1 (by trivial)
  let i := Proj.awayι (reesGrading (⊤ : Ideal A)) t ht Nat.zero_lt_one
  have hi : i.opensRange = ⊤ := by
    rw [Proj.opensRange_awayι]
    exact unitIdeal_oneChart_eq_top
  let : IsIso i := isIso_of_isOpenImmersion_of_opensRange_eq_top i hi
  have hc : i ≫ affineBlowupStructure (⊤ : Ideal A) =
      Spec.map (CommRingCat.ofHom (unitChartCoefficients t)) := by
    dsimp only [i, affineBlowupStructure]
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl
  have : IsIso (Spec.map (CommRingCat.ofHom (unitChartCoefficients t))) := by
    rw [← hc]
    infer_instance
  exact isIso_SpecMap_iff.mp this

/-- The actual graded tuple map with the original coefficient homomorphism. -/
def tupleGradedMap (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) :
    projectiveSpaceGrading R m →+*ᵍ reesGrading (⊤ : Ideal A) :=
  (generatorPolynomialMap ⊤ a ha).toGradedRingHom.comp (polynomialCoefficientMap r m)

/-- Native irrelevant containment is constructed by the actual constituent maps. -/
theorem tupleGradedMap_irrelevant (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) :
    HomogeneousIdeal.irrelevant (reesGrading (⊤ : Ideal A)) ≤
      (HomogeneousIdeal.irrelevant (projectiveSpaceGrading R m)).map (tupleGradedMap r a ha) :=
  HomogeneousIdeal.irrelevant_le_map_comp (polynomialCoefficientMap_irrelevant r m)
    (ProjClosedImmersion.irrelevant_le_map_of_surjective _ (generatorPolynomialMap_surjective ⊤ a ha))

/-- This is the literal native projective map already used in the affine tuple construction. -/
theorem affineProjectiveMap_eq_tupleGradedMap (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) :
    affineProjectiveMap r ⊤ a ha = Proj.map (tupleGradedMap r a ha) (tupleGradedMap_irrelevant r a ha) :=
  (Proj.map_comp _ _ _ _).symm

/-- The graded tuple map sends each original coordinate to its actual Rees degree-one value. -/
theorem tupleGradedMap_X (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (j : Fin (m + 1)) :
    tupleGradedMap r a ha (X j) = reesDegreeOne ⊤ (a j) (by trivial) := by
  change DeJongAlterations.Algebra.ReesPresentation.reesPolynomialEval ⊤ a _ (MvPolynomial.map r (X j)) = _
  simp only [MvPolynomial.map_X, DeJongAlterations.Algebra.ReesPresentation.reesPolynomialEval,
    MvPolynomial.aeval_X]

/-- The graded tuple map sends constants to the original coefficients. -/
theorem tupleGradedMap_C (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (c : R) :
    tupleGradedMap r a ha (C c) = algebraMap A (reesAlgebra (⊤ : Ideal A)) (r c) := by
  change DeJongAlterations.Algebra.ReesPresentation.reesPolynomialEval ⊤ a _ (MvPolynomial.map r (C c)) = _
  simp only [MvPolynomial.map_C, DeJongAlterations.Algebra.ReesPresentation.reesPolynomialEval,
    MvPolynomial.aeval_C]

/-- The original coefficient constants have literal preimages in the native chart map. -/
theorem tupleAwayMap_coefficient (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (c : R) :
    HomogeneousLocalization.Away.map (tupleGradedMap r a ha) (X i)
      (homogeneousChartCoefficients i c) =
        unitChartCoefficients (tupleGradedMap r a ha (X i)) (r c) := by
  have H := RingHom.congr_fun
    (ProjStructureMap.awayMap_comp_fromZero (tupleGradedMap r a ha) (X i))
    (homogeneousCoefficientZero R m c)
  have hc : (tupleGradedMap r a ha).gradedZeroRingHom (homogeneousCoefficientZero R m c) =
      reesConstants (⊤ : Ideal A) (r c) :=
    Subtype.ext (tupleGradedMap_C r a ha c)
  exact H.trans (congrArg
    (HomogeneousLocalization.fromZeroRingHom (reesGrading (⊤ : Ideal A))
      (.powers (tupleGradedMap r a ha (X i)))) hc)

/-- When a marker is one, every actual tuple value is the image of its genuine homogeneous ratio. -/
theorem tupleAwayMap_ratio (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1)
    (j : Fin (m + 1)) :
    HomogeneousLocalization.Away.map (tupleGradedMap r a ha) (X i)
      (HomogeneousLocalization.Away.mk (projectiveSpaceGrading R m)
        (MvPolynomial.isHomogeneous_X R i) 1 (X j)
          (by simpa only [one_smul, projectiveSpaceGrading,
            MvPolynomial.mem_homogeneousSubmodule] using MvPolynomial.isHomogeneous_X R j)) =
      unitChartCoefficients (tupleGradedMap r a ha (X i)) (a j) := by
  rw [HomogeneousLocalization.Away.map_mk]
  apply HomogeneousLocalization.val_injective
  change Localization.mk (tupleGradedMap r a ha (X j))
      (⟨tupleGradedMap r a ha (X i) ^ 1, 1, rfl⟩ :
        Submonoid.powers (tupleGradedMap r a ha (X i))) =
    Localization.mk (algebraMap A (reesAlgebra (⊤ : Ideal A)) (a j)) 1
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, pow_one]
  rw [tupleGradedMap_X, tupleGradedMap_X]
  apply Subtype.ext
  change Polynomial.monomial 1 (a j) = Polynomial.monomial 1 (a i) * Polynomial.C (a j)
  rw [hi]
  simp

/-- Whole-algebra generation proves surjectivity of the genuine homogeneous localization map. -/
theorem tupleAwayMap_surjective (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1)
    (hgen : letI := r.toAlgebra; Algebra.adjoin R (Set.range a) = ⊤) :
    Function.Surjective (HomogeneousLocalization.Away.map (tupleGradedMap r a ha) (X i)) := by
  let : Algebra R A := r.toAlgebra
  let b := tupleGradedMap r a ha (X i)
  let f := HomogeneousLocalization.Away.map (tupleGradedMap r a ha) (X i)
  have hb : b = reesDegreeOne (⊤ : Ideal A) 1 (by trivial) := by
    dsimp only [b]
    rw [tupleGradedMap_X]
    apply Subtype.ext
    exact congrArg (Polynomial.monomial 1) hi
  have hbij : Function.Bijective (unitChartCoefficients b) := by
    rw [hb]
    exact unitChartCoefficients_bijective
  have hpre (x : A) (hx : x ∈ Algebra.adjoin R (Set.range a)) :
      ∃ z, f z = unitChartCoefficients b x := by
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact ⟨_, tupleAwayMap_ratio r a ha i hi j⟩
    | algebraMap c =>
      exact ⟨homogeneousChartCoefficients i c, tupleAwayMap_coefficient r a ha i c⟩
    | add x y hx hy hpx hpy =>
      obtain ⟨z, hz⟩ := hpx
      obtain ⟨w, hw⟩ := hpy
      exact ⟨z + w, by rw [map_add, hz, hw, map_add]⟩
    | mul x y hx hy hpx hpy =>
      obtain ⟨z, hz⟩ := hpx
      obtain ⟨w, hw⟩ := hpy
      exact ⟨z * w, by rw [map_mul, hz, hw, map_mul]⟩
  intro z
  obtain ⟨x, rfl⟩ := hbij.2 z
  exact hpre x (by rw [hgen]; trivial)

/-- A unit-marker tuple generating the whole coefficient algebra gives an actual native immersion. -/
theorem affineTupleMap_isImmersion (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1)
    (hgen : letI := r.toAlgebra; Algebra.adjoin R (Set.range a) = ⊤) :
    IsImmersion (affineTupleMap r a ha) := by
  let f := tupleGradedMap r a ha
  let hf := tupleGradedMap_irrelevant r a ha
  let b := f (X i)
  let hbdeg := f.map_mem (MvPolynomial.isHomogeneous_X R i)
  let j := Proj.awayι (reesGrading (⊤ : Ideal A)) b hbdeg Nat.zero_lt_one
  have hb : b = reesDegreeOne (⊤ : Ideal A) 1 (by trivial) := by
    dsimp only [b, f]
    rw [tupleGradedMap_X]
    apply Subtype.ext
    exact congrArg (Polynomial.monomial 1) hi
  have hj : j.opensRange = ⊤ := by
    rw [Proj.opensRange_awayι, hb]
    exact unitIdeal_oneChart_eq_top
  let : IsIso j := isIso_of_isOpenImmersion_of_opensRange_eq_top j hj
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (HomogeneousLocalization.Away.map f (X i)))) :=
    IsClosedImmersion.spec_of_surjective _ (tupleAwayMap_surjective r a ha i hi hgen)
  have hjf : IsImmersion (j ≫ Proj.map f hf) := by
    rw [show j ≫ Proj.map f hf = _ from
      Proj.awayι_comp_map f hf Nat.zero_lt_one (X i) (MvPolynomial.isHomogeneous_X R i)]
    infer_instance
  let : IsImmersion (Proj.map f hf) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @IsImmersion) j _).mp hjf
  rw [affineTupleMap, affineProjectiveMap_eq_tupleGradedMap]
  infer_instance

end DeJongAlterations.Geometry.FiniteProjective
