import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projectivity over a coefficient ring

Projective space is the native scheme `Proj` of the polynomial ring with its standard grading.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DeJongAlterations

universe u

/-- The standard grading of the homogeneous coordinate ring of projective space. -/
abbrev projectiveSpaceGrading (k : Type u) [CommRing k] (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

/-- Native projective $n$-space over the coefficient ring. -/
def projectiveSpace (k : Type u) [CommRing k] (n : ℕ) : Scheme.{u} :=
  AlgebraicGeometry.Proj (projectiveSpaceGrading k n)

/-- Constants as the degree-zero homogeneous coordinate ring. -/
def projectiveSpaceConstants (k : Type u) [CommRing k] (n : ℕ) :
    k →+* projectiveSpaceGrading k n 0 where
  toFun a := ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C (Fin (n + 1)) a⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- Every homogeneous polynomial of degree zero is a unique constant. -/
theorem projectiveSpaceConstants_bijective (k : Type u) [CommRing k] (n : ℕ) :
    Function.Bijective (projectiveSpaceConstants k n) := by
  constructor
  · intro a b hab
    exact MvPolynomial.C_injective (Fin (n + 1)) k (congrArg Subtype.val hab)
  · intro p
    refine ⟨p.val.coeff 0, Subtype.ext ?_⟩
    exact (MvPolynomial.homogeneousComponent_zero _).symm.trans
      (MvPolynomial.homogeneousComponent_eq_self p.2)

/-- The coefficient ring is the actual degree-zero coordinate ring. -/
def projectiveSpaceDegreeZeroEquiv (k : Type u) [CommRing k] (n : ℕ) :
    k ≃+* projectiveSpaceGrading k n 0 :=
  RingEquiv.ofBijective (projectiveSpaceConstants k n)
    (projectiveSpaceConstants_bijective k n)

/-- The native structure map, with the degree-zero ring identified with the coefficient ring. -/
def projectiveSpaceStructure (k : Type u) [CommRing k] (n : ℕ) :
    projectiveSpace k n ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (projectiveSpaceGrading k n) ≫
    Spec.map (projectiveSpaceDegreeZeroEquiv k n).toCommRingCatIso.hom

/-- The homogeneous coordinate ring is finite type over its degree-zero part. -/
theorem projectiveSpaceGrading_finiteType (k : Type u) [CommRing k] (n : ℕ) :
    Algebra.FiniteType (projectiveSpaceGrading k n 0) (MvPolynomial (Fin (n + 1)) k) := by
  apply RingHom.finiteType_algebraMap.mp
  apply RingHom.FiniteType.of_comp_finiteType (f := projectiveSpaceConstants k n)
  change (algebraMap k (MvPolynomial (Fin (n + 1)) k)).FiniteType
  exact RingHom.finiteType_algebraMap.mpr inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Projective space is proper over its coefficient ring. -/
instance projectiveSpaceStructure_isProper (k : Type u) [CommRing k] (n : ℕ) :
    IsProper (projectiveSpaceStructure k n) := by
  let := projectiveSpaceGrading_finiteType k n
  unfold projectiveSpaceStructure
  infer_instance

/-- A morphism is projective when it factors through a closed immersion into projective space. -/
def IsProjectiveOver {k : Type u} [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ projectiveSpace k n),
    IsClosedImmersion i ∧ i ≫ projectiveSpaceStructure k n = p

/-- A projective morphism to an affine coefficient scheme is proper. -/
theorem IsProjectiveOver.isProper {k : Type u} [CommRing k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} (hp : IsProjectiveOver p) : IsProper p := by
  obtain ⟨n, i, hi, hcomp⟩ := hp
  let := hi
  rw [← hcomp]
  infer_instance

/-- Projective space itself has its tautological projective presentation. -/
theorem isProjectiveOver_projectiveSpaceStructure (k : Type u) [CommRing k] (n : ℕ) :
    IsProjectiveOver (projectiveSpaceStructure k n) :=
  ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩

end DeJongAlterations
