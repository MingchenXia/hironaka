import Hironaka.Geometry.ProjectiveSpaceBaseChange
import Hironaka.Geometry.ProjectiveIdentity
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Limits

/-!
# Actual relative projective spaces over arbitrary schemes

Native projective space is base changed from the actual terminal integer
spectrum. Actual affine-base projective spaces map openly into it by the
native coefficient base-change theorem. No relative scheme or Cartesian
certificate is supplied by a caller.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Hironaka.Geometry.BlowupProjectiveEmbedding

noncomputable section

namespace Hironaka.Geometry.RelativeChow

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Integer coefficients in the same universe as the original schemes. -/
abbrev IntegerRing := ULift.{u} ℤ

/-- The actual unique structure morphism to the native integer spectrum. -/
def integerStructure (S : Scheme.{u}) : S ⟶ Spec (CommRingCat.of IntegerRing) :=
  specULiftZIsTerminal.from S

@[reassoc (attr := simp)]
theorem integerStructure_naturality {S T : Scheme.{u}} (f : S ⟶ T) :
    f ≫ integerStructure T = integerStructure S :=
  specULiftZIsTerminal.hom_ext _ _

/-- The actual native relative projective space, defined by native base change. -/
def relativeSpace (S : Scheme.{u}) (n : ℕ) : Scheme.{u} :=
  pullback (integerStructure S) (projectiveSpaceStructure IntegerRing n)

/-- The actual first projection to the original scheme base. -/
def relativeStructure (S : Scheme.{u}) (n : ℕ) : relativeSpace S n ⟶ S :=
  pullback.fst _ _

/-- The actual second projection to native integer-coefficient projective space. -/
def integerProjection (S : Scheme.{u}) (n : ℕ) :
    relativeSpace S n ⟶ projectiveSpace IntegerRing n := pullback.snd _ _

instance relativeStructure_isProper (S : Scheme.{u}) (n : ℕ) :
    IsProper (relativeStructure S n) := by
  unfold relativeStructure
  infer_instance

instance relativeZeroStructure_isIso (S : Scheme.{u}) :
    IsIso (relativeStructure S 0) := by
  unfold relativeStructure
  infer_instance

instance relativeSpace_isNoetherian (S : Scheme.{u}) [AlgebraicGeometry.IsNoetherian S]
    (n : ℕ) : AlgebraicGeometry.IsNoetherian (relativeSpace S n) := by
  let : IsLocallyNoetherian (relativeSpace S n) :=
    LocallyOfFiniteType.isLocallyNoetherian (relativeStructure S n)
  let : CompactSpace (relativeSpace S n) :=
    QuasiCompact.compactSpace_of_compactSpace (relativeStructure S n)
  exact ⟨⟩

variable {S : Scheme.{u}} {A : Type u} [CommRing A]

/-- The actual canonical map of native projective space over an affine
base patch into projective space over the original scheme. -/
def affineProjectiveMap (a : Spec (CommRingCat.of A) ⟶ S) (n : ℕ) :
    projectiveSpace A n ⟶ relativeSpace S n :=
  pullback.lift (projectiveSpaceStructure A n ≫ a)
    (projectiveCoefficientMap (CommRingCat.isInitial.to (CommRingCat.of A)).hom n)
    (specULiftZIsTerminal.hom_ext _ _)

@[reassoc (attr := simp)]
theorem affineProjectiveMap_structure
    (a : Spec (CommRingCat.of A) ⟶ S) (n : ℕ) :
    affineProjectiveMap a n ≫ relativeStructure S n = projectiveSpaceStructure A n ≫ a := by
  simp [affineProjectiveMap, relativeStructure]

@[reassoc (attr := simp)]
theorem affineProjectiveMap_integerProjection
    (a : Spec (CommRingCat.of A) ⟶ S) (n : ℕ) :
    affineProjectiveMap a n ≫ integerProjection S n =
      projectiveCoefficientMap (CommRingCat.isInitial.to (CommRingCat.of A)).hom n := by
  simp [affineProjectiveMap, integerProjection]

/-- The actual coefficient map has its actual Cartesian square over the
original scheme base, derived by pullback cancellation. -/
theorem affineProjectiveMap_isPullback
    (a : Spec (CommRingCat.of A) ⟶ S) (n : ℕ) :
    IsPullback (affineProjectiveMap a n) (projectiveSpaceStructure A n)
      (relativeStructure S n) a := by
  have H : IsPullback
      (projectiveCoefficientMap (CommRingCat.isInitial.to (CommRingCat.of A)).hom n)
      (projectiveSpaceStructure A n) (projectiveSpaceStructure IntegerRing n)
      (a ≫ integerStructure S) := by
    convert ProjectiveSpaceBaseChange.isPullback_projectiveCoefficientMap
      (CommRingCat.isInitial.to (CommRingCat.of A)).hom n using 1
    exact specULiftZIsTerminal.hom_ext _ _
  have H' : IsPullback (affineProjectiveMap a n ≫ integerProjection S n)
      (projectiveSpaceStructure A n) (projectiveSpaceStructure IntegerRing n)
      (a ≫ integerStructure S) := by
    simpa only [affineProjectiveMap_integerProjection] using H
  exact H'.of_right (affineProjectiveMap_structure a n)
    (IsPullback.of_hasPullback (integerStructure S) (projectiveSpaceStructure IntegerRing n)).flip

instance affineProjectiveMap_isOpenImmersion
    (a : Spec (CommRingCat.of A) ⟶ S) [IsOpenImmersion a] (n : ℕ) :
    IsOpenImmersion (affineProjectiveMap a n) :=
  MorphismProperty.of_isPullback (affineProjectiveMap_isPullback a n).flip inferInstance

end Hironaka.Geometry.RelativeChow
