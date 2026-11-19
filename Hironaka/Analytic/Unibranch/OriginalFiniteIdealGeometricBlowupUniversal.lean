import Hironaka.Analytic.Unibranch.OriginalFiniteIdealGeometricBlowup
import Hironaka.Analytic.Unibranch.EmbeddedGeometricIdealGlobalCartier
import Hironaka.Analytic.Unibranch.EmbeddedGeometricIdealGlobalUniversal

/-!
# The ordinary arbitrary finite-ideal geometric blowup endpoint

The SAME generated original Y/p has its own whole ideal rank-one data
DERIVED and the full original universal property for every original A/F.
Private selected model geometry is transparently specialized, never input
or exported as a desired certificate. Zero-component ideals are included;
no density, surjectivity or proper-bimeromorphic claim is assumed.
Blueprint FIRST: `original-finite-ideal-geometric-blowup-universal.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGeometricBlowupUniversal

open Hironaka HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealSheaf SourceReducedComplexSpace OriginalFiniteIdealGeometricBlowup

noncomputable section

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType]

/-- OWN standard native rank-one data for the SAME entire pulled ideal;
no own-projection generator or ideal isomorphism certificate is supplied. -/
theorem projection_ideal_exists_locallyFreeData :
    ∃ q : (nativePulledIdealModule (projectionMorphism B b).hom.left B b).LocalGeneratorsData.{0},
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (Unique (q.generators i).I) := by
  unfold OriginalFiniteIdealGeometricBlowup.projectionMorphism
  exact EmbeddedGeometricIdealGlobalCartier.projection_ideal_exists_locallyFreeData _ _ _ B b _

/-- Native invertibility of the ENTIRE same projection ideal at every
actual original source stalk, without radicalization or domain replacement. -/
theorem projection_ideal_moduleInvertible (y : (sourceObject B b).obj.left) :
    Module.Invertible ((sourceObject B b).obj.left.presheaf.stalk y).carrier
      (nativePulledIdealStalkIdeal (projectionMorphism B b).hom.left B b y) := by
  unfold OriginalFiniteIdealGeometricBlowup.projectionMorphism
  exact EmbeddedGeometricIdealGlobalCartier.projection_ideal_moduleInvertible _ _ _ B b _ y

/-- EVERY ORIGINAL source with standard rank-one data on the SAME whole
F-pulled ideal has a UNIQUE FULL ORIGINAL lift over the actual projection. -/
theorem exists_unique_lift_of_locallyFreeData (A : SourceReducedComplexSpace) (F : A ⟶ X)
    (q : (nativePulledIdealModule F.hom.left B b).LocalGeneratorsData)
    [q.IsLocallyFreeData] [∀ i, Unique (q.generators i).I] :
    ∃! L : A ⟶ sourceObject B b, L ≫ projectionMorphism B b = F := by
  unfold OriginalFiniteIdealGeometricBlowup.sourceObject OriginalFiniteIdealGeometricBlowup.projectionMorphism
  exact EmbeddedGeometricIdealGlobalUniversal.exists_unique_lift_of_locallyFreeData
    _ _ _ B b _ _ A F q

/-- ONLY ordinary original finite-type data internally produce the actual
geometric blowup object, own Cartier data and full UP, with NO density premise.
The chosen witness is exactly the preceding ordinary sourceObject/projection. -/
theorem exists_ideal_blowup :
    ∃ (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
      IsProperMap p.hom.left.base ∧
      (∃ q : (nativePulledIdealModule p.hom.left B b).LocalGeneratorsData.{0},
        q.IsLocallyFreeData ∧ ∀ i, Nonempty (Unique (q.generators i).I)) ∧
      (∀ y : Y.obj.left, Module.Invertible (Y.obj.left.presheaf.stalk y).carrier
        (nativePulledIdealStalkIdeal p.hom.left B b y)) ∧
      (∀ (A : SourceReducedComplexSpace) (F : A ⟶ X)
        (q : (nativePulledIdealModule F.hom.left B b).LocalGeneratorsData.{0}),
        q.IsLocallyFreeData → (∀ i, Nonempty (Unique (q.generators i).I)) →
          ∃! L : A ⟶ Y, L ≫ p = F) := by
  refine ⟨sourceObject B b,projectionMorphism B b,
    projection_isProperMap B b,
    projection_ideal_exists_locallyFreeData B b,
    projection_ideal_moduleInvertible B b,?_⟩
  intro A F q hq huniq
  let : q.IsLocallyFreeData := hq
  let : ∀ i, Unique (q.generators i).I := fun i => Classical.choice (huniq i)
  exact exists_unique_lift_of_locallyFreeData B b A F q

end
end Hironaka.Analytic.Unibranch.OriginalFiniteIdealGeometricBlowupUniversal
