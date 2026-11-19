import Hironaka.Analytic.Unibranch.OriginalFiniteIdealBlowup
import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupOriginalBimeromorphic
import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupGlobalCartier
import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupGlobalUniversal

/-!
# The ordinary dense-unit-image finite-ideal blowup endpoint

The SAME generated original Y/p has its own whole ideal rank-one data
DERIVED and the full original universal property for every original A/F.
Private selected model geometry is transparently specialized, never input
or exported as a desired certificate. No all-zero-component claim.
Blueprint FIRST: `original-finite-ideal-blowup-universal.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalFiniteIdealBlowupUniversal

open Hironaka HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealSheaf SourceReducedComplexSpace OriginalFiniteIdealBlowup

noncomputable section

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType]
  (hDense : Dense {x : X.obj.left |
    LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})

/-- The SAME ordinary constructed projection is ORIGINAL proper bimeromorphic;
all target-locus and full complement-isomorphism data are internally derived. -/
theorem projection_isProperBimeromorphic :
    IsProperBimeromorphic (projectionMorphism B b hDense) := by
  unfold OriginalFiniteIdealBlowup.projectionMorphism
  exact EmbeddedIdealBlowupOriginalBimeromorphic.projection_isProperBimeromorphic
    _ _ _ B b _ _ _

/-- OWN standard native rank-one data for the SAME entire pulled ideal;
no own-projection generator or ideal isomorphism certificate is supplied. -/
theorem projection_ideal_exists_locallyFreeData :
    ∃ q : (nativePulledIdealModule (projectionMorphism B b hDense).hom.left B b).LocalGeneratorsData.{0},
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (Unique (q.generators i).I) := by
  unfold OriginalFiniteIdealBlowup.projectionMorphism
  exact EmbeddedIdealBlowupGlobalCartier.projection_ideal_exists_locallyFreeData _ _ _ B b _ _

/-- Native invertibility of the ENTIRE same projection ideal at every
actual original source stalk, without radicalization or domain replacement. -/
theorem projection_ideal_moduleInvertible (y : (sourceObject B b hDense).obj.left) :
    Module.Invertible ((sourceObject B b hDense).obj.left.presheaf.stalk y).carrier
      (nativePulledIdealStalkIdeal (projectionMorphism B b hDense).hom.left B b y) := by
  unfold OriginalFiniteIdealBlowup.projectionMorphism
  exact EmbeddedIdealBlowupGlobalCartier.projection_ideal_moduleInvertible _ _ _ B b _ _ y

/-- EVERY ORIGINAL source with standard rank-one data on the SAME whole
F-pulled ideal has a UNIQUE FULL ORIGINAL lift over the actual projection. -/
theorem exists_unique_lift_of_locallyFreeData (A : SourceReducedComplexSpace) (F : A ⟶ X)
    (q : (nativePulledIdealModule F.hom.left B b).LocalGeneratorsData)
    [q.IsLocallyFreeData] [∀ i, Unique (q.generators i).I] :
    ∃! L : A ⟶ sourceObject B b hDense, L ≫ projectionMorphism B b hDense = F := by
  unfold OriginalFiniteIdealBlowup.sourceObject OriginalFiniteIdealBlowup.projectionMorphism
  exact EmbeddedIdealBlowupGlobalUniversal.exists_unique_lift_of_locallyFreeData
    _ _ _ B b _ _ _ A F q

include hDense in
/-- ONLY ordinary original finite-type data and the EXPLICIT dense unit-image
locus internally produce the actual blowup object, own Cartier data and full UP.
The chosen witness is exactly the preceding ordinary sourceObject/projection. -/
theorem exists_ideal_blowup :
    ∃ (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
      IsProperBimeromorphic p ∧
      Function.Surjective p.hom.left.base ∧
      (∃ q : (nativePulledIdealModule p.hom.left B b).LocalGeneratorsData.{0},
        q.IsLocallyFreeData ∧ ∀ i, Nonempty (Unique (q.generators i).I)) ∧
      (∀ y : Y.obj.left, Module.Invertible (Y.obj.left.presheaf.stalk y).carrier
        (nativePulledIdealStalkIdeal p.hom.left B b y)) ∧
      (∀ (A : SourceReducedComplexSpace) (F : A ⟶ X)
        (q : (nativePulledIdealModule F.hom.left B b).LocalGeneratorsData.{0}),
        q.IsLocallyFreeData → (∀ i, Nonempty (Unique (q.generators i).I)) →
          ∃! L : A ⟶ Y, L ≫ p = F) := by
  refine ⟨sourceObject B b hDense,projectionMorphism B b hDense,
    projection_isProperBimeromorphic B b hDense,
    projection_surjective B b hDense,
    projection_ideal_exists_locallyFreeData B b hDense,
    projection_ideal_moduleInvertible B b hDense,?_⟩
  intro A F q hq huniq
  let : q.IsLocallyFreeData := hq
  let : ∀ i, Unique (q.generators i).I := fun i => Classical.choice (huniq i)
  exact exists_unique_lift_of_locallyFreeData B b hDense A F q

end
end Hironaka.Analytic.Unibranch.OriginalFiniteIdealBlowupUniversal
