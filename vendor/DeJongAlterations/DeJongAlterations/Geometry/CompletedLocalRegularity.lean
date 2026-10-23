import DeJongAlterations.Algebra.CompletionRegularity
import DeJongAlterations.Geometry.CompletedLocalRing
import DeJongAlterations.Regular
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! Genuine original scheme-stalk regularity reflected from the literal native completed local ring. -/

noncomputable section

open AlgebraicGeometry

namespace DeJongAlterations.Geometry.CompletedLocalRegularity

universe u
variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- The actual original stalk-to-completed-local-ring homomorphism is faithfully flat. -/
theorem toCompletedLocalRing_faithfullyFlat (x : X) : (X.toCompletedLocalRing x).FaithfullyFlat := by
  change (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x)).FaithfullyFlat
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr
    (Algebra.CompletionRegularityBasics.faithfullyFlat (X.presheaf.stalk x))

/-- The literal canonical map from the original stalk to its actual completion is injective. -/
theorem toCompletedLocalRing_injective (x : X) : Function.Injective (X.toCompletedLocalRing x) :=
  Algebra.CompletionRegularityBasics.algebraMap_injective (X.presheaf.stalk x)

/-- Regularity of the literal actual completed local ring forces regularity of the original stalk. -/
theorem isRegularLocalRing_stalk_of_completedLocalRing (x : X)
    [IsRegularLocalRing (X.completedLocalRing x)] : IsRegularLocalRing (X.presheaf.stalk x) :=
  Algebra.CompletionRegularity.isRegularLocalRing_of_completion (X.presheaf.stalk x)

/-- Regular completed local rings at all original points imply native regularity of the actual scheme. -/
theorem isRegularScheme_of_completedLocalRings
    (hX : ∀ x : X, IsRegularLocalRing (X.completedLocalRing x)) : IsRegularScheme X := by
  intro x
  let : IsRegularLocalRing (X.completedLocalRing x) := hX x
  exact isRegularLocalRing_stalk_of_completedLocalRing X x

end DeJongAlterations.Geometry.CompletedLocalRegularity
