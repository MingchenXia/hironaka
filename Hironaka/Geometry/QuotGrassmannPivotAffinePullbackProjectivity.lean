import Hironaka.Geometry.QuotGrassmannPivotAffineProjectiveSections
import Hironaka.Geometry.QuotGrassmannPivotGlobalLocalFrames
import Hironaka.Geometry.QuotGrassmannPivotPullbackGenerators

/-!
# EVERY actual affine pullback of SAME original global quotient has projective sections

Actual original pivot generators are genuinely pulled back. Their finite indices
and native generating isomorphisms are preserved internally. No output property
is assumed of the original quotient or its actual affine pullback.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι ν : Type u)
  [Fintype ι] [Fintype ν] [DecidableEq ι] {A : CommRingCat.{u}}

/-- The SAME original global-image generating data on its original inverse-image affine cover. -/
def originalGlobalAffinePullbackGenerators (f : Spec A ⟶ projectiveModel R ι ν) :
    ((Scheme.Modules.pullback f).obj (originalGlobalImageQuotient R ι ν)).LocalGeneratorsData :=
  originalPullbackLocalGeneratorsData f (originalGlobalImageLocalGeneratorsData R ι ν)

/-- The SAME original finite row generator indices survive the genuine native affine pullback. -/
theorem originalGlobalAffinePullbackGenerators_index
    (f : Spec A ⟶ projectiveModel R ι ν) (i : (originalGlobalAffinePullbackGenerators R ι ν f).I) :
    ((originalGlobalAffinePullbackGenerators R ι ν f).generators i).I = ι := rfl

/-- Actual native generating isomorphisms are internally produced on the SAME original inverse-image cover. -/
instance originalGlobalAffinePullbackGenerators_isLocallyFreeData
    (f : Spec A ⟶ projectiveModel R ι ν) :
    (originalGlobalAffinePullbackGenerators R ι ν f).IsLocallyFreeData := by
  change (originalPullbackLocalGeneratorsData f
    (originalGlobalImageLocalGeneratorsData R ι ν)).IsLocallyFreeData
  infer_instance

/-- Every actual original generating family remains finite, with precisely the original row indices. -/
instance originalGlobalAffinePullbackGenerators_isFiniteType
    (f : Spec A ⟶ projectiveModel R ι ν) :
    (originalGlobalAffinePullbackGenerators R ι ν f).IsFiniteType := by
  change (originalPullbackLocalGeneratorsData f
    (originalGlobalImageLocalGeneratorsData R ι ν)).IsFiniteType
  infer_instance

/-- The genuine actual affine pullback of SAME original global quotient is natively locally free. -/
instance originalGlobalAffinePullback_isLocallyFree
    (f : Spec A ⟶ projectiveModel R ι ν) :
    ((Scheme.Modules.pullback f).obj (originalGlobalImageQuotient R ι ν)).IsLocallyFree :=
  (originalGlobalAffinePullbackGenerators R ι ν f).isLocallyFree

/-- EVERY actual original affine pullback has finite presented projective SAME actual global sections. -/
theorem originalGlobalAffinePullbackSections_finitePresentation_projective
    (f : Spec A ⟶ projectiveModel R ι ν) :
    Module.FinitePresentation A
      Γ((Scheme.Modules.pullback f).obj (originalGlobalImageQuotient R ι ν), ⊤) ∧
    Module.Projective A
      Γ((Scheme.Modules.pullback f).obj (originalGlobalImageQuotient R ι ν), ⊤) :=
  originalAffineLocalGeneratorsSections_finitePresentation_projective
    (originalGlobalAffinePullbackGenerators R ι ν f)

end Hironaka.Geometry.QuotGrassmann
