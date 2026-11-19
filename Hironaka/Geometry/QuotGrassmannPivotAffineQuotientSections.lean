import Hironaka.Geometry.QuotGrassmannPivotAffinePullbackProjectivity
import Hironaka.Geometry.QuotGrassmannPivotPullbackFree
import Hironaka.Geometry.QuotGrassmannAffine

/-!
# SAME actual original quotient on affine sections, with ORIGINAL source coordinates

The canonical native free pullback and original tilde coordinate frame construct
an explicit source-section isomorphism. The whole linear quotient is the literal
native global sections of SAME original pulled-back global quotient. Its actual
epimorphism and surjectivity are derived from native affine quasicoherence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι ν : Type u)
  [Fintype ι] [Fintype ν] [DecidableEq ι] {A : CommRingCat.{u}}

/-- The actual source-section isomorphism preserves the ORIGINAL coordinate module and canonical native pullback. -/
def originalGlobalAffinePullbackSourceSectionsIso
    (f : Spec A ⟶ projectiveModel R ι ν) :
    ModuleCat.of A ((ι ⊕ ν) → A) ≅ moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback f).obj
        (SheafOfModules.free (R := (projectiveModel R ι ν).ringCatSheaf) (ι ⊕ ν))) :=
  tilde.isoTop (ModuleCat.of A ((ι ⊕ ν) → A)) ≪≫
    moduleSpecΓFunctor.mapIso (coordinateSheafIsoFree A (ι ⊕ ν)) ≪≫
    moduleSpecΓFunctor.mapIso (originalPullbackFreeIso f (ι ⊕ ν)).symm

/-- The literal native original affine quotient in the SAME ORIGINAL coordinate module. -/
def originalGlobalAffinePullbackQuotientSections
    (f : Spec A ⟶ projectiveModel R ι ν) :
    ((ι ⊕ ν) → A) →ₗ[A]
      Γ((Scheme.Modules.pullback f).obj (originalGlobalImageQuotient R ι ν), ⊤) :=
  ((originalGlobalAffinePullbackSourceSectionsIso R ι ν f).hom ≫
    moduleSpecΓFunctor.map ((Scheme.Modules.pullback f).map
      (originalGlobalQuotient R ι ν))).hom

/-- EVERY original vector satisfies the literal actual pulled-back global quotient/source coordinate triangle. -/
theorem originalGlobalAffinePullbackQuotientSections_apply
    (f : Spec A ⟶ projectiveModel R ι ν) (v : (ι ⊕ ν) → A) :
    originalGlobalAffinePullbackQuotientSections R ι ν f v =
      moduleSpecΓFunctor.map ((Scheme.Modules.pullback f).map
        (originalGlobalQuotient R ι ν))
          ((originalGlobalAffinePullbackSourceSectionsIso R ι ν f).hom v) := rfl

/-- SAME original native pullback quotient is epi on actual affine global sections, derived internally. -/
theorem originalGlobalAffinePullbackQuotientSections_epi
    (f : Spec A ⟶ projectiveModel R ι ν) :
    Epi (ModuleCat.ofHom (originalGlobalAffinePullbackQuotientSections R ι ν f)) := by
  let S := SheafOfModules.free (R := (projectiveModel R ι ν).ringCatSheaf) (ι ⊕ ν)
  let : ((Scheme.Modules.pullback f).obj S).IsLocallyFree :=
    originalSchemePullback_isLocallyFree f S
  let : (Scheme.Modules.pullback f).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.pullbackPushforwardAdjunction f)
  have : Epi (originalGlobalQuotient R ι ν) := originalGlobalQuotient_epi R ι ν
  have : Epi ((Scheme.Modules.pullback f).map (originalGlobalQuotient R ι ν)) :=
    Functor.map_epi (Scheme.Modules.pullback f) (originalGlobalQuotient R ι ν)
  have hq : Epi (moduleSpecΓFunctor.map ((Scheme.Modules.pullback f).map
      (originalGlobalQuotient R ι ν))) :=
    ProperSteinProjectiveCech.affineQuasicoherentSpec_globalEpi _
  have : Epi ((originalGlobalAffinePullbackSourceSectionsIso R ι ν f).hom ≫
      moduleSpecΓFunctor.map ((Scheme.Modules.pullback f).map
        (originalGlobalQuotient R ι ν))) := inferInstance
  exact this

/-- The SAME actual native original affine-section quotient is surjective on EVERY original element. -/
theorem originalGlobalAffinePullbackQuotientSections_surjective
    (f : Spec A ⟶ projectiveModel R ι ν) :
    Function.Surjective (originalGlobalAffinePullbackQuotientSections R ι ν f) := by
  have := originalGlobalAffinePullbackQuotientSections_epi R ι ν f
  exact (ModuleCat.epi_iff_surjective
    (ModuleCat.ofHom (originalGlobalAffinePullbackQuotientSections R ι ν f))).mp inferInstance

end Hironaka.Geometry.QuotGrassmann
