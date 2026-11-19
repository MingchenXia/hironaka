import Hironaka.Geometry.QuotGrassmannPivotAffinePullbackRank
import Hironaka.Geometry.QuotGrassmannPivotAffineQuotientSections
import Hironaka.Algebra.GrassmannQuotientKernel

/-!
# SAME actual original affine quotient produces a native Grassmannian point

All finite projectivity/rank/quotient surjectivity hypotheses of the native
algebraic kernel producer are internally derived for the SAME global quotient.
The ENTIRE original kernel and EVERY original-vector readback are retained.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι ν : Type u)
  [Fintype ι] [Fintype ν] [DecidableEq ι] {A : CommRingCat.{u}}

/-- EVERY original affine test morphism gives a genuine native Grassmannian point from SAME actual quotient. -/
def originalGlobalAffineGrassmannianPoint (f : Spec A ⟶ projectiveModel R ι ν) :
    Module.Grassmannian A ((ι ⊕ ν) → A) (Fintype.card ι) := by
  have h := originalGlobalAffinePullbackSections_finitePresentation_projective R ι ν f
  let := h.1
  let := h.2
  exact Algebra.GrassmannQuotientKernel.point
    (originalGlobalAffinePullbackQuotientSections R ι ν f)
    (originalGlobalAffinePullbackQuotientSections_surjective R ι ν f)
    (Fintype.card ι) (originalGlobalAffinePullbackSections_rankAtStalk R ι ν f)

/-- The ENTIRE actual original affine quotient kernel is exactly the produced native Grassmannian submodule. -/
theorem originalGlobalAffineGrassmannianPoint_toSubmodule
    (f : Spec A ⟶ projectiveModel R ι ν) :
    (originalGlobalAffineGrassmannianPoint R ι ν f).toSubmodule =
      (originalGlobalAffinePullbackQuotientSections R ι ν f).ker := rfl

/-- The actual native Grassmannian quotient is isomorphic to SAME actual original pulled-back global-image sections. -/
def originalGlobalAffineGrassmannianQuotientEquiv (f : Spec A ⟶ projectiveModel R ι ν) :
    (((ι ⊕ ν) → A) ⧸ (originalGlobalAffineGrassmannianPoint R ι ν f).toSubmodule) ≃ₗ[A]
      Γ((Scheme.Modules.pullback f).obj (originalGlobalImageQuotient R ι ν), ⊤) :=
  (originalGlobalAffinePullbackQuotientSections R ι ν f).quotKerEquivOfSurjective
    (originalGlobalAffinePullbackQuotientSections_surjective R ι ν f)

/-- EVERY original finite-coordinate vector retains its SAME actual original affine quotient readback. -/
theorem originalGlobalAffineGrassmannianQuotientEquiv_mkQ
    (f : Spec A ⟶ projectiveModel R ι ν) (v : (ι ⊕ ν) → A) :
    originalGlobalAffineGrassmannianQuotientEquiv R ι ν f
        ((originalGlobalAffineGrassmannianPoint R ι ν f).toSubmodule.mkQ v) =
      originalGlobalAffinePullbackQuotientSections R ι ν f v :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ v

/-- The actual native quotient reads back the SAME original global sheaf quotient on EVERY original vector. -/
theorem originalGlobalAffineGrassmannianQuotientEquiv_original_triangle
    (f : Spec A ⟶ projectiveModel R ι ν) (v : (ι ⊕ ν) → A) :
    originalGlobalAffineGrassmannianQuotientEquiv R ι ν f
        ((originalGlobalAffineGrassmannianPoint R ι ν f).toSubmodule.mkQ v) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pullback f).map
        (originalGlobalQuotient R ι ν))
          ((originalGlobalAffinePullbackSourceSectionsIso R ι ν f).hom v) :=
  (originalGlobalAffineGrassmannianQuotientEquiv_mkQ R ι ν f v).trans
    (originalGlobalAffinePullbackQuotientSections_apply R ι ν f v)

end Hironaka.Geometry.QuotGrassmann
