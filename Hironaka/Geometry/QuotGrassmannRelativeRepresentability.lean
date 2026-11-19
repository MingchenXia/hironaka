import Hironaka.Geometry.QuotGrassmannPivotNativeGlobalInverse
import Hironaka.Geometry.QuotGrassmannPivotGlobalClassifierInjective
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.CategoryTheory.Yoneda

/-! Relative representability for the SAME original native finite-projective quotient functor. -/

noncomputable section

open scoped Classical TensorProduct
open CategoryTheory AlgebraicGeometry Opposite

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R]
  (ι ν : Type u) [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

/-- The actual original classifier is an equivalence on actual native morphisms over
the original base, with the SAME unframed finite-projective quotient as its target. -/
def originalRelativeAffineGrassmannianEquiv (A : CommAlgCat.{u, u} R) :
    (((algSpec (CommRingCat.of R)).obj (op A)) ⟶ Over.mk (projectiveStructure R ι ν)) ≃
      Module.Grassmannian A (A ⊗[R] ((ι ⊕ ν) → R)) (Fintype.card ι) :=
  Equiv.ofBijective (fun f => originalGlobalAffineGrassmannianTensorPoint R ι ν
    (A := CommRingCat.of A) f.left) (by
    constructor
    · intro f g h
      apply Over.OverMorphism.ext
      exact originalGlobalAffineGrassmannianTensorPoint_injective_over_base R (A := A)
        f.left g.left (Over.w f) (Over.w g) h
    · intro N
      obtain ⟨f, hf, hN⟩ := originalNativeGrassmannian_exists_globalInverse R A ι ν N
      exact ⟨Over.homMk f hf, hN⟩)

/-- The SAME original projective model represents the original native Grassmannian functor
of unframed finite-projective quotients, using native relative Spec and native relative Yoneda. -/
def originalRelativeGrassmannianRepresentability :
    (algSpec (CommRingCat.of R)).rightOp ⋙ yoneda.obj (Over.mk (projectiveStructure R ι ν)) ≅
      Module.Grassmannian.functor (R := R) (M := ((ι ⊕ ν) → R)) (Fintype.card ι) :=
  NatIso.ofComponents (fun A => (originalRelativeAffineGrassmannianEquiv R ι ν A).toIso) (by
    intro A B φ
    ext f
    exact (originalGlobalAffineGrassmannianTensorPoint_map R ι ν
      (A := CommRingCat.of A) (B := CommRingCat.of B) φ.hom f.left).symm)

end Hironaka.Geometry.QuotGrassmann
