import Hironaka.Geometry.QuotGrassmannPivotNativeLocalInverse

/-! The original native quotient constructs an evaluated finite principal inverse cover. -/

noncomputable section

open scoped Classical TensorProduct
open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot Algebra.PluckerQuotTransition

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (ι ν : Type u) [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

/-- The native original quotient internally supplies actual original evaluated pivot charts
on a finite original unit-ideal cover, retaining the original matrix and permutation. -/
theorem originalNativeGrassmannian_exists_finitePrincipalEvaluatedInverse
    (N : Module.Grassmannian A (A ⊗[R] ((ι ⊕ ν) → R)) (Fintype.card ι)) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ g ∈ s, ∃ (p : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C : Matrix ι ν (Localization.Away g)),
        originalGlobalAffineGrassmannianTensorPoint R ι ν
            (originalMatrixEvaluatedPivotMorphism R p C) =
          Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away g)) N := by
  obtain ⟨s, hspan, hs⟩ := originalNativeGrassmannian_exists_finitePrincipalFixedNormalizedQuotients
    R A ι ν N
  refine ⟨s, hspan, ?_⟩
  intro g hg
  obtain ⟨p, e, C, hwhole, _⟩ := hs g hg
  refine ⟨p, C, ?_⟩
  let q := originalLocalizedCoordinateQuotient
    (originalNativeGrassmannianCoordinateQuotient R A (ι ⊕ ν) (Fintype.card ι) N) (Submonoid.powers g)
  have hf : e.toLinearMap.comp q = (splitNormalizedMatrix p C).mulVecLin := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ :=
      (LinearEquiv.funCongrLeft (Localization.Away g) (Localization.Away g) p.symm).surjective v
    exact (LinearMap.congr_fun hwhole w).trans
      (LinearMap.congr_fun (originalSplitNormalizedMatrix_whole_quotient p C) w).symm
  let π := (TensorProduct.piScalarRight R (Localization.Away g) (Localization.Away g) (ι ⊕ ν)).toLinearMap
  have ht : e.toLinearMap.comp (q.comp π) = (splitNormalizedMatrix p C).mulVecLin.comp π := by
    rw [← LinearMap.comp_assoc, hf]
  have hkernel : (q.comp π).ker = ((splitNormalizedMatrix p C).mulVecLin.comp π).ker :=
    (LinearEquiv.ker_comp e (q.comp π)).symm.trans (congrArg LinearMap.ker ht)
  apply Module.Grassmannian.ext
  exact (originalMatrixEvaluatedPivotClassifier_toSubmodule R p C).trans
    (hkernel.symm.trans
      (originalNativeGrassmannian_localization_map_toSubmodule R A (Submonoid.powers g)
        (ι ⊕ ν) (Fintype.card ι) N).symm)

end Hironaka.Geometry.QuotGrassmann
