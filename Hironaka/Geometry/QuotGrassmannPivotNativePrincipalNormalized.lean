import Hironaka.Geometry.QuotGrassmannPivotNativePrincipalMatrices
import Hironaka.Algebra.PluckerQuotTransitionComplementNormalization

/-!
# An actual native quotient internally yields the original normalized local quotient

The entire original quotient is compared under actual native source and target
isomorphisms on the principal cover derived from the point itself. This does
not yet glue inverse scheme morphisms or claim relative representability.
-/

noncomputable section

open scoped Classical TensorProduct

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuotTransition

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (E : Type u) [Fintype E] [DecidableEq E] (r : ℕ)

/-- SAME actual native point alone produces a finite unit-ideal principal cover and BOTH WHOLE original normalized-quotient triangles, preserving its original selected indices and actual complement. -/
theorem originalNativeGrassmannian_exists_finitePrincipalNormalizedQuotients
    (N : Module.Grassmannian A (A ⊗[R] (E → R)) r) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ g ∈ s, ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I) (a : I ↪ E),
        Nat.card I = r ∧ ∃
          (e : LocalizedModule (Submonoid.powers g) ((A ⊗[R] (E → R)) ⧸ N.toSubmodule) ≃ₗ[Localization.Away g]
            (I → Localization.Away g))
          (C : Matrix I ((Set.range a)ᶜ : Set E) (Localization.Away g)),
          e.toLinearMap.comp
            ((originalLocalizedCoordinateQuotient
              (originalNativeGrassmannianCoordinateQuotient R A E r N) (Submonoid.powers g)).comp
              (LinearEquiv.funCongrLeft (Localization.Away g) (Localization.Away g)
                (originalPivotComplementEquiv a).symm).toLinearMap) =
            Algebra.PluckerQuot.matrixQuotient C ∧
          e.symm.toLinearMap.comp (Algebra.PluckerQuot.matrixQuotient C) =
            (originalLocalizedCoordinateQuotient
              (originalNativeGrassmannianCoordinateQuotient R A E r N) (Submonoid.powers g)).comp
              (LinearEquiv.funCongrLeft (Localization.Away g) (Localization.Away g)
                (originalPivotComplementEquiv a).symm).toLinearMap := by
  obtain ⟨s, hspan, hs⟩ := originalNativeGrassmannian_exists_finitePrincipalPivotMatrices R A E r N
  refine ⟨s, hspan, ?_⟩
  intro g hg
  obtain ⟨I, hI, a, hcard, e, C, hwhole, _, hpivot⟩ := hs g hg
  let : Fintype I := Fintype.ofFinite I
  let : DecidableEq I := Classical.decEq I
  have hnormalized := originalPivotComplementMatrix_whole_quotient C a hpivot
  have hf : e.toLinearMap.comp
      ((originalLocalizedCoordinateQuotient
        (originalNativeGrassmannianCoordinateQuotient R A E r N) (Submonoid.powers g)).comp
        (LinearEquiv.funCongrLeft (Localization.Away g) (Localization.Away g)
          (originalPivotComplementEquiv a).symm).toLinearMap) =
      Algebra.PluckerQuot.matrixQuotient (originalPivotComplementMatrix C a) := by
    rw [← LinearMap.comp_assoc, hwhole]
    exact hnormalized
  refine ⟨I, inferInstance, inferInstance, a, hcard, e, originalPivotComplementMatrix C a, hf, ?_⟩
  apply LinearMap.ext
  intro v
  have hv := LinearMap.congr_fun hf v
  exact (congrArg e.symm hv.symm).trans (e.symm_apply_apply _)

end Hironaka.Geometry.QuotGrassmann
