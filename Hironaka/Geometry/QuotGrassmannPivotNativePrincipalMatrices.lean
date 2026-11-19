import Hironaka.Geometry.QuotGrassmannPivotNativePrincipalFrames
import Hironaka.Algebra.PluckerQuotTransitionLocalizedMatrix

/-!
# SAME actual native quotient internally produces its entire original local matrix

The principal cover, original pivot indices and actual target maps are
derived from the native point. Both whole quotient triangles and every
original coefficient are those of the SAME localized quotient.
-/

noncomputable section

open scoped Classical TensorProduct

namespace Hironaka.Geometry.QuotGrassmann

universe u v

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (E : Type v) [Fintype E] [DecidableEq E] (r : ℕ)

/-- Actual native N alone produces an original finite principal cover, actual target isomorphisms, and the WHOLE original localized quotient matrices with identity original pivot columns. -/
theorem originalNativeGrassmannian_exists_finitePrincipalPivotMatrices
    (N : Module.Grassmannian A (A ⊗[R] (E → R)) r) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ g ∈ s, ∃ (I : Type v) (_ : Finite I) (a : I ↪ E), Nat.card I = r ∧
        ∃ (e : LocalizedModule (Submonoid.powers g) ((A ⊗[R] (E → R)) ⧸ N.toSubmodule) ≃ₗ[Localization.Away g]
            (I → Localization.Away g)) (C : Matrix I E (Localization.Away g)),
          e.toLinearMap.comp
            (Algebra.PluckerQuotTransition.originalLocalizedCoordinateQuotient
              (originalNativeGrassmannianCoordinateQuotient R A E r N) (Submonoid.powers g)) = C.mulVecLin ∧
          e.symm.toLinearMap.comp C.mulVecLin =
            Algebra.PluckerQuotTransition.originalLocalizedCoordinateQuotient
              (originalNativeGrassmannianCoordinateQuotient R A E r N) (Submonoid.powers g) ∧
          ∀ i j, C i (a j) = if i = j then 1 else 0 := by
  obtain ⟨s, hspan, hs⟩ := originalNativeGrassmannian_exists_finitePrincipalPivotFrames R A E r N
  refine ⟨s, hspan, ?_⟩
  intro g hg
  obtain ⟨I, hI, a, hcard, e, he⟩ := hs g hg
  refine ⟨I, hI, a, hcard, e,
    Algebra.PluckerQuotTransition.originalFramedLocalizedQuotientMatrix
      (originalNativeGrassmannianCoordinateQuotient R A E r N) (Submonoid.powers g) e,
    Algebra.PluckerQuotTransition.originalFramedLocalizedQuotientMatrix_whole_triangle _ _ _,
    Algebra.PluckerQuotTransition.originalFramedLocalizedQuotientMatrix_whole_triangle_inv _ _ _, ?_⟩
  exact Algebra.PluckerQuotTransition.originalFramedLocalizedQuotientMatrix_pivot _ _ _ a he

end Hironaka.Geometry.QuotGrassmann
