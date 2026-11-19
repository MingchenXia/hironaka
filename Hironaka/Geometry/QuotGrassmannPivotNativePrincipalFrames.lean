import Hironaka.Geometry.QuotGrassmannPivotNativePrincipalCover
import Hironaka.Algebra.PluckerQuotTransitionPivotTargetFrame

/-!
# SAME actual native quotient internally produces original principal target frames

The finite original cover, selected original columns and actual bijections
are produced from N itself. Both target maps and every selected coordinate
unit readback follow from those SAME actual maps; no frame is an input.
-/

noncomputable section

open scoped Classical TensorProduct

namespace Hironaka.Geometry.QuotGrassmann

universe u v

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (E : Type v) [Fintype E] [DecidableEq E] (r : ℕ)

/-- SAME native Grassmannian point INTERNALLY constructs an actual finite principal unit-ideal cover, rank-r ORIGINAL column embeddings and BOTH native local target maps with exact original unit-coordinate readbacks. -/
theorem originalNativeGrassmannian_exists_finitePrincipalPivotFrames
    (N : Module.Grassmannian A (A ⊗[R] (E → R)) r) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ g ∈ s, ∃ (I : Type v) (_ : Finite I) (a : I ↪ E),
        Nat.card I = r ∧ ∃ e :
          LocalizedModule (Submonoid.powers g) ((A ⊗[R] (E → R)) ⧸ N.toSubmodule) ≃ₗ[Localization.Away g]
            (I → Localization.Away g),
          ∀ i, e (LocalizedModule.mkLinearMap (Submonoid.powers g) _
            (originalNativeGrassmannianCoordinateQuotient R A E r N
              (Pi.single (a i) (1 : A)))) = Pi.single i (1 : Localization.Away g) := by
  obtain ⟨s, hspan, hs⟩ := originalNativeGrassmannian_exists_finitePrincipalPivotCover R A E r N
  refine ⟨s, hspan, ?_⟩
  intro g hg
  obtain ⟨I, hI, a, hcard, hbij⟩ := hs g hg
  let : Finite I := hI
  refine ⟨I, hI, a, hcard,
    Algebra.PluckerQuotTransition.originalPrincipalPivotTargetFrame
      (originalNativeGrassmannianCoordinateQuotient R A E r N) a g hbij, ?_⟩
  exact Algebra.PluckerQuotTransition.originalPrincipalPivotTargetFrame_column
    (originalNativeGrassmannianCoordinateQuotient R A E r N) a g hbij

end Hironaka.Geometry.QuotGrassmann
