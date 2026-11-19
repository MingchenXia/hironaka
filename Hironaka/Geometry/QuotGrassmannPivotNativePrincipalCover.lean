import Hironaka.Algebra.PluckerQuotTransitionPrincipalCover
import Mathlib.RingTheory.Grassmannian
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# SAME original native Grassmannian quotient has an actual finite principal pivot cover

The native point itself supplies the quotient, finite projectivity and rank.
Original tensor coordinates construct its actual surjection. No cover, pivot
invertibility, frame or classifier inverse is an input.
-/

noncomputable section

open TensorProduct

namespace Hironaka.Geometry.QuotGrassmann

universe u v

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (E : Type v) [Fintype E] [DecidableEq E] (r : ℕ)

/-- The SAME original native quotient, in its actual ORIGINAL finite coordinate source via the genuine inverse tensor-coordinate isomorphism. -/
def originalNativeGrassmannianCoordinateQuotient
    (N : Module.Grassmannian A (A ⊗[R] (E → R)) r) :
    (E → A) →ₗ[A] ((A ⊗[R] (E → R)) ⧸ N.toSubmodule) :=
  N.toSubmodule.mkQ.comp (TensorProduct.piScalarRight R A A E).symm.toLinearMap

/-- Native quotient surjectivity and the genuine actual source inverse derive surjectivity of SAME original coordinate quotient. -/
theorem originalNativeGrassmannianCoordinateQuotient_surjective
    (N : Module.Grassmannian A (A ⊗[R] (E → R)) r) :
    Function.Surjective (originalNativeGrassmannianCoordinateQuotient R A E r N) :=
  (Submodule.mkQ_surjective N.toSubmodule).comp (TensorProduct.piScalarRight R A A E).symm.surjective

/-- The WHOLE ORIGINAL native quotient map is retained under the genuine actual tensor-coordinate source isomorphism. -/
theorem originalNativeGrassmannianCoordinateQuotient_tensor_triangle
    (N : Module.Grassmannian A (A ⊗[R] (E → R)) r) :
    (originalNativeGrassmannianCoordinateQuotient R A E r N).comp
      (TensorProduct.piScalarRight R A A E).toLinearMap = N.toSubmodule.mkQ := by
  apply LinearMap.ext
  intro u
  exact congrArg N.toSubmodule.mkQ ((TensorProduct.piScalarRight R A A E).symm_apply_apply u)

/-- An actual native Grassmannian point INTERNALLY produces finitely many original principal unit-ideal generators with SAME native quotient ORIGINAL rank-r pivot maps bijective after localization. -/
theorem originalNativeGrassmannian_exists_finitePrincipalPivotCover
    (N : Module.Grassmannian A (A ⊗[R] (E → R)) r) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ g ∈ s, ∃ (I : Type v) (_ : Finite I) (a : I ↪ E),
        Nat.card I = r ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers g)
          (Finsupp.linearCombination A (fun i : I =>
            originalNativeGrassmannianCoordinateQuotient R A E r N
              (Pi.single (a i) (1 : A))))) := by
  let M := (A ⊗[R] (E → R)) ⧸ N.toSubmodule
  let : Module.FinitePresentation A M := Module.finitePresentation_of_projective A M
  exact Algebra.PluckerQuotTransition.originalQuotient_exists_finitePrincipalPivotCover
    (originalNativeGrassmannianCoordinateQuotient R A E r N)
    (originalNativeGrassmannianCoordinateQuotient_surjective R A E r N) r N.rankAtStalk_eq

end Hironaka.Geometry.QuotGrassmann
