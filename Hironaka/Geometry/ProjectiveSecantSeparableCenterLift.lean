import Hironaka.Geometry.ProjectiveRationalPointCoordinatesScalarLift
import Mathlib.FieldTheory.IsSepClosed

/-!
# The same original separable coefficient centre lifts to the same original separable closure
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveRationalPointCoordinates BlowupProjectiveEmbedding

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsSeparable k L]

/-- The actual original separable coefficient extension internally supplies its actual embedding into the SAME original separable closure. -/
def originalSeparableClosureEmbedding : L →ₐ[k] SeparableClosure k := IsSepClosed.lift

variable (n : ℕ) (p : Spec (.of L) ⟶ projectiveSpace L (n + 1))
  (hp : p ≫ projectiveSpaceStructure L (n + 1) = 𝟙 _)

/-- The same original actual separable centre internally produces its actual rational centre in the SAME original separable closure. -/
def separableClosureCenter : Spec (.of (SeparableClosure k)) ⟶ projectiveSpace (SeparableClosure k) (n + 1) :=
  scalarPoint L (SeparableClosure k) (originalSeparableClosureEmbedding k L).toRingHom n p hp

/-- The entire actual scalar-centre new coefficient triangle is literal. -/
theorem separableClosureCenter_structure :
    separableClosureCenter k L n p hp ≫ projectiveSpaceStructure (SeparableClosure k) (n + 1) = 𝟙 _ :=
  scalarPoint_structure L (SeparableClosure k) (originalSeparableClosureEmbedding k L).toRingHom n p hp

/-- The internally chosen actual embedding and actual point retain the WHOLE original-k scheme morphism triangle. -/
theorem separableClosureCenter_original_triangle :
    separableClosureCenter k L n p hp ≫
      projectiveCoefficientMap (algebraMap k (SeparableClosure k)) (n + 1) =
    Spec.map (CommRingCat.ofHom (originalSeparableClosureEmbedding k L).toRingHom) ≫
      (p ≫ projectiveCoefficientMap (algebraMap k L) (n + 1)) := by
  let χ := originalSeparableClosureEmbedding k L
  have hχ : χ.toRingHom.comp (algebraMap k L) = algebraMap k (SeparableClosure k) :=
    RingHom.ext fun a => χ.commutes a
  have hcoef := projectiveCoefficientMap_comp (algebraMap k L) χ.toRingHom (n + 1)
  rw [hχ] at hcoef
  rw [← hcoef, ← Category.assoc, separableClosureCenter, scalarPoint_original, Category.assoc]

/-- The actual centre images in the SAME original parameter space are equal, derived from the WHOLE original coefficient triangle. -/
theorem separableClosureCenter_original_pointImage :
    projectiveCoefficientMap (algebraMap k (SeparableClosure k)) (n + 1)
      (pointImage (SeparableClosure k) n (separableClosureCenter k L n p hp)) =
    projectiveCoefficientMap (algebraMap k L) (n + 1) (pointImage L n p) := by
  have h := congrArg (fun g : Spec (.of (SeparableClosure k)) ⟶ projectiveSpace k (n + 1) =>
    g (⊥ : PrimeSpectrum (SeparableClosure k))) (separableClosureCenter_original_triangle k L n p hp)
  have hpoint : Spec.map (CommRingCat.ofHom (originalSeparableClosureEmbedding k L).toRingHom)
      (⊥ : PrimeSpectrum (SeparableClosure k)) = (⊥ : PrimeSpectrum L) := Subsingleton.elim _ _
  simpa only [Scheme.Hom.comp_apply, pointImage, hpoint] using h

/-- Membership in ANY actual original parameter open is retained by the internally produced actual closure centre. -/
theorem separableClosureCenter_mem_original_open (O : (projectiveSpace k (n + 1)).Opens)
    (hpO : projectiveCoefficientMap (algebraMap k L) (n + 1) (pointImage L n p) ∈ O) :
    projectiveCoefficientMap (algebraMap k (SeparableClosure k)) (n + 1)
      (pointImage (SeparableClosure k) n (separableClosureCenter k L n p hp)) ∈ O := by
  rw [separableClosureCenter_original_pointImage]
  exact hpO

end Hironaka.Geometry.ProjectiveSecant
