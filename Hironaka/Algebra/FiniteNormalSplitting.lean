import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Normal.Closure

/-!
# One genuine finite normal common field, including inseparable extensions

The actual normal closure is taken in the canonical algebraic closure.
No separability assumption or supplied ambient field is needed.
-/

noncomputable section

namespace Hironaka.Algebra.FiniteNormalSplitting

open IntermediateField

universe u

variable (K : Type u) [Field K] {ι : Type u} [Finite ι] (E : ι → Type u)
  [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, FiniteDimensional K (E i)]

/-- An actual compatible embedding of each finite extension into the canonical algebraic closure. -/
def componentEmbedding (i : ι) : E i →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift

/-- Its actual original image field. -/
def componentImage (i : ι) : IntermediateField K (AlgebraicClosure K) :=
  (componentEmbedding K E i).fieldRange

instance componentImage_finite (i : ι) : FiniteDimensional K (componentImage K E i) :=
  (componentEmbedding K E i).toLinearMap.finiteDimensional_range

/-- The finite compositum of the actual component image fields. -/
def compositum : IntermediateField K (AlgebraicClosure K) := ⨆ i, componentImage K E i

instance compositum_finite : FiniteDimensional K (compositum K E) :=
  IntermediateField.finiteDimensional_iSup_of_finite

/-- The actual common normal field, allowing inseparable component extensions. -/
def commonField : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.normalClosure K (compositum K E) (AlgebraicClosure K)

instance commonField_finite : FiniteDimensional K (commonField K E) :=
  normalClosure.is_finiteDimensional K (compositum K E) (AlgebraicClosure K)

instance commonField_normal : Normal K (commonField K E) :=
  normalClosure.normal K (compositum K E) (AlgebraicClosure K)

/-- Every original field embeds in the same internally constructed finite normal field. -/
def embedding (i : ι) : E i →ₐ[K] commonField K E :=
  (componentEmbedding K E i).codRestrict (commonField K E).toSubalgebra (fun x =>
    ((le_iSup (fun j => componentImage K E j) i).trans
      (IntermediateField.le_normalClosure (compositum K E))) ⟨x, rfl⟩)

omit [Finite ι] in
/-- The embeddings preserve their actual original values in the algebraic closure. -/
theorem embedding_val (i : ι) (x : E i) :
    (embedding K E i x : AlgebraicClosure K) = componentEmbedding K E i x := rfl

end Hironaka.Algebra.FiniteNormalSplitting
