import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Normal.Closure

/-!
# One actual finite Galois extension for a finite family of separable fields

Each original field embeds into the canonical separable closure. The normal
closure of the finite compositum of their actual image fields gives one
internally constructed finite Galois extension containing every member.
-/

noncomputable section

namespace DeJongAlterations.Algebra.FiniteSeparableSplitting

open IntermediateField

universe u

variable (K : Type u) [Field K] {ι : Type u} [Finite ι] (E : ι → Type u)
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    [∀ i, FiniteDimensional K (E i)] [∀ i, Algebra.IsSeparable K (E i)]

/-- The actual embedding of each original separable extension into the canonical separable closure. -/
def componentEmbedding (i : ι) : E i →ₐ[K] SeparableClosure K := IsSepClosed.lift

/-- Its actual image field in the common canonical separable closure. -/
def componentImage (i : ι) : IntermediateField K (SeparableClosure K) :=
  (componentEmbedding K E i).fieldRange

/-- Each actual image field is finite over the original field. -/
instance componentImage_finite (i : ι) : FiniteDimensional K (componentImage K E i) :=
  (componentEmbedding K E i).toLinearMap.finiteDimensional_range

/-- The actual finite compositum of all original image fields. -/
def compositum : IntermediateField K (SeparableClosure K) := ⨆ i, componentImage K E i

/-- Finiteness of the family gives finiteness of its actual compositum. -/
instance compositum_finite : FiniteDimensional K (compositum K E) :=
  IntermediateField.finiteDimensional_iSup_of_finite

/-- The internally constructed common field is the actual normal closure inside the separable closure. -/
def commonField : IntermediateField K (SeparableClosure K) :=
  IntermediateField.normalClosure K (compositum K E) (SeparableClosure K)

/-- The constructed common field is finite over the original field. -/
instance commonField_finite : FiniteDimensional K (commonField K E) :=
  normalClosure.is_finiteDimensional K (compositum K E) (SeparableClosure K)

/-- The constructed common field is Galois over the original field, including over imperfect fields. -/
instance commonField_isGalois : IsGalois K (commonField K E) :=
  IsGalois.normalClosure K (compositum K E) (SeparableClosure K)

/-- The original component embedding genuinely lands in the same constructed common field. -/
def embedding (i : ι) : E i →ₐ[K] commonField K E :=
  (componentEmbedding K E i).codRestrict (commonField K E).toSubalgebra (fun x =>
    ((le_iSup (fun j => componentImage K E j) i).trans
      (IntermediateField.le_normalClosure (compositum K E))) ⟨x, rfl⟩)

omit [Finite ι] [∀ i, FiniteDimensional K (E i)] in
/-- The common-field embeddings retain their actual original separable-closure values. -/
theorem embedding_val (i : ι) (x : E i) :
    (embedding K E i x : SeparableClosure K) = componentEmbedding K E i x := rfl

end DeJongAlterations.Algebra.FiniteSeparableSplitting
