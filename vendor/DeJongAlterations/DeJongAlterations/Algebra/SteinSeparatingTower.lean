import DeJongAlterations.Algebra.SteinSeparability
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!
# The actual separating family after algebraic coefficient enlargement

The rational intermediate fields are both actual subfields of the
original ambient field.  The inclusion and scalar tower are constructed.
-/

noncomputable section

open IntermediateField

namespace DeJongAlterations.Algebra.SteinSeparatingTower

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K L F : Type u} [Field K] [Field L] [Field F]
  [Algebra K L] [Algebra K F] [Algebra L F] [IsScalarTower K L F]
  {ι : Type u} (v : ι → F)

/-- The two actual intermediate rational fields give the required inclusion internally. -/
theorem isSeparable_adjoin
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) F] :
    Algebra.IsSeparable (IntermediateField.adjoin L (Set.range v)) F := by
  let A := IntermediateField.adjoin K (Set.range v)
  let B := IntermediateField.adjoin L (Set.range v)
  have hle : A ≤ B.restrictScalars K :=
    IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin L (Set.range v))
  let i : A →ₐ[K] B := IntermediateField.inclusion hle
  let : Algebra A B := i.toRingHom.toAlgebra
  let : IsScalarTower A B F := .of_algebraMap_eq' rfl
  exact Algebra.isSeparable_tower_top_of_isSeparable A B F

/-- The same family is a separating transcendence basis over the actual algebraic enlargement. -/
theorem separatingBasis_of_algebraic [Algebra.IsAlgebraic K L]
    (h : IsTranscendenceBasis K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) F] :
    IsTranscendenceBasis L v ∧
      Algebra.IsSeparable (IntermediateField.adjoin L (Set.range v)) F :=
  ⟨(Algebra.IsAlgebraic.isTranscendenceBasis_iff K L).mp h,
    isSeparable_adjoin (K := K) (L := L) v⟩

end DeJongAlterations.Algebra.SteinSeparatingTower
