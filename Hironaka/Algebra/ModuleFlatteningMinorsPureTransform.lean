import Hironaka.Algebra.ModuleFlatteningMinors
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The actual tensor-image pure transform over a fraction subalgebra

The canonical coefficient inclusion defines the original tensor map. Its
actual image is computed from the original module generator span, preserving
all original generator maps.
-/

noncomputable section

open Module TensorProduct
open scoped TensorProduct

namespace Hironaka.Algebra.ModuleFlatteningMinorsPureTransform

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R M : Type u) [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

/-- The canonical actual tensor map induced by the original fraction-subalgebra inclusion. -/
def tensorMap (S : Subalgebra R (FractionRing R)) :
    S ⊗[R] M →ₗ[S] FractionRing R ⊗[R] M :=
  AlgebraTensorModule.map (Algebra.linearMap S (FractionRing R)) (LinearMap.id : M →ₗ[R] M)

omit [IsDomain R] in
/-- The original module generator maps to its literal original generic tensor image. -/
@[simp]
theorem tensorMap_one_tmul (S : Subalgebra R (FractionRing R)) (m : M) :
    tensorMap R M S ((1 : S) ⊗ₜ[R] m) = (1 : FractionRing R) ⊗ₜ[R] m := by
  simp [tensorMap]

/-- The actual pure transform is the image of the original canonical chart tensor map. -/
abbrev pureTransform (S : Subalgebra R (FractionRing R)) :
    Submodule S (FractionRing R ⊗[R] M) := (tensorMap R M S).range

omit [IsDomain R] in
/-- The actual original tensor image is exactly the span of the original generic module generators. -/
theorem pureTransform_eq_span {κ : Type v} (S : Subalgebra R (FractionRing R))
    (m : κ → M) (hm : Submodule.span R (Set.range m) = ⊤) :
    pureTransform R M S = Submodule.span S (Set.range fun j ↦ (1 : FractionRing R) ⊗ₜ[R] m j) := by
  have hbase : Submodule.span S (Set.range fun j ↦ (1 : S) ⊗ₜ[R] m j) = ⊤ := by
    have h := congrArg (fun p : Submodule R M ↦ p.baseChange S) hm
    simpa only [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp,
      Function.comp_def, TensorProduct.mk_apply] using h
  change (tensorMap R M S).range = _
  rw [← Submodule.map_top, ← hbase, Submodule.map_span, ← Set.range_comp]
  simp only [Function.comp_def, tensorMap_one_tmul]

end Hironaka.Algebra.ModuleFlatteningMinorsPureTransform
