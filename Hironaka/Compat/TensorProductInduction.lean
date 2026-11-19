/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Defs

/-! Compatibility with the two-case tensor-product eliminator used in upstream Lean 4.34. -/

public section

open scoped TensorProduct

namespace TensorProduct

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

@[elab_as_elim, induction_eliminator]
theorem inductionOn {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul (0 : M) (0 : N)) tmul add

end TensorProduct
