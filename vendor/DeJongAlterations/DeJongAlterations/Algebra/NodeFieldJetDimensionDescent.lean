import DeJongAlterations.Algebra.NodeFieldUVJetLength
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Descend the genuine finite jets along the SAME original field extension.
Only actual finite-jet tensor products occur; no completed tensor identity is assumed. -/

noncomputable section

open IsLocalRing TensorProduct

namespace DeJongAlterations.Algebra.NodeFieldJetDimensionDescent

universe u v w z
variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]

section Modules

variable {M : Type w} [AddCommGroup M] [Module K M]
  {N : Type z} [AddCommGroup N] [Module L N]

/-- Finiteness of the ORIGINAL module follows by genuine faithful-flat descent. -/
theorem finite_of_tensorEquiv [Module.Finite L N] (e : L ⊗[K] M ≃ₗ[L] N) :
    Module.Finite K M := by
  let : Module.Finite L (L ⊗[K] M) := Module.Finite.equiv e.symm
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat L

/-- The original dimension uses the SAME original coefficient field and actual extension. -/
theorem finrank_of_tensorEquiv (e : L ⊗[K] M ≃ₗ[L] N) :
    Module.finrank K M = Module.finrank L N := by
  calc
    Module.finrank K M = Module.finrank L (L ⊗[K] M) := Module.finrank_baseChange.symm
    _ = Module.finrank L N := e.finrank_eq

end Modules

open NodeGeometricCompletionFormalUV NodeFieldUVJetLength

variable (C : Type w) [CommRing C] [IsLocalRing C] [Algebra K C]

/-- The ACTUAL original maximal-power quotient is finite dimensional, including order zero. -/
theorem originalJet_finiteDimensional (n : ℕ)
    (e : L ⊗[K] (C ⧸ maximalIdeal C ^ n) ≃ₗ[L]
      (FormalUV L ⧸ maximalIdeal (FormalUV L) ^ n)) :
    FiniteDimensional K (C ⧸ maximalIdeal C ^ n) :=
  finite_of_tensorEquiv K L e

/-- The genuine entire original jet quotient has its derived native rank at EVERY order. -/
theorem originalJet_finrank_succ (n : ℕ)
    (e : L ⊗[K] (C ⧸ maximalIdeal C ^ (n + 1)) ≃ₗ[L]
      (FormalUV L ⧸ maximalIdeal (FormalUV L) ^ (n + 1))) :
    Module.finrank K (C ⧸ maximalIdeal C ^ (n + 1)) = 2 * n + 1 :=
  (finrank_of_tensorEquiv K L e).trans (nativeJet_finrank_succ L n)

/-- The original first infinitesimal neighbourhood has dimension THREE, internally. -/
theorem originalJet_finrank_two
    (e : L ⊗[K] (C ⧸ maximalIdeal C ^ 2) ≃ₗ[L]
      (FormalUV L ⧸ maximalIdeal (FormalUV L) ^ 2)) :
    Module.finrank K (C ⧸ maximalIdeal C ^ 2) = 3 :=
  originalJet_finrank_succ K L C 1 e

/-- The actual original cubic-power quotient has dimension FIVE, internally. -/
theorem originalJet_finrank_three
    (e : L ⊗[K] (C ⧸ maximalIdeal C ^ 3) ≃ₗ[L]
      (FormalUV L ⧸ maximalIdeal (FormalUV L) ^ 3)) :
    Module.finrank K (C ⧸ maximalIdeal C ^ 3) = 5 :=
  originalJet_finrank_succ K L C 2 e

end DeJongAlterations.Algebra.NodeFieldJetDimensionDescent
