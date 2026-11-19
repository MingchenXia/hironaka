import Hironaka.Algebra.FiniteMorphismFlatteningLocalization
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The original algebra-image kernel is exactly the actual base torsion

The native tensor cancellation map identifies the original generic map
with localization at the nonzero elements of the actual fraction chart.
Its original kernel is therefore exactly chart-base torsion, as in de
Jong 2.18, including for nonreduced algebras.
-/

noncomputable section

open scoped TensorProduct

namespace Hironaka.Algebra.FiniteMorphismFlattening

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

/-- The actual canonical algebra-image kernel consists exactly of original chart-base torsion. -/
theorem tensorAlgMap_eq_zero_iff_chart_torsion (S : Subalgebra R (FractionRing R))
    (z : S ⊗[R] A) :
    tensorAlgMap R A S z = 0 ↔ ∃ d : S, d ≠ 0 ∧ d • z = 0 := by
  let T := S ⊗[R] A
  let L := FractionRing R ⊗[S] T
  let : Algebra T L := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid T (nonZeroDivisors S)) L :=
    inferInstance
  have he : chartGenericTensorEquiv R A S (algebraMap T L z) = tensorAlgMap R A S z :=
    DFunLike.congr_fun (chartGenericTensorEquiv_comp_includeRight R A S) z
  rw [← he, map_eq_zero_iff _ (chartGenericTensorEquiv R A S).injective,
    IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid T (nonZeroDivisors S)) L]
  constructor
  · rintro ⟨⟨_, d, hd, rfl⟩, h⟩
    refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp hd, ?_⟩
    exact (Algebra.smul_def (R := S) (A := T) d z).trans h
  · rintro ⟨d, hd, h⟩
    refine ⟨⟨algebraMap S T d, d, mem_nonZeroDivisors_iff_ne_zero.mpr hd, rfl⟩, ?_⟩
    change algebraMap S T d * z = 0
    exact (Algebra.smul_def (R := S) (A := T) d z).symm.trans h

/-- The original algebra modulo its actual chart-base torsion is the same actual algebra image. -/
def chartTorsionQuotientEquiv (S : Subalgebra R (FractionRing R)) :=
  Ideal.quotientKerEquivRange (R := S) (A := S ⊗[R] A)
    (B := FractionRing R ⊗[R] A) (tensorAlgMap R A S)

end Hironaka.Algebra.FiniteMorphismFlattening
