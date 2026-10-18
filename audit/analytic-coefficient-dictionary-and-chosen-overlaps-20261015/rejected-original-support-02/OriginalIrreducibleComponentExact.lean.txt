/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Analytic.SingularLocus
open Set Filter
open scoped Topology ENNReal NNReal ContDiff
namespace Hironaka
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- `V` is an irreducible component of `S`: a closed irreducible analytic
subvariety contained in `S` and maximal among such subvarieties. -/
def IsIrreducibleComponent (V : ClosedIrreducibleAnalyticSubvariety n M)
    (S : Set M) : Prop :=
  V.carrier ⊆ S ∧
    ∀ Z : ClosedIrreducibleAnalyticSubvariety n M,
      V.carrier ⊆ Z.carrier → Z.carrier ⊆ S → Z.carrier = V.carrier

end
end Hironaka
