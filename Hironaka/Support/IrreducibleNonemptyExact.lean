/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Analytic.ComplexAnalyticSubvarieties
open Set
open scoped Manifold ContDiff Topology

namespace Hironaka

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

variable [hM : IsComplexManifold n M]
namespace IsComplexAnalyticallyIrreducible
variable {A B C : Set M}

theorem nonempty (hA : IsComplexAnalyticallyIrreducible (n := n) A) : A.Nonempty :=
  hA.2.1

end IsComplexAnalyticallyIrreducible
end
end Hironaka
