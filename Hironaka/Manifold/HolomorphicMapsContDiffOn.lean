/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Manifold.HolomorphicMaps

set_option autoImplicit false
open scoped Manifold ContDiff Topology
open Set Filter
namespace Hironaka.HolomorphicMaps
noncomputable section
variable {k n : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold k V] [IsComplexManifold n M]

theorem coordinateMap_contDiffOn {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (e : ComplexChart k V) (d : ComplexChart n M) :
    ContDiffOn ℂ ∞ (coordinateMap f e d) (coordinateDomain f e d) :=
  fun _ hz => (coordinateMap_contDiffAt hf e d hz).contDiffWithinAt

end
end Hironaka.HolomorphicMaps
