/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.RegularPatchPullback

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold
namespace Hironaka.RegularPatchPullback
noncomputable section
open Hironaka
variable {n : ℕ}

/-- The same local holomorphic equivalence, recentred at another point of its source. -/
def recenter {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p) (q : ComplexModel n)
    (hq : q ∈ Φ.source) : LocalHolomorphicEquivAt (n := n) q :=
  { Φ with center_mem_source := hq }

end
end Hironaka.RegularPatchPullback
