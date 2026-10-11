/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaLocalPrincipalization

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaLocalPrincipalization
open Hironaka
noncomputable section
open BlowupSequences
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] {C : Set M} {π : Z → M}

/-- **The preimage of a compact set under a blowup is compact.** -/
theorem isCompact_preimage_of_isBlowupAlong (hπ : IsBlowupAlong n C π) {K : Set M} (hK : IsCompact K) :
    IsCompact (π ⁻¹' K) :=
  (isProperMap_of_isBlowupAlong hπ).isCompact_preimage hK


end
end Hironaka.HironakaLocalPrincipalization
