/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.Invariant.AmbientDivisorExponent

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.DivisorExponentAlong
open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.DivisorExponent
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
section Exponent
variable {N : Set M} {𝔞 : GermIdeal n M} {H : Set M} {r : M → M}

/-- For `N = univ` this is `DivisorExponent.IsDivNear`. -/
theorem isDivNearAlong_univ_iff {e : ℕ} {x : M} : IsDivNearAlong n univ 𝔞 H e x ↔ IsDivNear n 𝔞 H e x :=
  ⟨fun h => Filter.Eventually.mono h fun z hz => hz (mem_univ z),
    fun h => Filter.Eventually.mono h fun _ hz _ => hz⟩

/-- For `N = univ` this is `DivisorExponent.divExp`. -/
theorem divExpAlong_univ {x : M} : divExpAlong n univ 𝔞 H x = divExp n 𝔞 H x := by
  have hfun : IsDivNearAlong n univ 𝔞 H = IsDivNear n 𝔞 H :=
    funext fun _ => funext fun _ => propext isDivNearAlong_univ_iff
  unfold divExpAlong divExp
  rw [hfun]

end Exponent
end
end Hironaka.DivisorExponentAlong
