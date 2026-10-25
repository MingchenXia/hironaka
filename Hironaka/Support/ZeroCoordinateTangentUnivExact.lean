/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.MarkedIdeal.TangentDirectionAlong
import Hironaka.MarkedIdeal.MaximalContact
import Hironaka.Support.ZeroCoordinateDerivativeUnivExact
import Hironaka.Support.TangentFieldUnivExact

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.TangentDirectionAlong
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences Hironaka.GermIdealOrder Hironaka.DerivativeIdeal Hironaka.DerivativeIdealAlong Hironaka.GiraudAlong Hironaka.BlowupFlatCoordinates Hironaka.DerivativeIdealAlongCoherent Hironaka.RelativePrincipalizationSpan
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
variable {N : Set M} {𝔞 : GermIdeal n M}

theorem fieldDeriv_const (e : ComplexChart n M) (v : ComplexModel n) (f : M → ℂ) (p : M) :
    fieldDeriv e (fun m _ => v m) f p = chartDeriv e v f p := by
  simp only [fieldDeriv, chartDeriv]
  conv_rhs => rw [← sum_smul_single v]
  rw [map_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [map_smul, smul_eq_mul]

theorem isTangentDirectionAlong_univ_iff (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {μ : ℕ} {U : Set M}
    {u : M → ℂ} : IsTangentDirectionAlong univ 𝔞 μ U u ↔ MaximalContact.IsTangentDirection 𝔞 μ U u := by
  constructor
  · rintro ⟨hU, hmem, hmult⟩
    refine ⟨hU, fun x hx => ?_, fun x hx hux => ?_⟩
    · rw [← iterDerivIdealAlong_univ h𝔞]
      exact hmem x hx
    · obtain ⟨e, ξ, hξ, hne⟩ := hmult x hx hux
      obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      exact ⟨e, EuclideanSpace.single m 1, hξ.mem_source, right_ne_zero_of_mul hm⟩
  · rintro ⟨hU, hmem, hmult⟩
    refine ⟨hU, fun x hx => ?_, fun x hx hux => ?_⟩
    · rw [iterDerivIdealAlong_univ h𝔞]
      exact hmem x hx
    · obtain ⟨e, v, hxe, hne⟩ := hmult x hx hux
      exact ⟨e, fun m _ => v m, isTangentField_univ hxe fun m => holomorphicAt_const _,
        by rw [fieldDeriv_const]; exact hne⟩

end
end Hironaka.TangentDirectionAlong
