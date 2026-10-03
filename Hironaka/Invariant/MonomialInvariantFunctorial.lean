/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MonomialResolution
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport
import Hironaka.Invariant.MonomialCase
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The invariant of the monomial case under open restrictions, biholomorphisms and empty blowups
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MonomialInvariantFunctorial

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.DivisorExponent Hironaka.MonomialPart Hironaka.MonomialCase Hironaka.MonomialResolution Hironaka.MonomialInvariant Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealTowerTransport Hironaka.NormalCrossings

noncomputable section

variable {n : ℕ}

/-! ### Exponents and the invariant along maps that pull back cosupports -/

section Pullback

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
  {φ : M' → M} {𝔞 : GermIdeal n M}
  (hcos : ∀ e, cosupport n univ (GermIdeal.pullback (m := n) φ 𝔞) e = φ ⁻¹' cosupport n univ 𝔞 e)
  {x' : M'} (hmap : Filter.map φ (𝓝 x') = 𝓝 (φ x'))
include hcos hmap

omit hcos hmap in
/-- The members of `φ⁻¹E` through `x'` are those of `E` through `φ x'`. -/
theorem memberIdx_map_preimage (E : List (Set M)) (x' : M') :
    memberIdx (E.map (φ ⁻¹' ·)) x' = memberIdx E (φ x') := by
  ext i
  rw [mem_memberIdx, mem_memberIdx]
  constructor
  · rintro ⟨hi, hx⟩
    refine ⟨by simpa using hi, ?_⟩
    simpa using hx
  · rintro ⟨hi, hx⟩
    refine ⟨by simpa using hi, ?_⟩
    simpa using hx

end Pullback

end

end Hironaka.MonomialInvariantFunctorial
