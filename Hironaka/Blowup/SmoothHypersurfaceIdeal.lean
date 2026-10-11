/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupFlatCoordinates

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The actual invertible ideal of a smooth hypersurface

The original coordinate/Hadamard proof supplies a genuine principal
local generator, including its nonvanishing on every nonempty open set.
Only its original reusable statement and proof are restored here.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.BlowupExistenceCodimOne

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  Hironaka.BlowupFlatCoordinates

noncomputable section

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **The ideal of a smooth hypersurface is invertible.**  At a point off the (closed) centre
the generator is `1`; at a point of the centre it is the last flattening coordinate. -/
theorem isInvertible_vanishingIdeal_of_codimOne {C : Set X} (hCclosed : IsClosed C)
    (hCint : interior C = ∅)
    (hcodim : ∀ x ∈ C, ∃ k, RegularAtDim (n := n) C x k ∧ k + 1 = n) :
    (vanishingIdeal (n := n) C).IsInvertible := by
  intro x
  by_cases hx : x ∈ C
  · obtain ⟨k, hreg, hk⟩ := hcodim x hx
    obtain ⟨hkn, -, Φ, hΦsrc, -, hflat⟩ := hreg
    have hkn' : k < n := by omega
    set i₀ : Fin n := ⟨k, hkn'⟩ with hi₀
    have hi₀val : (i₀ : ℕ) = k := rfl
    -- on the flattening domain, `C` is exactly the zero set of the last flattening coordinate
    have hzero : ∀ y ∈ flatDomain Φ, (y ∈ C ↔ flatCoord Φ i₀ y = 0) := by
      intro y hy
      rw [hflat hy.1 hy.2]
      constructor
      · intro h; exact h i₀ le_rfl
      · intro h i hi
        have hlt := i.isLt
        have : i = i₀ := Fin.ext (by omega)
        rw [this]; exact h
    refine ⟨flatDomain Φ, isOpen_flatDomain Φ, mem_flatDomain_self Φ, flatCoord Φ i₀,
      fun y hy => (holomorphicAt_flatCoord Φ i₀ hy).mdifferentiableAt.mdifferentiableWithinAt,
      ?_, fun y hy g => ?_⟩
    · -- no nonempty open subset of the flattening domain lies inside `C`
      rintro W hW hWsub ⟨y, hy⟩
      by_contra hcon
      have hcon' : ∀ z ∈ W, flatCoord Φ i₀ z = 0 := fun z hz => by
        by_contra hz0; exact hcon ⟨z, hz, hz0⟩
      have hWC : W ⊆ C := fun z hz => (hzero z (hWsub hz)).mpr (hcon' z hz)
      have : y ∈ interior C := mem_interior.mpr ⟨W, hWC, hW, hy⟩
      rw [hCint] at this
      exact this
    · constructor
      · intro hg
        obtain ⟨b, hb0, hbhol, hbeq⟩ := exists_eq_sum_flatCoord Φ hΦsrc hflat hy hg
        refine isInSpanAt_eq_iff.mpr ⟨hg.1, b i₀, hbhol i₀, ?_⟩
        filter_upwards [hbeq] with z hz
        rw [hz, Finset.sum_eq_single i₀ (fun i _ hi => ?_) (by simp)]
        have hlt := i.isLt
        have : i.1 < k := by
          rcases lt_or_ge i.1 k with h | h
          · exact h
          · exact absurd (Fin.ext (show i.1 = (i₀ : ℕ) by omega) : i = i₀) hi
        rw [hb0 i this]; simp
      · rintro hg
        obtain ⟨-, a, -, heq⟩ := isInSpanAt_eq_iff.mp hg
        refine ⟨hg.1, ?_⟩
        filter_upwards [heq, (isOpen_flatDomain Φ).mem_nhds hy] with z hz hz' hzC
        rw [hz, (hzero z hz').mp hzC, mul_zero]
  · refine ⟨Cᶜ, hCclosed.isOpen_compl, hx, fun _ => 1,
      fun y _ => mdifferentiableAt_const.mdifferentiableWithinAt,
      fun W _ _ ⟨y, hy⟩ => ⟨y, hy, one_ne_zero⟩, fun y hy g => ?_⟩
    constructor
    · intro hg
      exact isInSpanAt_of_eq_mul rfl hg.1 hg.1 (Eventually.of_forall fun _ => by simp)
    · intro hg
      refine ⟨hg.1, ?_⟩
      filter_upwards [hCclosed.isOpen_compl.mem_nhds hy] with z hz hzC
      exact absurd hzC hz

end

end Hironaka.BlowupExistenceCodimOne
