/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MemberPullback

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.MemberPullback
open Hironaka
noncomputable section
open HolomorphicIdealSheaves RelativePrincipalizationSpan InvertibleIdealQuotient
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]


/-- **Products of principal ideals**: if `𝔞 = (p)` and `𝔟 = (q)` at `x`, then `𝔞 𝔟 = (p q)` at
`x`. -/
theorem mul_mem_iff_of_generators {𝔞 𝔟 : GermIdeal n M} {x : M} {p q : M → ℂ}
    (hp : ∀ g, 𝔞.mem x g ↔ IsInSpanAt (n := n) (· = p) x g)
    (hq : ∀ g, 𝔟.mem x g ↔ IsInSpanAt (n := n) (· = q) x g)
    (hph : HolomorphicAt n p x) (hqh : HolomorphicAt n q x) (g : M → ℂ) :
    (𝔞.mul 𝔟).mem x g ↔ IsInSpanAt (n := n) (· = fun y => p y * q y) x g := by
  show IsInSpanAt (n := n) (fun s => ∃ a b, 𝔞.mem x a ∧ 𝔟.mem x b ∧ s = a * b) x g ↔ _
  constructor
  · intro hg
    refine IsInSpanAt.of_forall_eq_mul ?_ hg
    rintro s ⟨a, b, ha, hb, rfl⟩
    obtain ⟨-, c, hc, hac⟩ := isInSpanAt_eq_iff.mp ((hp a).mp ha)
    obtain ⟨-, d, hd, hbd⟩ := isInSpanAt_eq_iff.mp ((hq b).mp hb)
    refine ⟨fun y => c y * d y, hc.mul hd, ?_⟩
    filter_upwards [hac, hbd] with y h1 h2
    simp only [Pi.mul_apply, h1, h2]
    ring
  · intro hg
    refine IsInSpanAt.trans (fun s hs => ?_) hg
    subst hs
    exact isInSpanAt_of_eq_mul ⟨p, q, (hp p).mpr (isInSpanAt_of_eq_mul rfl hph
      (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp)), (hq q).mpr
      (isInSpanAt_of_eq_mul rfl hqh (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => by simp)),
      rfl⟩ (hph.mul hqh) (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp)


end
end Hironaka.MemberPullback
