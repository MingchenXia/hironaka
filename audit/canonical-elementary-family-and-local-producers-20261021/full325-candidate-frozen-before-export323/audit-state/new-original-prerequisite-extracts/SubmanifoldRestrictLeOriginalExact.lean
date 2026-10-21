/- Complete original prerequisite; statement and mathematical proof unchanged. -/
import Hironaka.MarkedIdeal.SubmanifoldRestrictLe
import Hironaka.Analytic.SubmanifoldIdealRestriction

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.SubmanifoldRestrictLe

open Hironaka.HolomorphicIdealSheaves
open Hironaka.RestrictedIdealWeight
open Hironaka.RelativePrincipalizationSpan
open Hironaka.SubmanifoldIdealRestriction

noncomputable section

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}
  [ChartedSpace (ComplexModel k) W] [IsComplexManifold k W]

variable (hval : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X))

include hval in
/-- **The ambient restricted comparison is an inclusion of ideals on the submanifold.**  Each
germ of `𝔞` at a point of `W` agrees on `W` with `∑ cᵢ tᵢ`, `tᵢ ∈ 𝔟`; restricting the identity
to `↥W` exhibits it as a combination of germs of `Res_W 𝔟`, and `IsInSpanAt.trans` propagates
this from the generators to an arbitrary germ of `Res_W 𝔞`. -/
theorem restrictIdeal_le_of_restrictLe {𝔞 𝔟 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hle : RestrictLe W 𝔞 𝔟) :
    (restrictIdeal (k := k) (W := W) 𝔞).Le (restrictIdeal (k := k) (W := W) 𝔟) := by
  intro p G hG
  have hG' : IsInSpanAt (n := k)
      (fun s => ∃ a, 𝔞.mem p.1 a ∧ s = a ∘ (Subtype.val : W → X)) p G := hG
  show IsInSpanAt (n := k)
    (fun s => ∃ b, 𝔟.mem p.1 b ∧ s = b ∘ (Subtype.val : W → X)) p G
  refine IsInSpanAt.trans ?_ hG'
  rintro s ⟨a, hamem, rfl⟩
  obtain ⟨N, t, c, ht, hc, heq⟩ := hle p.1 p.2 a hamem
  refine ⟨holomorphicAt_comp_val hval (holomorphicAt_of_mem_of_isCoherent h𝔞 hamem),
    N, fun i => fun q : W => t i q.1, fun i => fun q : W => c i q.1,
    fun i => ⟨t i, ht i, rfl⟩,
    fun i => holomorphicAt_comp_val hval (hc i), ?_⟩
  have hev := (continuous_subtype_val.continuousAt (x := p)).eventually
    (p := fun y => y ∈ W → a y = ∑ i, c i y * t i y) heq
  filter_upwards [hev] with q hq
  exact hq q.2
end
end Hironaka.SubmanifoldRestrictLe
