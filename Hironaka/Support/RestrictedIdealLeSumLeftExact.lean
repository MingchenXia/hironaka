/- Exact complete original declaration and declaration context; namespace relocation only. -/
import Hironaka.MarkedIdeal.RestrictedIdealExtension
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.RestrictedIdealExtension
noncomputable section
open Hironaka.HolomorphicIdealSheaves
open Hironaka.IdealWeightComparison
open Hironaka.IdealWeightPowers
open Hironaka.RelativePrincipalizationSpan
open Hironaka.RestrictedIdealWeight
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

theorem le_sumIdeal_left {𝔞 𝔟 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) :
    𝔞.Le (sumIdeal 𝔞 𝔟) := by
  intro x g hg
  exact isInSpanAt_of_eq_mul (S := fun s => 𝔞.mem x s ∨ 𝔟.mem x s) (Or.inl hg)
    (GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) (holomorphicAt_const 1)
    (Eventually.of_forall fun y => (one_mul _).symm)

theorem le_sumIdeal_right {𝔞 𝔟 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) :
    𝔟.Le (sumIdeal 𝔞 𝔟) := by
  intro x g hg
  exact isInSpanAt_of_eq_mul (S := fun s => 𝔞.mem x s ∨ 𝔟.mem x s) (Or.inr hg)
    (GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hg) (holomorphicAt_const 1)
    (Eventually.of_forall fun y => (one_mul _).symm)

end
end Hironaka.RestrictedIdealExtension
