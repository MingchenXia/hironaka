import Hironaka.Resolution.HironakaG3Nonerasure
import Hironaka.Invariant.MemberInterTowerAlong

/-! Density away from a closed original boundary survives an avoiding tower. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DenseEscape
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower

/-- Every point of the strict target is a limit of points of that same strict
target away from the strict transform of the original closed obstacle. -/
theorem strictAlong_subset_closure_diff_of_centresAvoid
    {n : ℕ} {X Y : CMfd.{0} n} (A H : Set X) (hA : IsClosed A) (hH : IsClosed H)
    (hDense : A ⊆ closure (A \ H)) (T : BlowupTower X Y)
    (hAvoid : RestrictEmptyTower.CentresAvoid ⟨Hᶜ, hH.isOpen_compl⟩ T) :
    strictAlong T A ⊆ closure (strictAlong T A \ strictAlong T H) := by
  let O : Opens X := ⟨Hᶜ, hH.isOpen_compl⟩
  have hDenseO : A ⊆ closure (A ∩ (O : Set X)) := by
    change A ⊆ closure (A ∩ Hᶜ)
    simpa only [sdiff_eq] using hDense
  have hEq := HironakaG8P1ArcTangentTrace.strictAlong_eq_conventional_of_centresAvoid
    A hA O hDenseO T hAvoid
  have hD := HironakaAdmissibleCalculus.strictTransform_subset_closure_diff
    T.contMDiff_proj hA hDense
  have hSub := MemberInterTowerAlong.strictAlong_subset_preimage T hH
  rw [← hEq] at hD
  exact hD.trans (closure_mono (sdiff_subset_sdiff_right hSub))

end
end Hironaka.HironakaG3DenseEscape
