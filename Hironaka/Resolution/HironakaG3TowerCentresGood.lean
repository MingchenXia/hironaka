import Hironaka.Resolution.HironakaG3GluedClassFootprint
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3TowerCentresGood
noncomputable section
open Hironaka.BlowupSequences BlowupTowers RestrictEmptyTower EmbeddedFromResolution

theorem tower_isomorphism_off_closed_footprint {n : ℕ} {X Y : CMfd.{0} n}
    (F : Set X) (hF : IsClosed F) (T : BlowupTower X Y) (hOver : CentresOver F T) :
    IsIsomorphismOver n T.proj Fᶜ := by
  let O : Opens X := ⟨Fᶜ,hF.isOpen_compl⟩
  have hAvoid : CentresAvoid O T := centresAvoid_of_centresOver O disjoint_compl_left T hOver
  have hImage := image_exceptionalLocus_subset_compl O T hAvoid
  have hImage' : T.proj '' exceptionalLocus n T.proj ⊆ F := by
    change T.proj '' exceptionalLocus n T.proj ⊆ (Fᶜ)ᶜ at hImage
    simpa only [compl_compl] using hImage
  exact HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset T.isBlowupSequence hImage'
end
end Hironaka.HironakaG3TowerCentresGood
