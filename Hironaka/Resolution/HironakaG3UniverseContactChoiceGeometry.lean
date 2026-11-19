import Hironaka.Resolution.HironakaG3UniverseLiftedTower
import Hironaka.Invariant.StepOneValue
import Hironaka.Resolution.HironakaG3UniverseOpenDiffeo
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseContactChoiceGeometry
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue HironakaSmoothSubmersionCoefficientIdeals
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower G3UniverseOpenDiffeo
noncomputable section

/-- Literal universe lift commutes with append of actual finite towers. -/
theorem liftTower_append {n : ℕ} {X Y Z : CMfd.{0} n} (T₀ : BlowupTower X Y) (T₁ : BlowupTower Y Z) :
    liftTower.{u} (T₀.append T₁) = (liftTower.{u} T₀).append (liftTower.{u} T₁) := by
  induction T₁ with
  | refl => rfl
  | step T C π hπ ih => simp only [BlowupTower.append_step, liftTower, ih]

/-- The inverse-image original contact mask lies over the transported tangent open and avoids every actual lifted original member. -/
theorem lifted_original_maskB_geometry {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (T : BlowupTower X Y) (y : Y)
    (hMembers : origMembers (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) =
      (origMembers M T).map ((liftDiffeomorph.{u} Y).symm ⁻¹' ·)) :
    let e := (liftDiffeomorph.{u} X).symm
    let f := (liftDiffeomorph.{u} Y).symm
    let ML := markedPullback (m := n) e M
    let W := preimageOpens f (maskB M T y)
    ((W : Set (liftCMfd.{u} Y)) ⊆ (liftTower.{u} T).proj ⁻¹' (e ⁻¹' (tangentChoice M (T.proj y)).1)) ∧
    ∀ H ∈ origMembers ML (liftTower.{u} T), Disjoint (W : Set (liftCMfd.{u} Y)) H := by
  dsimp only
  constructor
  · intro z hz
    have h := (interior_subset (show (liftDiffeomorph.{u} Y).symm z ∈ maskB M T y from hz)).1
    change (liftDiffeomorph.{u} X).symm ((liftTower.{u} T).proj z) ∈ (tangentChoice M (T.proj y)).1
    rw [liftTower_proj]
    simpa using h
  · intro H hH
    rw [hMembers] at hH
    obtain ⟨H₀,hH₀,rfl⟩ := List.mem_map.mp hH
    apply Set.disjoint_left.mpr
    intro z hz hzH
    have hzM : (liftDiffeomorph.{u} Y).symm z ∈ maskB M T y := hz
    exact (interior_subset hzM).2.1 H₀ hH₀ hzH
end
end Hironaka.G3UniverseContactChoiceGeometry
