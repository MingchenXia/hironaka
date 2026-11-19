import Hironaka.Resolution.HironakaG3UniverseLiftedTower
import Hironaka.Invariant.RestrictEmptyTower
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseLiftedTowerFootprint
open Hironaka.BlowupSequences BlowupTowers RestrictEmptyTower
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower
open ResolutionInvariantExt (IsEmptyTower)
noncomputable section

/-- The actual stage centres of the lifted tower have precisely the lifted footprint. -/
theorem liftTower_centresOver_iff {n : ℕ} {X₀ Y₀ : CMfd.{0} n}
    (F : Set X₀) (T : BlowupTower X₀ Y₀) :
    CentresOver ((liftDiffeomorph.{u} X₀).symm ⁻¹' F) (liftTower.{u} T) ↔ CentresOver F T := by
  induction T with
  | refl => rfl
  | @step Y₀ Z₀ T C π hπ ih =>
    change (CentresOver ((liftDiffeomorph.{u} X₀).symm ⁻¹' F) (liftTower.{u} T) ∧
      ((liftDiffeomorph.{u} Y₀).symm ⁻¹' C) ⊆
        (liftTower.{u} T).proj ⁻¹' ((liftDiffeomorph.{u} X₀).symm ⁻¹' F)) ↔
      (CentresOver F T ∧ C ⊆ T.proj ⁻¹' F)
    rw [ih]
    constructor
    · rintro ⟨hprev,h⟩
      refine ⟨hprev,?_⟩
      intro y hy
      have hy' : (liftDiffeomorph.{u} Y₀) y ∈ (liftDiffeomorph.{u} Y₀).symm ⁻¹' C := by
        simpa using hy
      have hz := h hy'
      change (liftDiffeomorph.{u} X₀).symm ((liftTower.{u} T).proj ((liftDiffeomorph.{u} Y₀) y)) ∈ F at hz
      change T.proj y ∈ F
      simpa only [liftTower_proj,Function.comp_apply,Diffeomorph.symm_apply_apply] using hz
    · rintro ⟨hprev,h⟩
      refine ⟨hprev,?_⟩
      intro y hy
      change (liftDiffeomorph.{u} X₀).symm ((liftTower.{u} T).proj y) ∈ F
      have hz := h hy
      change T.proj ((liftDiffeomorph.{u} Y₀).symm y) ∈ F at hz
      simpa only [liftTower_proj,Function.comp_apply,Diffeomorph.symm_apply_apply] using hz

/-- Empty stages remain empty, and no nonempty stage is lost by lifting. -/
theorem liftTower_isEmptyTower_iff {n : ℕ} {X₀ Y₀ : CMfd.{0} n} (T : BlowupTower X₀ Y₀) :
    IsEmptyTower (liftTower.{u} T) ↔ IsEmptyTower T := by
  induction T with
  | refl => rfl
  | @step Y₀ Z₀ T C π hπ ih =>
    change (IsEmptyTower (liftTower.{u} T) ∧ (liftDiffeomorph.{u} Y₀).symm ⁻¹' C = ∅) ↔
      (IsEmptyTower T ∧ C = ∅)
    rw [ih]
    constructor
    · rintro ⟨hprev,h⟩
      refine ⟨hprev,?_⟩
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hy
      have hy' : (liftDiffeomorph.{u} Y₀) y ∈ (liftDiffeomorph.{u} Y₀).symm ⁻¹' C := by
        simpa using hy
      rw [h] at hy'
      exact hy'
    · rintro ⟨hprev,h⟩
      refine ⟨hprev,?_⟩
      rw [h]
      rfl
end
end Hironaka.G3UniverseLiftedTowerFootprint
