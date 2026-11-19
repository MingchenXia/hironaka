import Hironaka.Resolution.HironakaG3UniversePhysicalClassComparisons

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3IdentityHistoryAtlas

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MaxLocusLocal
  HironakaG3RTowerClass HironakaOriginalTerminalOverlapComparison G3UniversePhysicalClassComparisons

/-- Members have no blowup steps, hence are literal `BlowupTower.refl` histories. -/
def identityHistoryClass {n : ℕ} {X : CMfd.{u} n} : LocalTowerClass X :=
  fun _ _ T => T.length = 0

/-- The identity has a zero-step saturated chart on every specified open. -/
noncomputable def identity_history_chart {n : ℕ} {X : CMfd.{u} n} (U : Opens X) :
    TowerChart (identityHistoryClass (X := X)) X (id : X → X) :=
  ⟨U, CMfd.of (n := n) U, .refl, rfl, U, rfl,
    Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞, fun _ => rfl⟩

theorem identity_history_hasPhysicalComparisons {n : ℕ} (X : CMfd.{u} n) :
    HasPhysicalComparisons (identityHistoryClass (X := X)) := by
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
  change T₁.length = 0 at h₁
  change T₂.length = 0 at h₂
  cases T₁ with
  | step => simp at h₁
  | refl =>
    cases T₂ with
    | step => simp at h₂
    | refl => exact ⟨overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right, .refl⟩

theorem identity_history_atlas {n : ℕ} (X : CMfd.{u} n) :
    IsGluedFrom (identityHistoryClass (X := X)) X (id : X → X) :=
  ⟨contMDiff_id, isProperMap_id, surjective_id, fun _ => ⟨identity_history_chart ⊤, trivial⟩⟩

end Hironaka.HironakaG3IdentityHistoryAtlas
