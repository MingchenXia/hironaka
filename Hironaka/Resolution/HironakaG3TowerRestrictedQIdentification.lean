import Hironaka.Resolution.HironakaG3RigidOverLocalGlue
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3RigidOverLocalGlue
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3RTowerClass HironakaG3RGluedUniqueness
variable {n : ℕ} {X X₁ X₂ : CMfd.{u} n}

/-- The literal restriction of a continuous map to the inverse image of a base open. -/
def restrictedBaseMap (Q : X₂ → X) (hQ : Continuous Q) (A : Opens X) :
    window Q hQ A → A := fun y => ⟨Q y.val,y.property⟩

theorem restrictedBaseMap_continuous (Q : X₂ → X) (hQ : Continuous Q) (A : Opens X) :
    Continuous (restrictedBaseMap Q hQ A) :=
  Continuous.subtype_mk (hQ.comp continuous_subtype_val) _

/-- A tower is identified with the actual restricted map from local comparisons. -/
theorem identify_tower_with_restricted_map {B : CMfd.{u} n} (A : Opens X)
    (M : BlowupTower (CMfd.of (n := n) A) B)
    (Q : X₂ → X) (hQ : Continuous Q) {𝒞 : LocalTowerClass X}
    (hchQ : ∀ x, ∃ c : TowerChart 𝒞 X₂ Q, x ∈ c.U)
    {J : Type v} (V : J → Opens A) (hcover : ∀ x : A, ∃ j, x ∈ V j)
    (φ : ∀ j, (CMfd.of (n := n) (window M.proj M.contMDiff_proj.continuous (V j)))
      ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯
      (CMfd.of (n := n) (window (X := CMfd.of (n := n) A)
        (X₁ := CMfd.of (n := n) (window Q hQ A))
        (restrictedBaseMap Q hQ A) (restrictedBaseMap_continuous Q hQ A) (V j))))
    (hφ : ∀ j (z : window M.proj M.contMDiff_proj.continuous (V j)),
      (restrictedBaseMap Q hQ A) (φ j z).val = M.proj z.val) :
    ∃! Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (window Q hQ A),
      ∀ z, (restrictedBaseMap Q hQ A) (Φ z) = M.proj z := by
  have hRQ : RigidOver (X := CMfd.of (n := n) A)
      (X₂ := CMfd.of (n := n) (window Q hQ A)) (restrictedBaseMap Q hQ A) :=
    rigid_of_open_restriction hQ (rigid_of_tower_charts hchQ) A
  exact existsUnique_gluedLocalDiffeomorph M.contMDiff_proj.continuous
    (restrictedBaseMap_continuous Q hQ A) V hcover φ (rigid_of_tower M) hRQ hφ

end
end Hironaka.HironakaG3RigidOverLocalGlue
