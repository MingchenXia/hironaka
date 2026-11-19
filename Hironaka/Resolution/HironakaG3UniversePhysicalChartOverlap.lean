import Hironaka.Resolution.HironakaG3UniverseChartRestriction
import Hironaka.Resolution.HironakaG3UniverseOverlapBase
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareJoin
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniversePhysicalChartOverlap
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MaxLocusLocal
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower G3UniverseOpenDiffeo G3UniverseChartTowerTransport
  G3UniverseChartRestriction G3UniverseOverlapBase G3UniverseEmptyAwareCore
  G3UniverseEmptyAwareLift G3UniverseEmptyAwareJoin HironakaOriginalTerminalOverlapComparison
noncomputable section

/-- Two supplied physical isomorphisms and a small overlap comparison yield the actual lifted overlap comparison. -/
theorem lifted_physical_overlap_of_isos {n : ℕ} {X : CMfd.{u} n} {X₀ Y₁ Y₂ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀) (U V : Opens X₀)
    (T₁ : BlowupTower (CMfd.of (n := n) U) Y₁) (T₂ : BlowupTower (CMfd.of (n := n) V) Y₂)
    {Z₁ Z₂ : CMfd.{u} n}
    (Q₁ : BlowupTower (CMfd.of (n := n) (preimageOpens e U)) Z₁)
    (Q₂ : BlowupTower (CMfd.of (n := n) (preimageOpens e V)) Z₂)
    (χ₁ : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} Y₁)
    (χ₂ : Z₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} Y₂)
    (h₁ : IsTowerIso (baseLiftDiffeo e U) Q₁ (liftTower.{u} T₁) χ₁)
    (h₂ : IsTowerIso (baseLiftDiffeo e V) Q₂ (liftTower.{u} T₂) χ₂)
    (θ : CMfd.of (n := n) (openPreimage T₁ (nestedOpens U (U ⊓ V)))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T₂ (nestedOpens V (U ⊓ V))))
    (hθ : EmptyAwareTowerIso
      (overlapBaseEquiv (n := n) (inf_le_left : U ⊓ V ≤ U) (inf_le_right : U ⊓ V ≤ V))
      (restrict (nestedOpens U (U ⊓ V)) T₁) (restrict (nestedOpens V (U ⊓ V)) T₂) θ) :
    let W := U ⊓ V
    let hL : preimageOpens e W ≤ preimageOpens e U := fun _ h => h.1
    let hR : preimageOpens e W ≤ preimageOpens e V := fun _ h => h.2
    ∃ η, EmptyAwareTowerIso (overlapBaseEquiv hL hR)
      (restrict (nestedOpens (preimageOpens e U) (preimageOpens e W)) Q₁)
      (restrict (nestedOpens (preimageOpens e V) (preimageOpens e W)) Q₂) η := by
  obtain ⟨η₁,hr₁⟩ := towerIso_nestedLift_isTowerIso e U (U ⊓ V) T₁ Q₁ χ₁ h₁
  obtain ⟨η₂,hr₂⟩ := towerIso_nestedLift_isTowerIso e V (U ⊓ V) T₂ Q₂ χ₂ h₂
  have h := physical_comparison_of_lifted_small hr₁ hθ hr₂
  have hβ : liftMap.{u} (overlapBaseEquiv (n := n)
      (inf_le_left : U ⊓ V ≤ U) (inf_le_right : U ⊓ V ≤ V)) =
      (((liftDiffeomorph.{u} (CMfd.of (n := n) (nestedOpens U (U ⊓ V)))).symm.trans
        (overlapBaseEquiv (n := n) (inf_le_left : U ⊓ V ≤ U) (inf_le_right : U ⊓ V ≤ V))).trans
        (liftDiffeomorph.{u} (CMfd.of (n := n) (nestedOpens V (U ⊓ V))))) := by
    ext p
    rfl
  rw [hβ, lifted_overlap_base_eq] at h
  exact ⟨_,h⟩

/-- A supplied actual small chart comparison lifts to the literal common open of the two transported towers. -/
theorem lifted_physical_chart_overlap {n : ℕ} {X : CMfd.{u} n} {X₀ Y₁ Y₂ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀) (U V : Opens X₀)
    (T₁ : BlowupTower (CMfd.of (n := n) U) Y₁) (T₂ : BlowupTower (CMfd.of (n := n) V) Y₂)
    (θ : CMfd.of (n := n) (openPreimage T₁ (nestedOpens U (U ⊓ V)))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T₂ (nestedOpens V (U ⊓ V))))
    (hθ : EmptyAwareTowerIso
      (overlapBaseEquiv (n := n) (inf_le_left : U ⊓ V ≤ U) (inf_le_right : U ⊓ V ≤ V))
      (restrict (nestedOpens U (U ⊓ V)) T₁) (restrict (nestedOpens V (U ⊓ V)) T₂) θ) :
    let W := U ⊓ V
    let hL : preimageOpens e W ≤ preimageOpens e U := fun _ h => h.1
    let hR : preimageOpens e W ≤ preimageOpens e V := fun _ h => h.2
    ∃ η, EmptyAwareTowerIso (overlapBaseEquiv hL hR)
      (restrict (nestedOpens (preimageOpens e U) (preimageOpens e W)) (chartTowerTransport e U T₁).tower)
      (restrict (nestedOpens (preimageOpens e V) (preimageOpens e W)) (chartTowerTransport e V T₂).tower) η := by
  exact lifted_physical_overlap_of_isos e U V T₁ T₂
    (chartTowerTransport e U T₁).tower (chartTowerTransport e V T₂).tower
    (chartTowerTransport e U T₁).back (chartTowerTransport e V T₂).back
    (transport_isTowerIso (baseLiftDiffeo e U) (liftTower.{u} T₁))
    (transport_isTowerIso (baseLiftDiffeo e V) (liftTower.{u} T₂)) θ hθ

end
end Hironaka.G3UniversePhysicalChartOverlap
