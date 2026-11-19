import Hironaka.Resolution.HironakaG3UniverseLiftRestrict
import Hironaka.Resolution.HironakaSharpActualCurveComparisonRestriction
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseChartRestriction
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MaxLocusLocal
  HironakaG3UniverseLiftManifold G3UniverseOpenDiffeo G3UniverseChartTowerTransport
  HironakaSharpActualCurveComparisonRestriction

/-- The restricted transported chart uses precisely the literal nested inverse-image open. -/
theorem chart_restricted_open_eq {n : ℕ} {X : CMfd.{u} n} {X₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀) (U W : Opens X₀) :
    preimageOpen (baseLiftDiffeo e U)
      (preimageOpens (liftDiffeomorph.{u} (CMfd.of (n := n) U)).symm (nestedOpens U W)) =
    nestedOpens (preimageOpens e U) (preimageOpens e W) := by
  apply Opens.ext
  rfl
end Hironaka.G3UniverseChartRestriction

namespace Hironaka.G3UniverseChartRestriction
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsoTail MaxLocusLocal
  HironakaG3UniverseLiftManifold G3UniverseOpenDiffeo G3UniverseChartTowerTransport
  HironakaSharpActualCurveComparisonRestriction
noncomputable section

/-- Nested opens are the literal inverse-image opens under the restricted base map. -/
theorem nested_preimage_eq {n : ℕ} {X : CMfd.{u} n} {X₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀) (U W : Opens X₀) :
    nestedOpens (preimageOpens e U) (preimageOpens e W) =
      preimageOpens (preimageDiffeo e U).symm (nestedOpens U W) := by
  apply Opens.ext
  rfl

/-- The actual nested inverse-image base identifies with the lifted small nested open. -/
def nestedLiftBase {n : ℕ} {X : CMfd.{u} n} {X₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀) (U W : Opens X₀) :
    CMfd.of (n := n) (nestedOpens (preimageOpens e U) (preimageOpens e W))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        liftCMfd.{u} (CMfd.of (n := n) (nestedOpens U W)) :=
  (opensCongr (nested_preimage_eq e U W)).trans
    (baseLiftDiffeo (preimageDiffeo e U).symm (nestedOpens U W))

/-- The actual restriction base map, with the source written as the literal nested open. -/
def nestedRestrictedBase {n : ℕ} {X : CMfd.{u} n} {X₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀) (U W : Opens X₀) :
    CMfd.of (n := n) (nestedOpens (preimageOpens e U) (preimageOpens e W))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        liftCMfd.{u} (CMfd.of (n := n) (nestedOpens U W)) :=
  let β := baseLiftDiffeo e U
  let A := preimageOpens (liftDiffeomorph.{u} (CMfd.of (n := n) U)).symm (nestedOpens U W)
  let A' := nestedOpens (preimageOpens e U) (preimageOpens e W)
  let hA : (A' : Set (preimageOpens e U)) = β ⁻¹' (A : Set (liftCMfd.{u} (CMfd.of (n := n) U))) :=
    congrArg (fun O : Opens (preimageOpens e U) => (O : Set (preimageOpens e U))) (chart_restricted_open_eq e U W).symm
  (openRestriction β A' A hA).trans
    (baseLiftDiffeo (liftDiffeomorph.{u} (CMfd.of (n := n) U)).symm (nestedOpens U W))

/-- The restriction and direct inverse-image descriptions induce the same actual base map. -/
theorem nestedRestrictedBase_eq_nestedLiftBase {n : ℕ} {X : CMfd.{u} n} {X₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀) (U W : Opens X₀) :
    nestedRestrictedBase e U W = nestedLiftBase e U W := by
  ext p
  rfl
end
end Hironaka.G3UniverseChartRestriction

namespace Hironaka.G3UniverseChartRestriction
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MaxLocusLocal
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower G3UniverseOpenDiffeo G3UniverseChartTowerTransport
  G3UniverseLiftRestrict HironakaSharpActualCurveComparisonRestriction
noncomputable section

/-- Restrict any actual physical isomorphism to a literal lifted small tower over the nested base. -/
theorem towerIso_nestedLift_isTowerIso {n : ℕ} {X : CMfd.{u} n} {X₀ Y₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀) (U W : Opens X₀)
    (T : BlowupTower (CMfd.of (n := n) U) Y₀) {Z : CMfd.{u} n}
    (Q : BlowupTower (CMfd.of (n := n) (preimageOpens e U)) Z)
    (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} Y₀)
    (hIso : IsTowerIso (baseLiftDiffeo e U) Q (liftTower.{u} T) χ) :
    ∃ η, IsTowerIso (nestedLiftBase e U W)
      (restrict (nestedOpens (preimageOpens e U) (preimageOpens e W)) Q)
      (liftTower.{u} (restrict (nestedOpens U W) T)) η := by
  let β := baseLiftDiffeo e U
  let W₀ := nestedOpens U W
  let A := preimageOpens (liftDiffeomorph.{u} (CMfd.of (n := n) U)).symm W₀
  have hR := IsTowerIso.open_restriction hIso A
  have hL := liftTower_restrict_isTowerIso W₀ T
  have aux (A' : Opens (preimageOpens e U)) (hEq : A' = preimageOpen β A) :
      ∃ η, IsTowerIso
        ((openRestriction β A' A (congrArg (fun O : Opens (preimageOpens e U) => (O : Set (preimageOpens e U))) hEq)).trans
          (baseLiftDiffeo (liftDiffeomorph.{u} (CMfd.of (n := n) U)).symm W₀))
        (restrict A' Q) (liftTower.{u} (restrict W₀ T)) η := by
    subst A'
    exact ⟨_, hR.trans hL⟩
  have h := aux _ (chart_restricted_open_eq e U W).symm
  change ∃ η, IsTowerIso (nestedRestrictedBase e U W)
      (restrict (nestedOpens (preimageOpens e U) (preimageOpens e W)) Q)
      (liftTower.{u} (restrict (nestedOpens U W) T)) η at h
  rw [nestedRestrictedBase_eq_nestedLiftBase] at h
  exact h
end
end Hironaka.G3UniverseChartRestriction
