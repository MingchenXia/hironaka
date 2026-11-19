import Hironaka.Resolution.HironakaG3UniverseChartTowerTransport
import Hironaka.Resolution.HironakaG3RTowerClass
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseLiftedChart
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass
  HironakaG3UniverseLiftManifold G3UniverseOpenDiffeo G3UniverseChartTowerTransport
noncomputable section

/-- Candidate literal actual chart on the conjugated map, retaining the lifted tower. -/
def liftedTowerChart {n : ℕ} {X : CMfd.{u} n} {X₀ Y₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀)
    {P : Y₀ → X₀} {𝒞 : LocalTowerClass X₀} (c : TowerChart 𝒞 Y₀ P) :
    TowerChart (fun _ _ _ => True) (liftCMfd.{u} Y₀)
      (e.symm ∘ P ∘ (liftDiffeomorph.{u} Y₀).symm) := by
  let f := (liftDiffeomorph.{u} Y₀).symm
  let T := chartTowerTransport e c.U c.T
  refine { U := preimageOpens e c.U
           Y := T.target
           T := T.tower
           mem := trivial
           V := preimageOpens f c.V
           V_eq := ?_
           φ := T.back.trans ((liftDiffeomorph.{u} c.Y).symm.trans
             (c.φ.trans (preimageDiffeo f c.V)))
           proj_φ := ?_ }
  · ext y
    change f y ∈ (c.V : Set Y₀) ↔ e (e.symm (P (f y))) ∈ (c.U : Set X₀)
    rw [c.V_eq]
    simp
  · intro z
    apply e.injective
    have h := chartTowerTransport_proj e c.U c.T z
    have h' := congrArg (fun q => (liftDiffeomorph.{u} (CMfd.of (n := n) c.U)).symm q) h
    have hproj : e (((T.tower.proj z : preimageOpens e c.U) : X)) =
        ((c.T.proj ((liftDiffeomorph.{u} c.Y).symm (T.back z)) : c.U) : X₀) := by
      change (liftDiffeomorph.{u} (CMfd.of (n := n) c.U)).symm
          ((liftDiffeomorph.{u} (CMfd.of (n := n) c.U))
            ((preimageDiffeo e c.U).symm (T.tower.proj z))) =
        (liftDiffeomorph.{u} (CMfd.of (n := n) c.U)).symm
          ((liftDiffeomorph.{u} (CMfd.of (n := n) c.U))
            (c.T.proj ((liftDiffeomorph.{u} c.Y).symm (T.back z)))) at h'
      simp only [Diffeomorph.symm_apply_apply] at h'
      exact congrArg Subtype.val h'
    change e (e.symm (P ((liftDiffeomorph.{u} Y₀).symm
      ((liftDiffeomorph.{u} Y₀) (c.φ ((liftDiffeomorph.{u} c.Y).symm (T.back z)) : Y₀))))) =
      e (((T.tower.proj z : preimageOpens e c.U) : X))
    rw [e.apply_symm_apply, Diffeomorph.symm_apply_apply]
    exact (c.proj_φ ((liftDiffeomorph.{u} c.Y).symm (T.back z))).trans hproj.symm
end
end Hironaka.G3UniverseLiftedChart
