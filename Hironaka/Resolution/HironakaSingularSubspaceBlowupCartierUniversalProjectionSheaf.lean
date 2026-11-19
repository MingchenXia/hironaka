import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalIdealStalk
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartier

/-!
# Actual local sections of the projection's canonical pulled ideal sheaf

The SAME actual projection's canonical ideal sheaf has one genuine section
on an original source open, regular and generating at ALL nearby points.
No actual section, pointwise generator, ideal equality or regularity is input.

Blueprint: `hironaka-singular-subspace-blowup-cartier-universal-projection-sheaf.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSingularSubspaceBlowupCartierUniversalProjectionSheaf

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSingularSubspaceBlowupLift HironakaSingularSubspaceBlowupCartier
  HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf
  HironakaSingularSubspaceBlowupCartierUniversalIdealStalk

noncomputable section

variable {n : ℕ} {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C W : Set M} {π : Y → M}

/-- One ACTUAL canonical ideal-sheaf section on a genuine ORIGINAL source
open has regular generating original germs at ALL nearby original points. -/
theorem exists_local_projection_ideal_sheaf_generator
    (hπ : IsBlowupAlong n C π) (hW : IsClosed W)
    (hdense : W ⊆ closure (W \ C)) (x : strictTransform n π W) :
    ∃ (U : Opens (actualSubspaceLocallyRingedSpace (n := n) (strictTransform n π W)).toTopCat)
      (_hxU : x ∈ U)
      (s : actualPulledCentreSectionIdeal
        (strictTransformProjection hπ hW ≫ actualSubspaceInclusion (n := n) W) C U),
      ∀ (y : strictTransform n π W) (hy : y ∈ U),
        Ideal.map ((strictTransformProjection hπ hW ≫ actualSubspaceInclusion (n := n) W).stalkMap y).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C)
            ((strictTransformProjection hπ hW ≫ actualSubspaceInclusion (n := n) W).base y)) =
          Ideal.span {((actualSubspaceLocallyRingedSpace (n := n) (strictTransform n π W)).presheaf.germ
            U y hy s.val)} ∧
        IsRegular ((actualSubspaceLocallyRingedSpace (n := n) (strictTransform n π W)).presheaf.germ
          U y hy s.val) := by
  obtain ⟨V, hxV, a, ha⟩ := exists_local_projection_cartier_generator hπ hW hdense x
  let X := actualSubspaceLocallyRingedSpace (n := n) (strictTransform n π W)
  let j : X ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) Y :=
    actualSubspaceInclusion (n := n) (strictTransform n π W)
  let p := strictTransformProjection hπ hW
  let H := p ≫ actualSubspaceInclusion (n := n) W
  let U : Opens X.toTopCat := (Opens.map j.base).obj V
  let s₀ : (X.presheaf.obj (op U)).carrier := j.c.app (op V) a
  have hgen : ∀ (y : strictTransform n π W) (hy : y ∈ U),
      Ideal.map (H.stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (H.base y)) =
        Ideal.span {X.presheaf.germ U y hy s₀} ∧ IsRegular (X.presheaf.germ U y hy s₀) := by
    intro y hy
    have hg : X.presheaf.germ U y hy s₀ =
        j.stalkMap y ((actualComplexStructureSheaf (n := n) Y).presheaf.germ V y.val hy a) :=
      (LocallyRingedSpace.stalkMap_germ_apply j V y hy a).symm
    rw [hg]
    have heq := (actualPulledCentreStalkInclusion_range H C y).symm.trans
      (actualPulledCentreStalkInclusion_range_subspace p C y)
    exact ⟨heq.trans (ha y hy).1, (ha y hy).2⟩
  have hs₀ : s₀ ∈ actualPulledCentreSectionIdeal H C U := by
    intro y hy
    rw [(hgen y hy).1]
    exact Ideal.subset_span (Set.mem_singleton _)
  exact ⟨U, hxV, ⟨s₀, hs₀⟩, hgen⟩

end

end Hironaka.HironakaSingularSubspaceBlowupCartierUniversalProjectionSheaf
