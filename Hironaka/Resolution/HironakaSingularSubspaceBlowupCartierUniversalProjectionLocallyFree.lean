import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalProjectionSheaf
import Hironaka.Resolution.HironakaSingularRankOneLocalGenerators

/-!
# The SAME projection ideal sheaf has standard native local-free rank-one data

All genuine source opens and actual ideal sections are produced by geometry.
The native adapter internally constructs unit maps/isomorphisms and existing
LocalGeneratorsData. No local-free data, section, or stalk dictionary is input.

Blueprint: `hironaka-singular-subspace-blowup-cartier-universal-projection-locally-free.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSingularSubspaceBlowupCartierUniversalProjectionLocallyFree

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSingularSubspaceBlowupLift
  HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf
  HironakaSingularSubspaceBlowupCartierUniversalIdealStalk
  HironakaSingularSubspaceBlowupCartierUniversalProjectionSheaf
  HironakaSingularRankOneLocalGenerators

noncomputable section

variable {n : ℕ} {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C W : Set M} {π : Y → M}

private instance originalOverHasWeakSheafify (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat) :
    HasWeakSheafify ((Opens.grothendieckTopology X.toTopCat).over U) AddCommGrpCat.{0} :=
  CategoryTheory.sheafToPresheaf_isRightAdjoint
    ((Opens.grothendieckTopology X.toTopCat).over U) AddCommGrpCat.{0}

/-- Genuine geometric local sections internally produce standard native
local generator data, each actual local generating map ISO and rank ONE. -/
theorem projection_ideal_sheaf_exists_locallyFreeData
    (hπ : IsBlowupAlong n C π) (hW : IsClosed W) (hdense : W ⊆ closure (W \ C)) :
    ∃ q : (actualPulledCentreIdealModule
        (strictTransformProjection hπ hW ≫ actualSubspaceInclusion (n := n) W) C).LocalGeneratorsData.{0},
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (Unique (q.generators i).I) := by
  classical
  let X := actualSubspaceLocallyRingedSpace (n := n) (strictTransform n π W)
  let H := strictTransformProjection hπ hW ≫ actualSubspaceInclusion (n := n) W
  choose U hxU s hs using exists_local_projection_ideal_sheaf_generator hπ hW hdense
  exact exists_locallyFreeData_of_regular_sections X.toSheafedSpace.sheaf
    (actualPulledCentreIdealInclusion H C) (fun _ => Subtype.val_injective)
    U (fun x => ⟨x, hxU x⟩) s
    (fun i x hx => (hs i x hx).2)
    (fun i x hx => (actualPulledCentreStalkInclusion_range H C x).trans (hs i x hx).1)

/-- The SAME actual canonical ideal sheaf has the existing native
IsLocallyFree property; the preceding theorem retains its rank-one data. -/
theorem projection_ideal_sheaf_isLocallyFree
    (hπ : IsBlowupAlong n C π) (hW : IsClosed W) (hdense : W ⊆ closure (W \ C)) :
    (actualPulledCentreIdealModule
      (strictTransformProjection hπ hW ≫ actualSubspaceInclusion (n := n) W) C).IsLocallyFree := by
  obtain ⟨q, hq, _hunique⟩ := projection_ideal_sheaf_exists_locallyFreeData hπ hW hdense
  let : q.IsLocallyFreeData := hq
  exact q.isLocallyFree

end

end Hironaka.HironakaSingularSubspaceBlowupCartierUniversalProjectionLocallyFree
