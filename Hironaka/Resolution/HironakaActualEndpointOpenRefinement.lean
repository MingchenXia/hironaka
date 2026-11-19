import Hironaka.Resolution.HironakaSharpActualCurveTopologicalGluing

/-! Genuine source-open refinement of an existing actual endpoint-history
family. Native prefix/tail restriction and transport preserve every true
chronological position and construct an actual whole-history isomorphism
with its all-point ambient projection identity. No new comparison map is
supplied; global family comparisons remain a separate construction.

Blueprint: `hironaka-actual-endpoint-open-refinement-20261101.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaActualEndpointOpenRefinement
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism MarkedIdealTowerTransport MaxLocusLocal
  HironakaSharpActualCurveEndpointGeometry HironakaSharpActualCurveTopologicalGluing
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

/-- The SAME actual prefix, restricted and transported from its smaller
ambient base; all original positions, including empty traces, remain. -/
def prefixRefinement (A : ActualEndpointHistories X J) (V : J→Opens X)
    (hV : ∀i,V i≤A.openSet i) (i : J) :
    TowerTransport (CMfd.of (n:=n) (V i))
      (CMfd.of (n:=n) (openPreimage (A.prefixTower i) (nestedOpens (A.openSet i) (V i)))) :=
  transport (nestedOpensDiffeo (n:=n) (hV i)).symm
    (restrict (nestedOpens (A.openSet i) (V i)) (A.prefixTower i))

/-- The SAME actual tail, restricted to the own actual prefix inverse image
and transported through the own prefix endpoint map. -/
def tailRefinement (A : ActualEndpointHistories X J) (V : J→Opens X)
    (hV : ∀i,V i≤A.openSet i) (i : J) :
    TowerTransport (prefixRefinement A V hV i).target
      (CMfd.of (n:=n) (openPreimage (A.tail i)
        (openPreimage (A.prefixTower i) (nestedOpens (A.openSet i) (V i))))) :=
  transport (prefixRefinement A V hV i).back
    (restrict (openPreimage (A.prefixTower i) (nestedOpens (A.openSet i) (V i))) (A.tail i))

theorem prefixRefinement_length (A : ActualEndpointHistories X J) (V : J→Opens X)
    (hV : ∀i,V i≤A.openSet i) (i : J) :
    (prefixRefinement A V hV i).tower.length=(A.prefixTower i).length := by
  simp only [prefixRefinement,length_transport,length_restrict]

theorem tailRefinement_length (A : ActualEndpointHistories X J) (V : J→Opens X)
    (hV : ∀i,V i≤A.openSet i) (i : J) :
    (tailRefinement A V hV i).tower.length=(A.tail i).length := by
  simp only [tailRefinement,length_transport,length_restrict]

/-- The internally produced tail endpoint map compares the WHOLE actual
new history to the SAME original restricted prefix and tail. -/
theorem wholeRefinement_isTowerIso (A : ActualEndpointHistories X J) (V : J→Opens X)
    (hV : ∀i,V i≤A.openSet i) (i : J) :
    IsTowerIso (nestedOpensDiffeo (n:=n) (hV i)).symm
      ((prefixRefinement A V hV i).tower.append (tailRefinement A V hV i).tower)
      ((restrict (nestedOpens (A.openSet i) (V i)) (A.prefixTower i)).append
        (restrict (openPreimage (A.prefixTower i) (nestedOpens (A.openSet i) (V i))) (A.tail i)))
      (tailRefinement A V hV i).back :=
  (transport_isTowerIso _ _).append (transport_isTowerIso _ _)

/-- The actual projection to the original ambient is equal on EVERY own
endpoint point, including points on exceptional divisors and centres. -/
theorem wholeRefinement_projection (A : ActualEndpointHistories X J) (V : J→Opens X)
    (hV : ∀i,V i≤A.openSet i) (i : J) (z : (tailRefinement A V hV i).target) :
    endpointProjection (V i) (prefixRefinement A V hV i).tower (tailRefinement A V hV i).tower z=
      endpointProjection (A.openSet i) (A.prefixTower i) (A.tail i)
        ((tailRefinement A V hV i).back z).val := by
  have hBase (p : V i) :
      ((nestedOpensDiffeo (n:=n) (hV i)).symm p).val.val=p.val:=rfl
  have h:=congrArg (fun p : nestedOpens (A.openSet i) (V i)=>p.val.val)
    ((wholeRefinement_isTowerIso A V hV i).proj_comm z)
  simpa only [endpointProjection,BlowupTower.proj_append,Function.comp_apply,proj_restrict,hBase] using h

end
end Hironaka.HironakaActualEndpointOpenRefinement
