import Hironaka.Resolution.HironakaG3CoupledStrictTransform
import Hironaka.Resolution.HironakaG3Nonerasure
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3CoupledNonerasure
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  RestrictEmptyTower HironakaDisjointFiniteControlledHistory HironakaG3CoupledAvoidance
  HironakaG3CoupledStrictTransform HironakaG3Nonerasure HironakaG3ControlledHistorySubsetTransport

/-- An actual ambient tower coupled to an intrinsic tower that avoids a
dense native open cannot erase the target: the conventional ambient strict
transform projects onto the entire original image. -/
theorem coupled_projection_strictTransform_eq {d t : ℕ}
    {X : CMfd.{0} (d+t)} {P Q : CMfd.{0} d} {Y : CMfd.{0} (d+t)}
    {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι : P → X} {M : MarkedIdeal d P} {T : BlowupTower P Q} {A : BlowupTower X Y}
    {η : Q → Y} (h : CoupledHistory N B J ι M T A η) (hι : Topology.IsClosedEmbedding ι)
    (V : Set P) (hV : IsClosed V) (O : Opens P) (hdense : V ⊆ closure (V ∩ O))
    (hAvoid : CentresAvoid O T) : A.proj '' strictTransform (d+t) A.proj (ι '' V) = ι '' V := by
  obtain ⟨_hc,_hr,_hI,_hNorm,_hE,_hTrans,_F,_hF,hproj,_hIdeal,_hBoundary⟩ :=
    endpoint_of_coupledHistory h
  rw [← coupled_strictAlong_eq_conventional h hι V hV O hdense hAvoid,
    ← strictAlong_image_of_coupledHistory h V, image_image]
  change (A.proj ∘ η) '' strictAlong T V = ι '' V
  rw [hproj]
  calc
    (ι ∘ T.proj) '' strictAlong T V = ι '' (T.proj '' strictAlong T V) := by
      simpa only [Function.comp_def] using (Set.image_image ι T.proj (strictAlong T V)).symm
    _ = ι '' V := congrArg (fun S => ι '' S)
      (projection_strictAlong_eq_of_centresAvoid V hV O hdense T hAvoid)

end
end Hironaka.HironakaG3CoupledNonerasure
