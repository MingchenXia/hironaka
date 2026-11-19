import Hironaka.Resolution.HironakaG3CoupledNativeGeometry
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3CoupledAvoidance
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  RestrictEmptyTower HironakaDisjointFiniteControlledHistory HironakaG3ControlledHistorySubsetTransport

/-- Avoidance by the native centres forces avoidance by the actual ambient
centres over the corresponding ambient open. -/
theorem coupled_centresAvoid {d t : ℕ} {X : CMfd.{0} (d+t)} {P Q : CMfd.{0} d} {Y : CMfd.{0} (d+t)}
    {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι : P → X} {M : MarkedIdeal d P} {T : BlowupTower P Q} {U : BlowupTower X Y}
    {η : Q → Y} (h : CoupledHistory N B J ι M T U η) (O : Opens P) (G : Opens X)
    (hOpen : ∀ p, ι p ∈ G ↔ p ∈ O) (hAvoid : CentresAvoid O T) : CentresAvoid G U := by
  induction h with
  | refl _ => trivial
  | @step Q R Y Z T U η η' C C' ρ π hρ hπ hprev hcentre hsquare hEnd ih =>
    refine ⟨ih hAvoid.1,?_⟩
    apply Set.disjoint_left.mpr
    intro y hyC hyG
    rw [hcentre] at hyC
    obtain ⟨q,hq,rfl⟩ := hyC
    apply Set.disjoint_left.mp hAvoid.2 hq
    have hEndPrev := endpoint_of_coupledHistory hprev
    obtain ⟨_hc,_hr,_hI,_hNorm,_hE,_hTrans,_F,_hF,hproj,_hIdeal,_hBoundary⟩ := hEndPrev
    have hh := congrFun hproj q
    change U.proj (η q) = ι (T.proj q) at hh
    apply (hOpen (T.proj q)).mp
    rw [← hh]
    exact hyG

/-- The actual coupled ambient projection is an isomorphism over the
corresponding avoided open. -/
theorem coupled_isIsomorphismOver_of_avoid {d t : ℕ} {X : CMfd.{0} (d+t)} {P Q : CMfd.{0} d} {Y : CMfd.{0} (d+t)}
    {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι : P → X} {M : MarkedIdeal d P} {T : BlowupTower P Q} {U : BlowupTower X Y}
    {η : Q → Y} (h : CoupledHistory N B J ι M T U η) (O : Opens P) (G : Opens X)
    (hOpen : ∀ p, ι p ∈ G ↔ p ∈ O) (hAvoid : CentresAvoid O T) :
    IsIsomorphismOver (d+t) U.proj (G : Set X) := by
  have ha := coupled_centresAvoid h O G hOpen hAvoid
  have hExc := EmbeddedFromResolution.image_exceptionalLocus_subset_compl G U ha
  simpa only [compl_compl] using
    HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset U.isBlowupSequence hExc

end
end Hironaka.HironakaG3CoupledAvoidance
