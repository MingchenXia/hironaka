import Hironaka.Resolution.HironakaG11TransverseTrace
import Hironaka.Blowup.BlowupTowers

set_option autoImplicit false

/-! At a normal-crossings centre, tangent containment in an incident
member forces the centre germ into that member. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11TangentCentreContainment
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupSpaceTangent NormalCrossings HironakaG11TransverseTrace

/-- If the centre lies in the contact carrier locally and that carrier is
tangent to an incident normal-crossings member, the centre lies in the
member locally. -/
theorem centre_germ_contained_of_tangent
    {n : ℕ} {X : CMfd.{0} n} {C P : Set X} {E : List (Set X)} {x : X}
    (hcross : HasNormalCrossings n C E) (hxC : x ∈ C) (i : Fin E.length)
    (hxH : x ∈ E.get i) (hCP : ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ P)
    (htan : tangentSpace n P x ≤ tangentSpace n (E.get i) x) :
    ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ E.get i := by
  by_contra hnot
  obtain ⟨f,hf,hdef,ξ,hξ,hne⟩ :=
    local_equation_of_normalCrossings_not_containing hcross hxC i hxH hnot
  have hξP : ξ ∈ tangentSpace n P x := by
    apply mem_tangentSpace.mpr
    intro g hg
    have hgC : (vanishingIdeal (n := n) C).mem x g := by
      refine ⟨hg.1,?_⟩
      filter_upwards [hg.2,hCP] with y hy hyCP hyC
      exact hy (hyCP hyC)
    exact (mem_tangentSpace.mp hξ) g hgC
  have hfH : (vanishingIdeal (n := n) (E.get i)).mem x f := by
    refine ⟨hf,?_⟩
    exact hdef.mono fun _ h hH => h.mp hH
  exact hne ((mem_tangentSpace.mp (htan hξP)) f hfH)

end Hironaka.HironakaG11TangentCentreContainment
