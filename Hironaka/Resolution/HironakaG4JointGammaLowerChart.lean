import Hironaka.Resolution.HironakaG4RestrictFlatChart
import Hironaka.Resolution.HironakaG4LocalLowerDictionary

/-! Shrink a Gamma chart so it also reads the actual local lower carrier. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4JointGammaLowerChart
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupFlatCoordinates NormalCrossings
  HironakaG34CoordinateScaling HironakaG4OptionalBoundaryTransform
  HironakaG4RestrictFlatChart HironakaG4LocalLowerDictionary

variable {n : ℕ} {X : CMfd.{u} n}

/-- A local lower-trace equality can be imposed on the whole domain of a
smaller Gamma chart without changing its coordinate or binomial equations. -/
theorem exists_joint_gamma_lower_chart {x₀ : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (N W H : Set X) (D : List (Set X)) (j : Fin D.length)
    (R₀ : Finset (Fin n)) (m : Fin D.length → Option (Fin n))
    (s t : Fin n) (c : Fin n → ℕ)
    (hxW : x₀ ∈ W) (hW : ∀ᶠ y in 𝓝 x₀, y ∈ W ↔ y ∈ N ∩ D.get j)
    (hN : ∀ y ∈ flatDomain Φ, y ∈ N ↔ flatMap Φ y ∈ coordSubspace R₀)
    (hD : ∀ i y, y ∈ flatDomain Φ → (y ∈ D.get i ↔
      flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))))
    (hH : ∀ y ∈ flatDomain Φ, y ∈ H ↔ binomial s t c (flatMap Φ y) = 0) :
    ∃ (Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
      (R : Finset (Fin n)), Ψ.source ⊆ Φ.source ∧ R₀ ⊆ R ∧
      Ψ.toFun (chartAt (ComplexModel n) x₀ x₀) = Φ.toFun (chartAt (ComplexModel n) x₀ x₀) ∧
      (∀ y ∈ flatDomain Ψ, y ∈ N ↔ flatMap Ψ y ∈ coordSubspace R₀) ∧
      (∀ i y, y ∈ flatDomain Ψ → (y ∈ D.get i ↔
        flatMap Ψ y ∈ optionalCoordLocus ((m i).map (fun k => {k})))) ∧
      (∀ y ∈ flatDomain Ψ, y ∈ H ↔ binomial s t c (flatMap Ψ y) = 0) ∧
      ∀ y ∈ flatDomain Ψ, y ∈ W ↔ flatMap Ψ y ∈ coordSubspace R := by
  have hxD : x₀ ∈ D.get j := ((hW.self_of_nhds).mp hxW).2
  obtain ⟨V,hVsub,hVo,hxV⟩ := mem_nhds_iff.mp hW
  let U : Opens X := ⟨V,hVo⟩
  obtain ⟨Ψ,hsrc,hinside,hmap,hcenter⟩ := exists_flat_chart_inside_open Φ U hxV
  have hN' : ∀ y ∈ flatDomain Ψ, y ∈ N ↔ flatMap Ψ y ∈ coordSubspace R₀ := by
    intro y hy
    rw [(hmap y hy).2]
    exact hN y (hmap y hy).1
  have hD' : ∀ i y, y ∈ flatDomain Ψ → (y ∈ D.get i ↔
      flatMap Ψ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))) := by
    intro i y hy
    rw [(hmap y hy).2]
    exact hD i y (hmap y hy).1
  have hW' : ∀ y ∈ flatDomain Ψ, y ∈ W ↔ y ∈ N ∩ D.get j :=
    fun y hy => hVsub (hinside hy)
  obtain ⟨R,hR,hcoord⟩ := lower_carrier_dictionary_of_local_mask Ψ ⊤ N W D j R₀ m hW' hxD hN' hD'
  refine ⟨Ψ,R,hsrc,hR,hcenter,hN',hD',?_,?_⟩
  · intro y hy
    rw [(hmap y hy).2]
    exact hH y (hmap y hy).1
  · intro y hy
    exact hcoord y hy (by trivial)

end
end Hironaka.HironakaG4JointGammaLowerChart
