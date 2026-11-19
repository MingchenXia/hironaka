import Hironaka.Resolution.HironakaG4ToricDivisorHistory
import Hironaka.Resolution.HironakaG4RebaseDiagonalAction

/-! Construct transverse toric divisor states from a weighted coordinate window. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG4InitialToricDivisors
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupFlatCoordinates NormalCrossings HironakaG34CoordinateScaling HironakaG34ToricCharts
  HironakaG4WeightedGammaParameter HironakaG4CoherentTowerActions HironakaG4UniformScalingDomain
  HironakaG4OptionalBoundaryTransform HironakaG4OptionalDivisorMasks
  HironakaG4LocalToricDivisors HironakaG4RebaseDiagonalAction

variable {n : ℕ} {X : CMfd.{u} n} {x₀ : X}

/-- A weighted window with valid singleton masks provides the strong initial state. -/
theorem initialToricDivisorState_of_weighted_chart {ι : Type v}
    (N : Set X) (D : ι → Set X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    (O : Opens (ComplexModel n)) (hOt : (O : Set (ComplexModel n)) ⊆ Φ.target)
    (s t : Fin n) (c : Fin n → ℕ) (S : Finset (Fin n)) (m : ι → Option (Fin n))
    (hs : s ∈ S) (hst : t ≠ s) (hcs : c s = 0)
    (hN : ∀ y ∈ flatDomain Φ, y ∈ N ↔ flatMap Φ y ∈ coordSubspace S)
    (hD : ∀ i y, y ∈ flatDomain Φ → (y ∈ D i ↔
      flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))))
    (hm : DivisorMasksValid S m)
    (act : weightedScalings s t c → X → X)
    (hAct : CoherentHistory (fun a : weightedScalings s t c => scaleDomain Φ O a)
      (fun a => scaleDomain Φ O (invScale a))
      (fun a => scaleDiffeo hΦsrc hOt a.2.1) (.refl : BlowupTower X X) act)
    {x : X} (hx : x ∈ flatDomain Φ) (hxO : flatMap Φ x ∈ O) :
    LocalToricDivisorState (n := n) (𝓝 (weightedIdentity s t c)) N D x act := by
  let A := weightedScalings s t c
  let F : Filter A := 𝓝 (weightedIdentity s t c)
  let μ : A → Fin n → ℂ := Subtype.val
  have hμ : Tendsto μ F (𝓝 1) := (weightedSection_partial_realization s t c S hs hst hcs).1
  have hmap : Tendsto (fun p : A × X => (μ p.1, p.2)) (F ×ˢ 𝓝 x)
      (𝓝 1 ×ˢ 𝓝 x) := (hμ.comp tendsto_fst).prodMk tendsto_snd
  have hSource := hmap.eventually (eventually_mem_scaleDomain Φ O hx hxO)
  have hscale := hmap.eventually (actsDiagonallyNear_scaleMap hΦsrc hOt hx hxO)
  have hdiag : ActsDiagonallyNear F act μ Φ x := by
    filter_upwards [hSource, hscale] with p hp hd
    have heq := (hAct p.1 p.2 hp).1
    change act p.1 p.2 = scaleMap (Φ := Φ) (μ p.1) p.2 at heq
    rw [heq]
    exact hd
  obtain ⟨Ψ, hΨsrc, hcoords, hdiag'⟩ := exists_rebased_diagonal_chart Φ hx hμ hdiag
  refine ⟨S, μ, weightedSection s t c hst hcs, Ψ, m, hΨsrc, ?_, ?_, hm, hμ, hdiag',
    (weightedSection_partial_realization s t c S hs hst hcs).2⟩
  · intro y hy
    rw [(hcoords y hy).2]
    exact hN y (hcoords y hy).1
  · intro i y hy
    rw [(hcoords y hy).2]
    exact hD i y (hcoords y hy).1

end
end Hironaka.HironakaG4InitialToricDivisors
