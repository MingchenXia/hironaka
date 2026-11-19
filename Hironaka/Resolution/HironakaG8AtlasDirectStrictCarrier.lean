import Hironaka.Resolution.HironakaG8InitialBoundaryAtlasMarkOne
import Hironaka.Resolution.HironakaG3EmptyAwareFullBoundary

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8AtlasDirectStrictCarrier

noncomputable section

open Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic NormalCrossings HironakaG3RTowerClass HironakaG3RPureEmbedded
  HironakaG8NoncompactInitialBoundaryAtlas HironakaG8InitialBoundaryAtlasMarkOne
  HironakaActualSmoothBoundaryCleanup HironakaG3EmptyAwareFullBoundary
  HironakaG3EmptyAwareBornSlots HironakaG4SharpTerminalAtlas
  HironakaSharpActualFiniteChronologicalHistory HironakaG8LocalMixedPhaseAssembly

/-- The all-stage carrier defined from the actual finite charts, viewed as
a subset of the ambient atlas on the given projection. -/
def atlasIteratedStrictCarrier {n : ℕ} {X Z : CMfd.{0} n}
    {K : LocalTowerClass X} {P : Z → X} (W : Set X) : Set Z :=
  ⋃ c : TowerChart K Z P, chartIncl c ''
    strictAlong c.T ((Subtype.val : c.U → X) ⁻¹' W)

/-- The global all-stage atlas carrier equals the direct strict transform
of the very same glued map. -/
theorem atlas_iterated_strictCarrier_eq_direct {n : ℕ} {X Z : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    {C : SmoothTailCertificate n} {P : Z → X}
    (A : IsGluedFrom (initialBoundaryClass C W E) Z P) :
    atlasIteratedStrictCarrier (K := initialBoundaryClass C W E) (P := P) W =
      strictTransform n P W := by
  refine Subset.antisymm ?_ ?_
  · intro z hz
    obtain ⟨c, y, hy, rfl⟩ := Set.mem_iUnion.mp hz
    have h := (initial_boundary_chart_original_markOne hW hE hDense A c).2.1
    rw [h] at hy
    exact hy
  · intro z hz
    obtain ⟨c, hc⟩ := A.2.2.2 (P z)
    let v : c.V := ⟨z, c.mem_V hc⟩
    have hInc : chartIncl c (c.φ.symm v) = z := chartIncl_symm c v
    refine Set.mem_iUnion.mpr ⟨c, c.φ.symm v, ?_, hInc⟩
    rw [(initial_boundary_chart_original_markOne hW hE hDense A c).2.1]
    change chartIncl c (c.φ.symm v) ∈ strictTransform n P W
    rwa [hInc]

/-- In every finite chart the first `E.length` positions of the full raw
boundary are exactly the iterated strict transforms of the incoming list.
Each initial entry occupies its original list position. -/
theorem initial_boundary_chart_incoming_positions {n : ℕ} {X Z : CMfd.{0} n}
    {W : Set X} {E : List (Set X)}
    {C : SmoothTailCertificate n} {P : Z → X}
    (c : TowerChart (initialBoundaryClass C W E) Z P) :
    (fullChartBoundary c E).take E.length =
      E.map (fun H => chartIncl c '' strictAlong c.T ((Subtype.val : c.U → X) ⁻¹' H)) := by
  let G := geometricTemplate (univ : Set X) E
  let G₀ := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : c.U → X) G
  change (((geoTransformAlong G₀ c.T).E).map (chartIncl c '' ·)).take E.length = _
  rw [boundary_decomp, List.map_append]
  have hLen : ((G₀.E.map (strictAlong c.T)).map (chartIncl c '' ·)).length = E.length := by
    simp [G₀, G, MarkedIdealBiholomorphism.MarkedIdeal.pullback, geometricTemplate]
  rw [← hLen, List.take_left]
  simp only [G₀, G, MarkedIdealBiholomorphism.MarkedIdeal.pullback, geometricTemplate,
    List.map_map, Function.comp_def]

end
end Hironaka.HironakaG8AtlasDirectStrictCarrier
