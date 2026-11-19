import Hironaka.Resolution.HironakaG4ToricLocalizedTest
import Hironaka.Resolution.HironakaG4LocalizedProtectedWindow

/-! A coherent toric history protects a locally presented slice. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ToricLocalProtectedHistory
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupFlatCoordinates BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism NormalCrossings
  HironakaG34CoordinateScaling HironakaG4WeightedGammaParameter HironakaG4UniformScalingDomain
  HironakaG4CoherentTowerActions HironakaG4ToricLargerCarrierHistory HironakaG4TrackedBoundaryIndex
  HironakaG4ToricLocalizedTest HironakaG4LocalizedProtectedWindow HironakaG4LocalToricDivisors
  HironakaG34LowerCleanupLift

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The coherent toric history protects a slice presented only on the source
window, at an invariant regular centre over that window. -/
theorem protected_window_of_coherent_toric_history
    (P D : MarkedIdeal n X) (hPN : P.N ⊆ D.N)
    (hN : IsClosed D.N) (hE : ∀ H ∈ D.E, IsClosed H)
    (U₀ : Opens X) (hD : (MarkedIdeal.pullback (Subtype.val : U₀ → X) D).IsWellFormed)
    (hmark : D.d = 0) (i : Fin D.E.length) (S : Set X)
    (hSlice : (Subtype.val : U₀ → X) ⁻¹' S =
      (Subtype.val : U₀ → X) ⁻¹' (D.N ∩ D.E.get i))
    {x₀ : X} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    (O : Opens (ComplexModel n)) (hOt : (O : Set (ComplexModel n)) ⊆ Φ.target)
    (hWindow : ∀ x ∈ U₀, x ∈ flatDomain Φ ∧ flatMap Φ x ∈ O)
    (s t : Fin n) (c : Fin n → ℕ) :
    let A := weightedScalings s t c
    let G : Filter A := 𝓝 (weightedIdentity s t c)
    let U : A → Opens X := fun a => scaleDomain Φ O a
    let V : A → Opens X := fun a => scaleDomain Φ O (invScale a)
    let φ := fun a : A => scaleDiffeo hΦsrc hOt a.2.1
    (∀ act : A → X → X, CoherentHistory U V φ (.refl : BlowupTower X X) act →
      ∀ x ∈ D.N, x ∈ flatDomain Φ → flatMap Φ x ∈ O →
        LocalToricDivisorState (n := n) G D.N (fun i : Fin D.E.length => D.E.get i) x act) →
    (T : BlowupTower X Y) → IsGeoTestTower P T →
      ∀ act : A → Y → Y, CoherentHistory U V φ T act →
      ∀ (F : List (Set Y)) (C : Set Y) (x : Y),
        (geoTransformAlong D T).E = strictAlong T (D.E.get i) :: F →
        T.proj x ∈ U₀ → x ∈ C → IsClosed C →
        (∀ K ∈ strictAlong T (D.E.get i) :: F, IsClosed K) →
        C ⊆ strictAlong T D.N → IsComplexAnalyticSubset (n := n) C →
        (∃ k, RegularAtDim (n := n) C x k) →
        (∀ᶠ p in G ×ˢ 𝓝 x, p.2 ∈ C → act p.1 p.2 ∈ C) →
        ProtectedWindowAt (strictAlong T D.N) (strictAlong T S) F C x := by
  dsimp only
  intro hInit T hTest act hHist F C x hBoundary hxU hxC hCclosed hEclosed hCN hCan hreg hpres
  have hlocalTest := localized_enlarged_test_of_coherent_toric_history P D hPN hN hE U₀ hD hmark
    Φ hΦsrc O hOt hWindow s t c hInit T hTest act hHist
  obtain ⟨hxΦ, hxO⟩ := hWindow (T.proj x) hxU
  have hstate := localToricDivisorState_largerCarrier_geoTestTower P D.N
    (fun j : Fin D.E.length => D.E.get j) hPN hN
    (fun j => hE _ (List.get_mem _ j)) Φ hΦsrc O hOt s t c hInit T hTest act hHist
    x (hCN hxC) hxΦ hxO
  have hordered := toric_state_for_ordered_boundary D T (𝓝 (weightedIdentity s t c)) hstate
  rw [hBoundary] at hordered
  obtain ⟨k, hk⟩ := hreg
  exact protected_window_of_local_test_history D U₀ hD T hlocalTest i S hSlice hxU hCclosed
    hEclosed hCN hCan hk hordered hpres

end
end Hironaka.HironakaG4ToricLocalProtectedHistory
