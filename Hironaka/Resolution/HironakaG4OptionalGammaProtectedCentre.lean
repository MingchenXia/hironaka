import Hironaka.Resolution.HironakaG4ToricLocalProtectedHistory
import Hironaka.Resolution.HironakaG4OptionalCoherentGammaHistory
import Hironaka.Resolution.HironakaG4InitialToricDivisors

/-! A Gamma chart and an equivariant actual step protect the earlier slice. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4OptionalGammaProtectedCentre
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupFlatCoordinates BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism NormalCrossings
  HironakaG34CoordinateScaling HironakaG34MaskFoldEquivariance HironakaG4WeightedGammaParameter
  HironakaG4UniformScalingDomain HironakaG4CoherentTowerActions HironakaG4OptionalCoherentGammaHistory
  HironakaG4OptionalBoundaryTransform HironakaG4OptionalDivisorMasks HironakaG4InitialToricDivisors
  HironakaG4ToricLocalProtectedHistory HironakaG34LowerCleanupLift

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- On a weighted Gamma chart, equivariance of the actual test step gives
the protected-window certificate at every centre point over the chart. -/
theorem optional_gamma_chart_protects_equivariant_test_centre
    (P D : MarkedIdeal n X) (hPN : P.N ⊆ D.N)
    (hNclosed : IsClosed D.N) (hDclosed : ∀ H ∈ D.E, IsClosed H)
    (U₀ : Opens X) (hD : (MarkedIdeal.pullback (Subtype.val : U₀ → X) D).IsWellFormed)
    (hmark : D.d = 0) (i : Fin D.E.length) (S : Set X)
    (hSlice : (Subtype.val : U₀ → X) ⁻¹' S =
      (Subtype.val : U₀ → X) ⁻¹' (D.N ∩ D.E.get i))
    {x₀ : X} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    (O : Opens (ComplexModel n)) (hOt : (O : Set (ComplexModel n)) ⊆ Φ.target)
    (hWindow : ∀ x ∈ U₀, x ∈ flatDomain Φ ∧ flatMap Φ x ∈ O)
    (s t : Fin n) (c : Fin n → ℕ) (R R₀ : Finset (Fin n)) (m : Fin D.E.length → Option (Fin n))
    (hs : s ∈ R₀) (hst : t ≠ s) (hcs : c s = 0)
    (hN : ∀ y ∈ flatDomain Φ, y ∈ D.N ↔ flatMap Φ y ∈ coordSubspace R₀)
    (hDcoords : ∀ j y, y ∈ flatDomain Φ → (y ∈ D.E.get j ↔
      flatMap Φ y ∈ optionalCoordLocus ((m j).map (fun k => {k})))) (hm : DivisorMasksValid R₀ m)
    {W : Set X} {E : List (Set X)}
    (hW : ∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O → (y ∈ W ↔ flatMap Φ y ∈ coordSubspace R))
    (hE : ∀ H ∈ E, (∃ Q : Finset (Fin n), ∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O →
      (y ∈ H ↔ flatMap Φ y ∈ coordSubspace Q)) ∨
      (∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O → (y ∈ H ↔ flatMap Φ y ∈ {w | binomial s t c w = 0})) ∨
      (∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O → y ∉ H))
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower P (.step T C π hπ)) (hEq : IsEquivariant W E (.step T C π hπ))
    (F : List (Set Y)) (hBoundary : (geoTransformAlong D T).E = strictAlong T (D.E.get i) :: F)
    (hEclosed : ∀ K ∈ strictAlong T (D.E.get i) :: F, IsClosed K)
    (x : Y) (hxC : x ∈ C) (hxU : T.proj x ∈ U₀) :
    ProtectedWindowAt (strictAlong T D.N) (strictAlong T S) F C x := by
  obtain ⟨act', hHist', -, -⟩ := exists_optional_coherent_gamma_history (.step T C π hπ) hEq
    Φ hΦsrc O hOt s t c R R₀ hs hst hcs hW hE
  obtain ⟨act, hHist, hPres, hStep⟩ := hHist'
  have hprefix : IsGeoTestTower P T := hTest.1
  have hCN : C ⊆ strictAlong T D.N := by
    have hc := hTest.2.subset_N
    rw [N_geoTransformAlong] at hc
    exact hc.trans (MemberInterTowerAlong.strictAlong_mono T hPN)
  have hCan : IsComplexAnalyticSubset (n := n) C :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
  obtain ⟨k, hk⟩ := hπ.1.2 x hxC
  obtain ⟨hxΦ, hxO⟩ := hWindow (T.proj x) hxU
  have hμ : Tendsto (Subtype.val : weightedScalings s t c → Fin n → ℂ)
      (𝓝 (weightedIdentity s t c)) (𝓝 1) := continuous_subtype_val.continuousAt
  have hmap : Tendsto (fun p : weightedScalings s t c × Y => ((p.1 : Fin n → ℂ), p.2))
      ((𝓝 (weightedIdentity s t c)) ×ˢ 𝓝 x) (𝓝 1 ×ˢ 𝓝 x) :=
    (hμ.comp tendsto_fst).prodMk tendsto_snd
  have hsource := hmap.eventually (eventually_preimage_mem_scaleDomain Φ O T.proj
    T.contMDiff_proj.continuous.continuousAt hxΦ hxO)
  have hpres : ∀ᶠ p in (𝓝 (weightedIdentity s t c)) ×ˢ 𝓝 x,
      p.2 ∈ C → act p.1 p.2 ∈ C := by
    filter_upwards [hsource] with q hq hqC
    exact (hPres q.1 q.2 hq).mpr hqC
  apply protected_window_of_coherent_toric_history P D hPN hNclosed hDclosed U₀ hD hmark i S hSlice
    Φ hΦsrc O hOt hWindow s t c ?_ T hprefix act hHist F C x hBoundary hxU hxC hπ.1.1
      hEclosed hCN hCan ⟨k,hk⟩ hpres
  intro act₀ hAct₀ y hyN hyΦ hyO
  exact initialToricDivisorState_of_weighted_chart D.N (fun j : Fin D.E.length => D.E.get j)
    Φ hΦsrc O hOt s t c R₀ m hs hst hcs hN hDcoords hm act₀ hAct₀ hyΦ hyO

end
end Hironaka.HironakaG4OptionalGammaProtectedCentre
