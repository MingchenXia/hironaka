import Hironaka.Resolution.HironakaG4LocalizedEnlargedTest
import Hironaka.Resolution.HironakaG4BoundaryRestrict
import Hironaka.Resolution.HironakaG4ToricCentreLocalNC
import Hironaka.Resolution.HironakaG4ToricEnlargedTest

/-! Coherent toric states test the enlarged boundary over a local chart. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ToricLocalizedTest
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupFlatCoordinates BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism NormalCrossings
  HironakaG34CoordinateScaling HironakaG4WeightedGammaParameter HironakaG4UniformScalingDomain
  HironakaG4CoherentTowerActions HironakaG4ToricLargerCarrierHistory HironakaG4TrackedBoundaryIndex
  HironakaG4ToricCentreLocalNC HironakaG4BoundaryRestrict HironakaG4LocalizedEnlargedTest
  HironakaG4LocalToricDivisors

variable {n : ℕ} {X : CMfd.{u} n}

/-- A coherent action with initial toric states produces the local boundary
history, and hence the restricted enlarged test, for the same actual tower. -/
theorem localized_enlarged_test_of_coherent_toric_history
    (P D : MarkedIdeal n X) (hPN : P.N ⊆ D.N)
    (hN : IsClosed D.N) (hE : ∀ H ∈ D.E, IsClosed H)
    (U₀ : Opens X) (hD : (MarkedIdeal.pullback (Subtype.val : U₀ → X) D).IsWellFormed)
    (hmark : D.d = 0)
    {x₀ : X} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    (O : Opens (ComplexModel n)) (hOt : (O : Set (ComplexModel n)) ⊆ Φ.target)
    (hWindow : ∀ x ∈ U₀, x ∈ flatDomain Φ ∧ flatMap Φ x ∈ O)
    (s t : Fin n) (c : Fin n → ℕ) :
    let A := weightedScalings s t c
    let F : Filter A := 𝓝 (weightedIdentity s t c)
    let U : A → Opens X := fun a => scaleDomain Φ O a
    let V : A → Opens X := fun a => scaleDomain Φ O (invScale a)
    let φ := fun a : A => scaleDiffeo hΦsrc hOt a.2.1
    (∀ act : A → X → X, CoherentHistory U V φ (.refl : BlowupTower X X) act →
      ∀ x ∈ D.N, x ∈ flatDomain Φ → flatMap Φ x ∈ O →
        LocalToricDivisorState (n := n) F D.N (fun i : Fin D.E.length => D.E.get i) x act) →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower P T →
      ∀ act : A → Y → Y, CoherentHistory U V φ T act →
        IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U₀ → X) D) (restrict U₀ T) := by
  dsimp only
  intro hInit Y T hTest act hHist
  apply restricted_enlarged_test_of_local_nc P D hPN U₀ hD hmark T hTest
  induction T with
  | refl => trivial
  | @step Y Z T C π hπ ih =>
    obtain ⟨act₀, hHist₀, hPres, hStep⟩ := hHist
    have hprefix : IsGeoTestTower P T := hTest.1
    refine ⟨ih hprefix act₀ hHist₀, ?_⟩
    rw [boundary_geoTransformAlong_restrict]
    have hCN : C ⊆ strictAlong T D.N := by
      have hc := hTest.2.subset_N
      rw [N_geoTransformAlong] at hc
      exact hc.trans (MemberInterTowerAlong.strictAlong_mono T hPN)
    have hCan : IsComplexAnalyticSubset (n := n) C :=
      AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
    apply normalCrossings_on_open_of_invariant_toric_states (openPreimage T U₀) hCN hCan hπ.1.2
    · intro x hxC hxU
      obtain ⟨hxΦ, hxO⟩ := hWindow (T.proj x) hxU
      have hstate := localToricDivisorState_largerCarrier_geoTestTower P D.N
        (fun i : Fin D.E.length => D.E.get i) hPN hN
        (fun i => hE _ (List.get_mem _ i)) Φ hΦsrc O hOt s t c hInit T hprefix act₀ hHist₀
        x (hCN hxC) hxΦ hxO
      exact toric_state_for_ordered_boundary D T (𝓝 (weightedIdentity s t c)) hstate
    · intro x hxC hxU
      obtain ⟨hxΦ, hxO⟩ := hWindow (T.proj x) hxU
      have hμ : Tendsto (Subtype.val : weightedScalings s t c → Fin n → ℂ)
          (𝓝 (weightedIdentity s t c)) (𝓝 1) := continuous_subtype_val.continuousAt
      have hmap : Tendsto (fun p : weightedScalings s t c × Y => ((p.1 : Fin n → ℂ), p.2))
          ((𝓝 (weightedIdentity s t c)) ×ˢ 𝓝 x) (𝓝 1 ×ˢ 𝓝 x) :=
        (hμ.comp tendsto_fst).prodMk tendsto_snd
      have hsource := hmap.eventually (eventually_preimage_mem_scaleDomain Φ O T.proj
        T.contMDiff_proj.continuous.continuousAt hxΦ hxO)
      filter_upwards [hsource] with q hq hqC
      exact (hPres q.1 q.2 hq).mpr hqC

end
end Hironaka.HironakaG4ToricLocalizedTest
