import Hironaka.Resolution.HironakaG4TrackedBoundaryIndex
import Hironaka.Resolution.HironakaG4ToricLargerCarrierHistory
import Hironaka.Resolution.HironakaG4ToricCentreNC
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism

/-! Coherent toric states make the same actual tower test the enlarged boundary. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ToricEnlargedTest
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupFlatCoordinates BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings MarkedIdealOpenBiholomorphism
  HironakaG34CoordinateScaling HironakaG4WeightedGammaParameter HironakaG4UniformScalingDomain
  HironakaG4CoherentTowerActions HironakaG4ToricLargerCarrierHistory HironakaG4TrackedBoundaryIndex
  HironakaG4ToricCentreNC HironakaSharpNormalCrossingsOpenLocus
  HironakaG4LocalToricDivisors GermIdealOrder RelativePrincipalizationSpan

variable {n : ℕ} {X : CMfd.{u} n}

/-- If a smaller-carrier test history admits a coherent weighted toric state
for a well-formed zero-marked larger record at all points in the window, then
the very same history is a test tower for the larger record and its boundary. -/
theorem enlarged_test_of_coherent_toric_history
    (P D : MarkedIdeal n X) (hPN : P.N ⊆ D.N) (hD : D.IsWellFormed) (hmark : D.d = 0)
    {x₀ : X} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    (O : Opens (ComplexModel n)) (hOt : (O : Set (ComplexModel n)) ⊆ Φ.target)
    (s t : Fin n) (c : Fin n → ℕ) :
    let A := weightedScalings s t c
    let F : Filter A := 𝓝 (weightedIdentity s t c)
    let U : A → Opens X := fun a => scaleDomain Φ O a
    let V : A → Opens X := fun a => scaleDomain Φ O (invScale a)
    let φ := fun a : A => scaleDiffeo hΦsrc hOt a.2.1
    (∀ act : A → X → X, CoherentHistory U V φ (.refl : BlowupTower X X) act →
      ∀ x ∈ D.N, x ∈ flatDomain Φ → flatMap Φ x ∈ O →
        LocalToricDivisorState (n := n) F D.N (fun i : Fin D.E.length => D.E.get i) x act) →
    (∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower P T →
      ∀ z ∈ strictAlong T D.N, T.proj z ∈ flatDomain Φ ∧ flatMap Φ (T.proj z) ∈ O) →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower P T →
      ∀ act : A → Y → Y, CoherentHistory U V φ T act → IsGeoTestTower D T := by
  dsimp only
  intro hInit hcover Y T
  induction T with
  | refl => intro _ _ _; trivial
  | @step Y Z T C π hπ ih =>
    intro hTest act' hHist'
    obtain ⟨act, hHist, hPres, hStep⟩ := hHist'
    have hprefix : IsGeoTestTower P T := hTest.1
    have hDprefix : IsGeoTestTower D T := ih hprefix act hHist
    refine ⟨hDprefix, hπ.1, ?_, ?_⟩
    · have hCN : C ⊆ strictAlong T D.N := by
        have hc := hTest.2.subset_N
        rw [N_geoTransformAlong] at hc
        exact hc.trans (MemberInterTowerAlong.strictAlong_mono T hPN)
      have hwell := isWellFormed_geoTransformAlong hD T hDprefix
      have hmark' : (geoTransformAlong D T).d = 0 := by simp [hmark, d_geoTransformAlong]
      rw [show (geoTransformAlong D T).cosupp = (geoTransformAlong D T).N by
        change cosupport n (geoTransformAlong D T).N (geoTransformAlong D T).ideal (geoTransformAlong D T).d = _
        rw [hmark', cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hwell.isCoherent hg)]]
      simpa only [N_geoTransformAlong] using hCN
    · intro x hxC
      have hCN : C ⊆ strictAlong T D.N := by
        have hc := hTest.2.subset_N
        rw [N_geoTransformAlong] at hc
        exact hc.trans (MemberInterTowerAlong.strictAlong_mono T hPN)
      have hxN := hCN hxC
      obtain ⟨hxΦ, hxO⟩ := hcover T hprefix x hxN
      have hstate := localToricDivisorState_largerCarrier_geoTestTower P D.N
        (fun i : Fin D.E.length => D.E.get i) hPN hD.isClosedSubmanifold_N.1
        (fun i => hD.isSNCDivisor.1 _ (List.get_mem _ i)) Φ hΦsrc O hOt s t c hInit T hprefix act hHist x hxN hxΦ hxO
      have hordered := toric_state_for_ordered_boundary D T (𝓝 (weightedIdentity s t c)) hstate
      have hμ : Tendsto (Subtype.val : weightedScalings s t c → Fin n → ℂ)
          (𝓝 (weightedIdentity s t c)) (𝓝 1) := continuous_subtype_val.continuousAt
      have hmap : Tendsto (fun p : weightedScalings s t c × Y => ((p.1 : Fin n → ℂ), p.2))
          ((𝓝 (weightedIdentity s t c)) ×ˢ 𝓝 x) (𝓝 1 ×ˢ 𝓝 x) :=
        (hμ.comp tendsto_fst).prodMk tendsto_snd
      have hsource := hmap.eventually (eventually_preimage_mem_scaleDomain Φ O T.proj
        T.contMDiff_proj.continuous.continuousAt hxΦ hxO)
      have hpreserve : ∀ᶠ p in (𝓝 (weightedIdentity s t c)) ×ˢ 𝓝 x,
          p.2 ∈ C → act p.1 p.2 ∈ C := by
        filter_upwards [hsource] with q hq hqC
        exact (hPres q.1 q.2 hq).mpr hqC
      obtain ⟨k, hk⟩ := hπ.1.2 x hxC
      have hCan : IsComplexAnalyticSubset (n := n) C :=
        AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
      exact normalCrossingsAt_of_invariant_toric_state hCN hCan hk hordered hpreserve

end
end Hironaka.HironakaG4ToricEnlargedTest
