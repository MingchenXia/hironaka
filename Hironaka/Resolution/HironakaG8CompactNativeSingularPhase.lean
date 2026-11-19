import Hironaka.Resolution.HironakaOriginalCompactCosupportGlobalScheduler
import Hironaka.Resolution.HironakaG8NativeHSOriginalInequivalence
import Hironaka.Resolution.HironakaG8HSTowerStateStrictTransform
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8CompactNativeSingularPhase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance HironakaStageCenters
  HironakaG11PresLineState HironakaG11PresTowerState HomogenizedGlueingTower
  HironakaOriginalCompactCosupportGlobalScheduler HironakaG8NativeHSOriginalTestBridge
  HironakaG8NativeHSStageCentres HironakaG8HSTowerStateStrictTransform
  HironakaG8NativeHSOriginalInequivalence
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- A global native HS record with compact cosupport yields an actual
finite singular-centred phase on its full initial boundary. The native
canonical resolution strictly lowers the profile on the actual strict transform. -/
theorem compact_native_record_global_singular_phase_with_boundary {n k : ℕ} (hn : 0<n)
    {X : CMfd.{0} n} {W : Set X} {H : ℕ → ℕ} (Q : MarkedIdeal n X)
    (hQ : IsInvDomain k Q)
    (hS : NativeHSState Q W H) (hK : IsCompact Q.cosupp) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      IsCanonical Q ((CanonicalCentres.invFamily hn k).inv Q) T ∧ IsGeoResolution Q T ∧
      IsGeoTestTower (⟨univ,Q.E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T ∧
      ∀ y : Y, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) y ℓ ≤ H ℓ) ∧
        ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) y ℓ < H ℓ := by
  have hW := hS.2.1
  obtain ⟨Y,T,hCan,hRes⟩ := exists_original_compact_cosupport_terminal_tower hn k Q hQ hK
  have hTest := hs_state_test_is_original_test Q hW hS.hsTowerState T hRes.1
  have hCent := hs_tower_stage_centres_singular Q hW.isClosed hS.hsTowerState T hRes.1
  refine ⟨Y,T,hCan,hRes,hTest,hCent,?_⟩
  intro y
  have hs := hS.hsTowerState T hRes.1
  have heq := hsTowerState_strictAlong_eq_strictTransform Q hW.isClosed hS.hsTowerState T hRes.1
  rw [← heq]
  refine ⟨hs.2.2.1 y, ?_⟩
  have hne : ¬ ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictAlong T W)) y ℓ = H ℓ := by
    intro he
    have hc := (hs.2.2.2.1 y).mpr he
    rw [hRes.2] at hc
    exact hc
  obtain ⟨ℓ,hℓ⟩ := not_forall.mp hne
  exact ⟨ℓ,lt_of_le_of_ne (hs.2.2.1 y ℓ) hℓ⟩

/-- A genuinely global native HS record with compact cosupport yields one
actual finite singular-centred global canonical phase and strictly lowers its
profile everywhere. The original record is tested, not asserted canonical. -/
theorem compact_native_record_global_singular_phase {n k : ℕ} (hn : 0<n)
    {X : CMfd.{0} n} {W : Set X} {H : ℕ → ℕ} (Q : MarkedIdeal n X)
    (hQ : IsInvDomain k Q) (hE : Q.E = [])
    (hS : NativeHSState Q W H) (hK : IsCompact Q.cosupp) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      IsCanonical Q ((CanonicalCentres.invFamily hn k).inv Q) T ∧ IsGeoResolution Q T ∧
      IsGeoTestTower (⟨univ,[],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T ∧
      ∀ y : Y, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) y ℓ ≤ H ℓ) ∧
        ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) y ℓ < H ℓ := by
  simpa only [hE] using compact_native_record_global_singular_phase_with_boundary hn Q hQ hS hK

/-- A compact singular locus already gives compact native cosupport, even
when the ambient analytic carrier is noncompact. -/
theorem compact_singular_native_record_global_singular_phase {n k : ℕ} (hn : 0<n)
    {X : CMfd.{0} n} {W : Set X} {H : ℕ → ℕ} (Q : MarkedIdeal n X)
    (hQ : IsInvDomain k Q) (hE : Q.E = []) (hS : NativeHSState Q W H)
    (hSingcompact : IsCompact (singularSet (n := n) W)) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      IsCanonical Q ((CanonicalCentres.invFamily hn k).inv Q) T ∧ IsGeoResolution Q T ∧
      IsGeoTestTower (⟨univ,[],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T ∧
      ∀ y : Y, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) y ℓ ≤ H ℓ) ∧
        ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) y ℓ < H ℓ := by
  have hclosed : IsClosed Q.cosupp :=
    GiraudAlong.isClosed_cosupport_along hQ.isWellFormed.isCoherent hQ.isWellFormed.isClosedSubmanifold_N Q.d
  exact compact_native_record_global_singular_phase hn Q hQ hE hS
    (hSingcompact.of_isClosed_subset hclosed (native_hs_cosupp_subset_singular Q hS))

/-- Compactness of the analytic carrier supplies compactness of the actual
native cosupport; no extra compact-cosupport hypothesis is needed. -/
theorem compact_carrier_native_record_global_singular_phase {n k : ℕ} (hn : 0<n)
    {X : CMfd.{0} n} {W : Set X} {H : ℕ → ℕ} (Q : MarkedIdeal n X)
    (hQ : IsInvDomain k Q) (hE : Q.E = []) (hS : NativeHSState Q W H)
    (hWcompact : IsCompact W) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      IsCanonical Q ((CanonicalCentres.invFamily hn k).inv Q) T ∧ IsGeoResolution Q T ∧
      IsGeoTestTower (⟨univ,[],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T ∧
      ∀ y : Y, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) y ℓ ≤ H ℓ) ∧
        ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) y ℓ < H ℓ := by
  exact compact_singular_native_record_global_singular_phase hn Q hQ hE hS
    (hWcompact.of_isClosed_subset (isClosed_singularSet hS.2.1.isClosed) (singularSet_subset W))
end
end Hironaka.HironakaG8CompactNativeSingularPhase
