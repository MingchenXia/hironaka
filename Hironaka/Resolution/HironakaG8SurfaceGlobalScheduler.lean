import Hironaka.Resolution.HironakaG8HereditaryDiscreteScheduler
import Hironaka.Resolution.HironakaG8SurfaceFiniteService
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8SurfaceGlobalScheduler
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG8IntrinsicSingularBlockSchedule
  HironakaG8SurfaceSingularPhase HironakaG8SurfaceFiniteService
  HironakaUniformHistoricalSuccessorOriginalRegular NormalCrossings

/-- Surface analytic sets form a hereditary discrete-singular class. -/
def surfaceHistoryClass : HironakaG8HereditaryDiscreteScheduler.DiscreteHistoryClass 2 where
  holds := fun _ _ => True
  discrete := fun _ _ hV _ => surface_singular_discrete hV
  next := fun _ _ _ _ _ => trivial
  originalTest := fun V hV _ E hE T hT => surface_singular_history_is_original_test V hV E hE T hT

/-- The actual singular points above a compact base task form a finite set. -/
theorem current_singular_over_compact_finite {X Y : CMfd.{0} 2}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W)
    (K : Set X) (hK : IsCompact K) (T : BlowupTower X Y) :
    (singularSet (n := 2) (strictTransform 2 T.proj W) ∩ T.proj ⁻¹' K).Finite :=
  HironakaG8HereditaryDiscreteScheduler.current_singular_over_compact_finite W hW surfaceHistoryClass trivial K hK T trivial

/-- A finite physical block serves the chosen compact base task. -/
theorem surface_compact_task_block {X Y : CMfd.{0} 2}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W)
    (K : Set X) (hK : IsCompact K) (T : BlowupTower X Y) :
    ∃ (Z : CMfd.{0} 2) (S : BlowupTower Y Z),
      StageCentres (fun P C => C ⊆ singularSet (n := 2)
        (strictTransform 2 P.proj (strictTransform 2 T.proj W))) S ∧
      Disjoint (singularSet (n := 2) (strictTransform 2 (T.append S).proj W))
        ((T.append S).proj ⁻¹' K) :=
  HironakaG8HereditaryDiscreteScheduler.hereditary_compact_task_block (by decide) W hW surfaceHistoryClass trivial K hK T trivial

/-- Supplied compact tasks are served by actual singular-centred test blocks. -/
noncomputable def surfaceNext {X : CMfd.{0} 2}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W)
    (K : ℕ → Set X) (hK : ∀ j, IsCompact (K j))
    (j : ℕ) {Y : CMfd.{0} 2} (T : BlowupTower X Y) : Σ Z : CMfd.{0} 2, BlowupTower Y Z :=
  HironakaG8HereditaryDiscreteScheduler.hereditaryNext (by decide) W hW surfaceHistoryClass trivial K hK j T

theorem surfaceNext_spec {X : CMfd.{0} 2}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W)
    (K : ℕ → Set X) (hK : ∀ j, IsCompact (K j))
    (j : ℕ) {Y : CMfd.{0} 2} (T : BlowupTower X Y)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W)) T) :
    StageCentres (fun P C => C ⊆ singularSet (n := 2)
      (strictTransform 2 P.proj (strictTransform 2 T.proj W))) (surfaceNext W hW K hK j T).2 ∧
    Disjoint (singularSet (n := 2) (strictTransform 2 (T.append (surfaceNext W hW K hK j T).2).proj W))
      ((T.append (surfaceNext W hW K hK j T).2).proj ⁻¹' K j) :=
  HironakaG8HereditaryDiscreteScheduler.hereditaryNext_spec (by decide) W hW surfaceHistoryClass trivial K hK j T hStage

/-- Every chosen block tests the actual transformed same original record. -/
theorem surfaceNext_test {X : CMfd.{0} 2}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W)
    (E : List (Set X)) (hE : IsSNCDivisor 2 E)
    (K : ℕ → Set X) (hK : ∀ j, IsCompact (K j))
    (j : ℕ) {Y : CMfd.{0} 2} (T : BlowupTower X Y)
    (hTest : IsGeoTestTower (⟨univ,E,vanishingIdeal (n := 2) W,1⟩ : MarkedIdeal 2 X) T) :
    IsGeoTestTower (geoTransformAlong (⟨univ,E,vanishingIdeal (n := 2) W,1⟩ : MarkedIdeal 2 X) T)
      (surfaceNext W hW K hK j T).2 :=
  HironakaG8HereditaryDiscreteScheduler.hereditaryNext_test (by decide) W hW surfaceHistoryClass trivial E hE K hK j T hTest

/-- Each actual block boundary makes its assigned base window regular. -/
theorem surface_scheduled_sequence_regular {X : CMfd.{0} 2}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W)
    (K : ℕ → Set X) (hK : ∀ j, IsCompact (K j))
    (U : ℕ → Opens X) (hU : ∀ j, (U j : Set X) ⊆ K j)
    (s : ResolutionInvariantSeq.GrowingSeq X)
    (hBoundary : ∀ j, s.stage (HironakaExhaustionBlockLocalFiniteness.blockEndpoints
      (surfaceNext W hW K hK) j).2.length =
      HironakaExhaustionBlockLocalFiniteness.blockEndpoints (surfaceNext W hW K hK) j) :
    ∀ a, ∃ N, Disjoint (singularSet (n := 2) (strictTransform 2 (s.stage N).2.proj W))
      ((s.stage N).2.proj ⁻¹' (U a : Set X)) :=
  HironakaG8HereditaryDiscreteScheduler.hereditary_scheduled_sequence_regular (by decide) W hW surfaceHistoryClass trivial K hK U hU s hBoundary

/-- A compact exhaustion produces actual serving blocks and a finite smooth
endpoint or a locally finite singular-centred original-test history. -/
theorem surface_intrinsic_singular_service_schedule {X : CMfd.{0} 2}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W)
    (E : List (Set X)) (hE : IsSNCDivisor 2 E)
    (K : ℕ → Set X) (hK : ∀ j, IsCompact (K j))
    (U : ℕ → Opens X) (hU : ∀ j, (U j : Set X) ⊆ K j)
    (hcover : ∀ x : X, ∃ j, x ∈ U j) :
    let next := surfaceNext W hW K hK
    (∃ a, (∀ b, a ≤ b → HironakaExhaustionBlockLocalFiniteness.blockEndpoints next b =
          HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a) ∧
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := 2) W,1⟩ : MarkedIdeal 2 X)
        (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a).2 ∧
      StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W))
        (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a).2 ∧
      singularSet (n := 2) (strictTransform 2 (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a).2.proj W) = ∅) ∨
    ∃ s : ResolutionInvariantSeq.GrowingSeq X,
      (∀ j, s.stage (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next j).2.length =
        HironakaExhaustionBlockLocalFiniteness.blockEndpoints next j) ∧
      (∀ i, IsGeoTestTower (⟨univ,E,vanishingIdeal (n := 2) W,1⟩ : MarkedIdeal 2 X) (s.stage i).2) ∧
      (∀ i, StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W)) (s.stage i).2) ∧
      LocallyFinite (HironakaLocallyFiniteResolutionSequence.centreImage s) ∧
      ∀ a, ∃ N, ∀ r, ResolutionInvariantExt.IsEmptyTower
        (restrict (openPreimage (s.stage N).2 (U a))
          (HironakaLocallyFiniteResolutionSequence.tailTower s N r)) :=
  HironakaG8HereditaryDiscreteScheduler.hereditary_intrinsic_singular_service_schedule (by decide) W hW surfaceHistoryClass trivial E hE K hK U hU hcover

/-- Compact exhaustion and its interiors supply all scheduler tasks internally. -/
theorem surface_exists_intrinsic_singular_service_schedule {X : CMfd.{0} 2}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W)
    (E : List (Set X)) (hE : IsSNCDivisor 2 E) :
    ∃ (K : ℕ → Set X) (hK : ∀ j, IsCompact (K j)) (U : ℕ → Opens X),
      (∀ j, (U j : Set X) ⊆ K j) ∧ (∀ x : X, ∃ j, x ∈ U j) ∧
    let next := surfaceNext W hW K hK
    (∃ a, (∀ b, a ≤ b → HironakaExhaustionBlockLocalFiniteness.blockEndpoints next b =
          HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a) ∧
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := 2) W,1⟩ : MarkedIdeal 2 X)
        (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a).2 ∧
      StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W))
        (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a).2 ∧
      singularSet (n := 2) (strictTransform 2 (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a).2.proj W) = ∅) ∨
    ∃ s : ResolutionInvariantSeq.GrowingSeq X,
      (∀ j, s.stage (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next j).2.length =
        HironakaExhaustionBlockLocalFiniteness.blockEndpoints next j) ∧
      (∀ i, IsGeoTestTower (⟨univ,E,vanishingIdeal (n := 2) W,1⟩ : MarkedIdeal 2 X) (s.stage i).2) ∧
      (∀ i, StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W)) (s.stage i).2) ∧
      LocallyFinite (HironakaLocallyFiniteResolutionSequence.centreImage s) ∧
      ∀ a, ∃ N, ∀ r, ResolutionInvariantExt.IsEmptyTower
        (restrict (openPreimage (s.stage N).2 (U a))
          (HironakaLocallyFiniteResolutionSequence.tailTower s N r)) :=
  HironakaG8HereditaryDiscreteScheduler.hereditary_exists_intrinsic_singular_service_schedule
    (by decide) W hW surfaceHistoryClass trivial E hE

end
end Hironaka.HironakaG8SurfaceGlobalScheduler
