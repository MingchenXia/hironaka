import Hironaka.Resolution.HironakaActualCoreHistoricalLowerGeometry
import Hironaka.Resolution.HironakaUniformHistoricalSuccessorOriginalRegular
import Hironaka.Resolution.HironakaG11InvBMMaskStep
import Hironaka.Resolution.HironakaG3RTaskSchedule
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8IntrinsicSingularBlockSchedule
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal HironakaEmbeddedAnalytic HironakaStageCenters RestrictEmptyTower
  HironakaActualHistoricalNativeGivenTower HironakaUniformHistoricalSuccessorOriginalRegular
  HironakaG11InvBMMaskStep

/-- The two literal intrinsic singular-centre predicates encode the same
actual tower. -/
theorem intrinsic_stage_native_history {n : ℕ} {X : CMfd.{0} n} (W : Set X) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
        ActualHistoricalNativeTowerCentres W T
  | _, .refl, _ => trivial
  | _, .step T _ _ _, h => ⟨intrinsic_stage_native_history W T h.1,h.2⟩

/-- Served regular opens remain untouched by all intrinsically singular-centred
continuations. -/
theorem intrinsic_singular_history_avoids_regular_open {n : ℕ} {X Y : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) (O : Opens X)
    (hO : Disjoint (singularSet (n := n) W) (O : Set X))
    (T : BlowupTower X Y)
    (hstage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    CentresAvoid O T := by
  let V : Opens X := ⟨(singularSet (n := n) W)ᶜ, (isClosed_singularSet hW.isClosed).isOpen_compl⟩
  have hOV : O ≤ V := by
    intro x hx hs
    exact disjoint_left.mp hO hs hx
  have hp := actual_singular_history_original_regular_protection W hW T (intrinsic_stage_native_history W T hstage)
  exact centresAvoid_mono hOV T hp.1

/-- Regularity over an open persists along any intrinsically singular-centred
history, on the same strict transforms and projection. -/
theorem intrinsic_singular_disjoint_persists {n : ℕ} {X Y : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) (K : Set X)
    (hreg : Disjoint (singularSet (n := n) W) K)
    (T : BlowupTower X Y)
    (hstage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    Disjoint (singularSet (n := n) (strictTransform n T.proj W)) (T.proj ⁻¹' K) := by
  have hp := actual_singular_history_original_regular_protection W hW T (intrinsic_stage_native_history W T hstage)
  exact disjoint_left.mpr (fun _ hy hU => disjoint_left.mp hreg (hp.2.2.2.2.2.1 hy) hU)

/-- Concatenating actual singular-centred histories preserves their literal
positions relative to the original analytic set. -/
theorem intrinsic_stage_append {n : ℕ} {X Y Z : CMfd.{0} n}
    (W : Set X) (T : BlowupTower X Y) (S : BlowupTower Y Z)
    (hT : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T)
    (hS : StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj (strictTransform n T.proj W))) S) :
    StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) (T.append S) := by
  induction S with
  | refl => exact hT
  | @step A B S C π hπ ih =>
      refine ⟨ih hS.1, ?_⟩
      have heq := StrictTransformComposition.strictTransform_comp T.contMDiff_proj S.contMDiff_proj W
      rw [← BlowupTower.proj_append] at heq
      dsimp only
      rw [heq]
      exact hS.2

open ResolutionInvariantSpec (countCentresMeeting)

/-- A tower avoiding an open has no centre meeting it. -/
theorem countCentresMeeting_eq_zero_of_avoids {n : ℕ} {X : CMfd.{0} n} (U : Opens X) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), CentresAvoid U T →
      countCentresMeeting (U : Set X) T = 0
  | _, .refl, _ => rfl
  | _, .step T C _ _, h => by
      have hn : ¬ (C ∩ T.proj ⁻¹' (U : Set X)).Nonempty := by
        rintro ⟨x,hxC,hxU⟩
        exact disjoint_left.mp h.2 hxC hxU
      change countCentresMeeting (U : Set X) T +
        (if (C ∩ T.proj ⁻¹' (U : Set X)).Nonempty then 1 else 0) = 0
      rw [countCentresMeeting_eq_zero_of_avoids U T h.1, if_neg hn]

/-- Once a base open is regular in the current actual strict transform, a
singular-centred continuation cannot increase its centre count. -/
theorem count_append_eq_of_current_regular_open {n : ℕ} {X Y Z : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) (U : Opens X)
    (T : BlowupTower X Y) (S : BlowupTower Y Z)
    (hreg : Disjoint (singularSet (n := n) (strictTransform n T.proj W))
      (T.proj ⁻¹' (U : Set X)))
    (hstage : StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj (strictTransform n T.proj W))) S) :
    countCentresMeeting (U : Set X) (T.append S) = countCentresMeeting (U : Set X) T := by
  let V := openPreimage T U
  have hWT := HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform T.isBlowupSequence hW
  have havoid : CentresAvoid V S := intrinsic_singular_history_avoids_regular_open hWT V hreg S hstage
  rw [TowerPreimageCompact.countCentresMeeting_append]
  change countCentresMeeting (U : Set X) T + countCentresMeeting (V : Set Y) S = _
  rw [countCentresMeeting_eq_zero_of_avoids V S havoid, Nat.add_zero]

open HironakaExhaustionBlockLocalFiniteness

/-- The exhaustion block selection preserves all actual intrinsic singular
positions if each supplied block has the property for its current carrier. -/
theorem blockEndpoints_intrinsic_singular {n : ℕ} {X : CMfd.{0} n} (W : Set X)
    (next : ∀ (_j : ℕ) {Y : CMfd.{0} n}, BlowupTower X Y → Σ Z : CMfd.{0} n, BlowupTower Y Z)
    (hnext : ∀ (j : ℕ) {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj (strictTransform n T.proj W))) (next j T).2) :
    ∀ j, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
      (blockEndpoints next j).2
  | 0 => trivial
  | j+1 => intrinsic_stage_append W (blockEndpoints next j).2 (next j (blockEndpoints next j).2).2
      (blockEndpoints_intrinsic_singular W next hnext j)
      (hnext j _ (blockEndpoints_intrinsic_singular W next hnext j))

/-- Once an exhaustion block serves its task, every later singular-centred
block leaves that task regular. -/
theorem blockEndpoints_intrinsic_regular_persists {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (K : ℕ → Set X)
    (next : ∀ (_j : ℕ) {Y : CMfd.{0} n}, BlowupTower X Y → Σ Z : CMfd.{0} n, BlowupTower Y Z)
    (hnext : ∀ (j : ℕ) {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj (strictTransform n T.proj W))) (next j T).2)
    (hserve : ∀ (j : ℕ) {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      Disjoint (singularSet (n := n) (strictTransform n (T.append (next j T).2).proj W))
        ((T.append (next j T).2).proj ⁻¹' K j))
    (a b : ℕ) (hab : a+1 ≤ b) :
    Disjoint (singularSet (n := n) (strictTransform n (blockEndpoints next b).2.proj W))
      ((blockEndpoints next b).2.proj ⁻¹' K a) := by
  induction b, hab using Nat.le_induction with
  | base => exact hserve a (blockEndpoints next a).2 (blockEndpoints_intrinsic_singular W next hnext a)
  | succ b _ ih =>
      let T := (blockEndpoints next b).2
      let S := (next b T).2
      have hWT := HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform T.isBlowupSequence hW
      have hSing := hnext b T (blockEndpoints_intrinsic_singular W next hnext b)
      have hp := intrinsic_singular_disjoint_persists hWT (T.proj ⁻¹' K a) ih S hSing
      rw [← StrictTransformComposition.strictTransform_comp T.contMDiff_proj S.contMDiff_proj W,
        ← BlowupTower.proj_append] at hp
      change Disjoint (singularSet (n := n) (strictTransform n (T.append S).proj W))
        ((T.append S).proj ⁻¹' K a)
      simpa only [BlowupTower.proj_append, preimage_comp] using hp


section Schedule
variable {n : ℕ} {X : CMfd.{0} n} (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
  (K : ℕ → Set X)
  (next : ∀ (_j : ℕ) {Y : CMfd.{0} n}, BlowupTower X Y → Σ Z : CMfd.{0} n, BlowupTower Y Z)
  (hnext : ∀ (j : ℕ) {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj (strictTransform n T.proj W))) (next j T).2)
  (hserve : ∀ (j : ℕ) {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      Disjoint (singularSet (n := n) (strictTransform n (T.append (next j T).2).proj W))
        ((T.append (next j T).2).proj ⁻¹' K j))
include hW hnext hserve

/-- A served open has a fixed actual centre count at all later block endpoints. -/
theorem blockEndpoints_count_constant (a b : ℕ) (hab : a+1 ≤ b)
    (U : Opens X) (hU : (U : Set X) ⊆ K a) :
    countCentresMeeting (U : Set X) (blockEndpoints next b).2 =
      countCentresMeeting (U : Set X) (blockEndpoints next (a+1)).2 := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      let T := (blockEndpoints next b).2
      let S := (next b T).2
      have hreg := blockEndpoints_intrinsic_regular_persists W hW K next hnext hserve a b hab
      have hreg' : Disjoint (singularSet (n := n) (strictTransform n T.proj W))
          (T.proj ⁻¹' (U : Set X)) := hreg.mono_right (preimage_mono hU)
      have heq := count_append_eq_of_current_regular_open hW U T S hreg'
        (hnext b T (blockEndpoints_intrinsic_singular W next hnext b))
      change countCentresMeeting (U : Set X) (T.append S) = _
      rw [heq]
      exact ih

/-- Every served open has a uniform finite bound on all block-endpoint
centre counts. -/
theorem blockEndpoints_intrinsic_count_bound (U : ℕ → Opens X)
    (hU : ∀ a, (U a : Set X) ⊆ K a) :
    ∀ a, ∃ m, ∀ j, countCentresMeeting (U a : Set X) (blockEndpoints next j).2 ≤ m := by
  intro a
  refine ⟨countCentresMeeting (U a : Set X) (blockEndpoints next (a+1)).2, fun j => ?_⟩
  rcases le_total j (a+1) with hj | hj
  · obtain ⟨S,hS⟩ := HironakaG3RTaskSchedule.blockEndpoints_prefix next j (a+1) hj
    rw [hS, TowerPreimageCompact.countCentresMeeting_append]
    exact Nat.le_add_right _ _
  · exact (blockEndpoints_count_constant W hW K next hnext hserve a j hj (U a) (hU a)).le


/-- Serving a countable cover by finite actual blocks produces either a finite
smooth endpoint or a locally finite actual singular-centred test sequence.
Existence of the individual serving blocks remains a hypothesis. -/
theorem intrinsic_singular_service_schedule
    (M : MarkedIdeal n X)
    (htest : ∀ (j : ℕ) {Y : CMfd.{0} n} (T : BlowupTower X Y),
      IsGeoTestTower M T → IsGeoTestTower (geoTransformAlong M T) (next j T).2)
    (U : ℕ → Opens X) (hU : ∀ a, (U a : Set X) ⊆ K a)
    (hcover : ∀ x : X, ∃ a, x ∈ U a) :
    (∃ a, (∀ b, a ≤ b → blockEndpoints next b = blockEndpoints next a) ∧
      IsGeoTestTower M (blockEndpoints next a).2 ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
        (blockEndpoints next a).2 ∧
      singularSet (n := n) (strictTransform n (blockEndpoints next a).2.proj W) = ∅) ∨
    ∃ s : ResolutionInvariantSeq.GrowingSeq X,
      (∀ j, s.stage (blockEndpoints next j).2.length = blockEndpoints next j) ∧
      (∀ i, IsGeoTestTower M (s.stage i).2) ∧
      (∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
        (s.stage i).2) ∧
      LocallyFinite (HironakaLocallyFiniteResolutionSequence.centreImage s) ∧
      ∀ a, ∃ N, ∀ r, ResolutionInvariantExt.IsEmptyTower
        (restrict (openPreimage (s.stage N).2 (U a))
          (HironakaLocallyFiniteResolutionSequence.tailTower s N r)) := by
  let B := blockEndpoints next
  have hB := blockEndpoints_extend next
  have hbound := blockEndpoints_intrinsic_count_bound W hW K next hnext hserve U hU
  have hst (j) := blockEndpoints_intrinsic_singular W next hnext j
  have hbt := isGeoTestTower_blockEndpoints next M htest
  rcases HironakaCountableTowerPrefixes.unbounded_or_eventually_constant B hB with hUnbounded | hFinite
  · let s := HironakaCountableTowerPrefixes.sequenceOfBlocks B hB hUnbounded
    refine Or.inr ⟨s, HironakaCountableTowerPrefixes.sequenceOfBlocks_boundary B hB hUnbounded,
      HironakaCountableTowerPrefixes.isGeoTestTower_sequenceOfBlocks B hB hUnbounded M hbt, ?_,
      locallyFinite_sequenceOfBlocks B hB hUnbounded U hbound hcover,
      sequenceOfBlocks_empty_tails B hB hUnbounded U hbound⟩
    intro i
    obtain ⟨j,hj⟩ := hUnbounded i
    rw [HironakaCountableTowerPrefixes.sequenceOfBlocks_stage B hB hUnbounded hj]
    change StageCentres _ (BlowupTowerSplit.head (B j).2 ((B j).2.length-i))
    apply HironakaActualCoreHistoricalLowerGeometry.stage_centres_prefix _ _
      (BlowupTowerSplit.tail (B j).2 ((B j).2.length-i))
    rw [BlowupTowerSplit.head_append_tail]
    exact hst j
  · obtain ⟨a,ha⟩ := hFinite
    refine Or.inl ⟨a,ha,hbt a,hst a,?_⟩
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨c,hc⟩ := hcover ((B a).2.proj y)
    have hr := blockEndpoints_intrinsic_regular_persists W hW K next hnext hserve c (max a (c+1))
      (le_max_right _ _)
    change Disjoint (singularSet (n := n) (strictTransform n (B (max a (c+1))).2.proj W))
      ((B (max a (c+1))).2.proj ⁻¹' K c) at hr
    rw [ha _ (le_max_left _ _)] at hr
    exact disjoint_left.mp hr hy (hU c hc)

end Schedule
end
end Hironaka.HironakaG8IntrinsicSingularBlockSchedule
