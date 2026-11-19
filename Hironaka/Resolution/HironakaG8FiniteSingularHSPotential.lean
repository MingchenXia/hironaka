import Hironaka.Resolution.HironakaG8IntrinsicSingularBlockSchedule
import Hironaka.Resolution.HironakaActualHilbertSamuelWellFounded
import Mathlib.Data.Multiset.DershowitzManna
import Hironaka.Resolution.HironakaG8FiniteIsolatedProfilePhase
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8FiniteSingularHSPotential
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HironakaEmbeddedAnalytic HironakaStageCenters
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci HironakaActualHilbertSamuelWellFounded
  HironakaUniformHistoricalSuccessorOriginalRegular HironakaG8IntrinsicSingularBlockSchedule
  HironakaG8FiniteIsolatedProfilePhase MarkedIdeals MarkedIdeals.MarkedIdeal

/-- Every actual analytic point has a genuinely realizable entire HS profile. -/
def actualHSProfile {n : ℕ} {X : CMfd.{0} n} (W : Set X) (x : X) : ActualHilbertSamuelProfile n :=
  ⟨hilbertSamuelAt (vanishingIdeal (n := n) W) x,
    analytic_hilbertSamuel_realizable (wholeChartStalkIdeal (vanishingIdeal (n := n) W) x x
      (mem_chart_source (ComplexModel n) x))⟩

/-- Actual HS profiles, counted with multiplicity over a finite carrier. -/
def finiteHSProfiles {n : ℕ} {X : CMfd.{0} n} (W F : Set X) (hF : F.Finite) :
    Multiset (ActualHilbertSamuelProfile n) := hF.toFinset.val.map (actualHSProfile W)

/-- A strict parent profile for every new point decreases the entire finite multiset. -/
theorem finiteHSProfiles_descent {n : ℕ} {X Y : CMfd.{0} n} (W : Set X) (V : Set Y)
    (F : Set X) (G : Set Y) (hF : F.Finite) (hG : G.Finite) (hNe : F.Nonempty)
    (p : Y → X) (hParent : MapsTo p G F)
    (hDrop : ∀ y ∈ G,
      (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) V) y ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (p y) ℓ) ∧
      ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) V) y ℓ <
        hilbertSamuelAt (vanishingIdeal (n := n) W) (p y) ℓ) :
    Multiset.IsDershowitzMannaLT (finiteHSProfiles V G hG) (finiteHSProfiles W F hF) := by
  have hOldMS : finiteHSProfiles W F hF ≠ 0 := by
    obtain ⟨x,hx⟩ := hNe
    have hxM : actualHSProfile W x ∈ finiteHSProfiles W F hF := by
      apply Multiset.mem_map.mpr
      exact ⟨x,by simpa using hx,rfl⟩
    intro he
    rw [he] at hxM
    exact Multiset.notMem_zero _ hxM
  refine ⟨0,finiteHSProfiles V G hG,finiteHSProfiles W F hF,hOldMS,by simp,by simp,?_⟩
  intro v hv
  obtain ⟨y,hy,rfl⟩ := Multiset.mem_map.mp hv
  have hyG : y ∈ G := by simpa using hy
  refine ⟨actualHSProfile W (p y),?_,?_⟩
  · apply Multiset.mem_map.mpr
    exact ⟨p y,by simpa using hParent hyG,rfl⟩
  · obtain ⟨hle,ℓ,hlt⟩ := hDrop y hyG
    have hle' : actualHSProfile V y ≤ actualHSProfile W (p y) := hle
    have hne' : actualHSProfile V y ≠ actualHSProfile W (p y) := by
      intro he
      exact (Nat.ne_of_lt hlt) (congrFun (congrArg Subtype.val he) ℓ)
    exact lt_of_le_of_ne hle' hne'

/-- Finite singular points counted with multiplicity of their actual profiles. -/
def singularHSProfiles {n : ℕ} {X : CMfd.{0} n} (W : Set X)
    (hfin : (singularSet (n := n) W).Finite) : Multiset (ActualHilbertSamuelProfile n) :=
  finiteHSProfiles W (singularSet (n := n) W) hfin

/-- A singular-centred finite phase that strictly lowers every surviving
singular profile strictly decreases the actual finite multiset potential. -/
theorem finite_singular_HS_multiset_descent {n : ℕ} {X Y : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (T : BlowupTower X Y)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T)
    (hOld : (singularSet (n := n) W).Finite)
    (hNew : (singularSet (n := n) (strictTransform n T.proj W)).Finite)
    (hNe : (singularSet (n := n) W).Nonempty)
    (hDrop : ∀ y ∈ singularSet (n := n) (strictTransform n T.proj W),
      (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) y ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (T.proj y) ℓ) ∧
      ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) y ℓ <
        hilbertSamuelAt (vanishingIdeal (n := n) W) (T.proj y) ℓ) :
    Multiset.IsDershowitzMannaLT
      (singularHSProfiles (strictTransform n T.proj W) hNew) (singularHSProfiles W hOld) := by
  have hSub := (actual_singular_history_original_regular_protection W hW T
    (intrinsic_stage_native_history W T hStage)).2.2.2.2.2.1
  exact finiteHSProfiles_descent W (strictTransform n T.proj W)
    (singularSet (n := n) W) (singularSet (n := n) (strictTransform n T.proj W))
    hOld hNew hNe T.proj hSub hDrop

/-- Properness and singular-centre protection make the actual current
singular locus compact; discreteness then makes it finite. -/
theorem current_singular_compact_finite {n : ℕ} {X Y : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact (singularSet (n := n) W)) (T : BlowupTower X Y)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T)
    [DiscreteTopology (singularSet (n := n) (strictTransform n T.proj W))] :
    IsCompact (singularSet (n := n) (strictTransform n T.proj W)) ∧
      (singularSet (n := n) (strictTransform n T.proj W)).Finite := by
  have hp := actual_singular_history_original_regular_protection W hW T
    (intrinsic_stage_native_history W T hStage)
  have hCurrent := hp.2.2.2.1
  have hProper := hp.2.2.1
  have hSub := hp.2.2.2.2.2.1
  have hCompact := (hProper.isCompact_preimage hK).of_isClosed_subset
    (isClosed_singularSet hCurrent.isClosed) hSub
  exact ⟨hCompact,hCompact.finite (isDiscrete_iff_discreteTopology.mpr inferInstance)⟩
/-- A compact discrete singular locus admits a genuine singular-centred test
phase decreasing its multiset, provided its final singular locus is discrete. -/
theorem discrete_singular_global_phase_multiset_descent {n : ℕ} (hn : 0<n)
    {X : CMfd.{0} n} (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact (singularSet (n := n) W))
    [DiscreteTopology (singularSet (n := n) W)]
    (hNe : (singularSet (n := n) W).Nonempty)
    (hPersist : ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      DiscreteTopology (singularSet (n := n) (strictTransform n T.proj W))) :
    ∃ (hOld : (singularSet (n := n) W).Finite) (Y : CMfd.{0} n) (Q : BlowupTower X Y)
      (hNew : (singularSet (n := n) (strictTransform n Q.proj W)).Finite),
      IsGeoTestTower (⟨univ,[],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) Q ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) Q ∧
      (∀ y ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (Q.proj y) ℓ) ∧
      Multiset.IsDershowitzMannaLT (singularHSProfiles (strictTransform n Q.proj W) hNew)
        (singularHSProfiles W hOld) := by
  have hOld : (singularSet (n := n) W).Finite :=
    hK.finite (isDiscrete_iff_discreteTopology.mpr inferInstance)
  let : Fintype (singularSet (n := n) W) := hOld.fintype
  let a : (singularSet (n := n) W) → X := Subtype.val
  obtain ⟨D,Y,Q,hD,hTest,hStage,hFoot,hBound,hDrop⟩ :=
    finite_discrete_singular_global_phase hn W hW a (fun i => i.property) Subtype.val_injective
  let : DiscreteTopology (singularSet (n := n) (strictTransform n Q.proj W)) := hPersist Q hStage
  have hNew := (current_singular_compact_finite W hW hK Q hStage).2
  have hParent := (actual_singular_history_original_regular_protection W hW Q
    (intrinsic_stage_native_history W Q hStage)).2.2.2.2.2.1
  have hDropEach : ∀ y ∈ singularSet (n := n) (strictTransform n Q.proj W),
      (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (Q.proj y) ℓ) ∧
      ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y ℓ <
        hilbertSamuelAt (vanishingIdeal (n := n) W) (Q.proj y) ℓ := by
    intro y hy
    let i : singularSet (n := n) W := ⟨Q.proj y, hParent hy⟩
    let y' : openPreimage Q (D i) := ⟨y, hD i⟩
    simpa [a,i,y'] using hDrop i y'
  exact ⟨hOld,Y,Q,hNew,hTest,hStage,hBound,
    finite_singular_HS_multiset_descent W hW Q hStage hOld hNew hNe hDropEach⟩

end
end Hironaka.HironakaG8FiniteSingularHSPotential
