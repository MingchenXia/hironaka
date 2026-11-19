import Mathlib.Topology.DiscreteSubset
import Hironaka.Resolution.HironakaG8MergedHSLocality
import Hironaka.Resolution.HironakaG8IsolatedProfileGlobalPhase
import Hironaka.Resolution.HironakaG8FiniteSingularTowerMerge
set_option autoImplicit false
open Set Filter Function Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8FiniteIsolatedProfilePhase
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaEmbeddedAnalytic HironakaStageCenters
  HironakaHolomorphicJetChartInvariance HironakaG3EmptyAwareHistory
  HironakaG3FiniteDisjointTowerMerge HironakaG8IsolatedProfileGlobalPhase
  HironakaG8FiniteSingularTowerMerge HomogenizedGlueingTower NormalCrossings
  HironakaG8NativePhaseHSControl HironakaG8LocallyConstantBennett HironakaG8MergedHSLocality
  HironakaActualWholeHSSingularity

/-- Finitely many separated isolated HS levels admit one actual global
singular-centred original-test phase with simultaneous local profile drops. -/
theorem finite_isolated_profile_global_phase {n : ℕ} (hn : 0<n)
    {X : CMfd.{0} n} {ι : Type} [Fintype ι] [DecidableEq ι]
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (a : ι → X) (O : ι → Opens X)
    (ha : ∀ i, a i ∈ singularSet (n := n) W) (haO : ∀ i, a i ∈ O i)
    (hsep : ∀ i j, i ≠ j → a j ∉ O i)
    (hisol : ∀ i x, x ∈ O i → (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n) W) (a i) ℓ) → x = a i) :
    ∃ (D : ι → Opens X) (Y : ι → CMfd.{0} n) (T : ∀ i, BlowupTower X (Y i))
      (Z : CMfd.{0} n) (Q : BlowupTower X Z),
      (∀ i, a i ∈ D i ∧ D i ≤ O i) ∧
      IsGeoTestTower (⟨univ,[],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) Q ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) Q ∧
      CentresOver (range a) Q ∧
      (∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) z ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (Q.proj z) ℓ) ∧
      (∀ i, ∃ φ : (CMfd.of (n := n) (openPreimage Q (D i))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          (CMfd.of (n := n) (openPreimage (T i) (D i))),
        EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (D i)) ∞)
          (restrict (D i) Q) (restrict (D i) (T i)) φ) ∧
      ∀ i (y : openPreimage Q (D i)),
        (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y.val ℓ ≤
          hilbertSamuelAt (vanishingIdeal (n := n) W) (a i) ℓ) ∧
        ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y.val ℓ <
          hilbertSamuelAt (vanishingIdeal (n := n) W) (a i) ℓ := by
  have hex i := exists_isolated_profile_global_HS_control hn W hW (a i) (ha i) (O i) (haO i) (hisol i)
  choose D haD hDO Y T hTest hStage hFoot hProfile hBound hAmbient using hex
  let M : MarkedIdeal n X := ⟨univ,[],vanishingIdeal (n := n) W,1⟩
  have hM : M.IsWellFormed := ⟨isClosedSubmanifold_univ,CartanIrreducible.cartanCoherence W hW,
    isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold isClosedSubmanifold_univ⟩
  let F : ι → Set X := fun i => {a i}
  have hF : ∀ i, IsClosed (F i) := fun _ => isClosed_singleton
  have hFD : ∀ i, F i ⊆ D i := by intro i x hx; simp only [F,mem_singleton_iff] at hx; simpa [hx] using haD i
  have hdisj : ∀ i j, i ≠ j → Disjoint (D i : Set X) (F j) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hxD hxF
    simp only [F,mem_singleton_iff] at hxF
    subst x
    exact hsep i j hij (hDO i hxD)
  obtain ⟨Z',Q,hQT,hQS,hQF,hCompare⟩ :=
    finite_disjoint_singular_test_towers_merge M hM W hW.isClosed F hF D hFD hdisj Y T hFoot hTest hStage Finset.univ
  have hRange : finiteSupport F Finset.univ = range a := by ext x; simp [finiteSupport,F]
  have hQRange : CentresOver (range a) Q := hRange ▸ hQF
  have hCovered : ∀ x ∈ range a, ∃ i, x ∈ D i := by
    rintro x ⟨i,rfl⟩
    exact ⟨i,haD i⟩
  have hLocalProfile : ∀ i, StageCentres (fun P C => ∀ c ∈ C, ∀ ℓ,
      hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj
        ((Subtype.val : D i → X) ⁻¹' W))) c ℓ =
          hilbertSamuelAt (vanishingIdeal (n := n) W) (a i) ℓ) (restrict (D i) Q) := by
    intro i
    obtain ⟨φ,hφ⟩ := hCompare i (Finset.mem_univ i)
    have hs := stages_HS_profile_restrict W (hilbertSamuelAt (vanishingIdeal (n := n) W) (a i))
      (D i) (T i) (hProfile i)
    have hs' := stages_HS_profile_of_emptyAware (n := n)
      (X' := CMfd.of (n := n) (D i)) (X := CMfd.of (n := n) (D i))
      (T' := restrict (D i) (T i)) (T := restrict (D i) Q) (χ := φ.symm)
      ((Subtype.val : D i → X) ⁻¹' W) (hW.isClosed.preimage continuous_subtype_val)
      (hilbertSamuelAt (vanishingIdeal (n := n) W) (a i))
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (D i)) ∞).symm
      (HironakaG3EmptyAwareSymmetry.symm hφ)
    simp only [Diffeomorph.symm_refl,Diffeomorph.coe_refl,preimage_id] at hs'
    exact hs' hs
  have hLoc := locally_constant_stages_of_profiles W (range a) D
    (fun i => hilbertSamuelAt (vanishingIdeal (n := n) W) (a i)) hCovered Q hQRange hLocalProfile
  have hGlobalBound := locally_constant_tower_bennett W hW Q hLoc
  refine ⟨D,Y,T,Z',Q,fun i => ⟨haD i,hDO i⟩,hQT,hQS,hQRange,hGlobalBound,?_,?_⟩
  · intro i
    exact hCompare i (Finset.mem_univ i)
  · intro i
    obtain ⟨φ,hφ⟩ := hCompare i (Finset.mem_univ i)
    exact profile_drop_of_emptyAware_open_overlap W hW.isClosed (D i)
      (hilbertSamuelAt (vanishingIdeal (n := n) W) (a i)) Q (T i) φ hφ (hAmbient i)

/-- Finitely many separated isolated singular points admit a single actual
global HS-nonincreasing singular-centred phase with strict local drops. -/
theorem finite_isolated_singular_global_phase {n : ℕ} (hn : 0<n)
    {X : CMfd.{0} n} {ι : Type} [Fintype ι] [DecidableEq ι]
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (a : ι → X) (O : ι → Opens X)
    (ha : ∀ i, a i ∈ singularSet (n := n) W) (haO : ∀ i, a i ∈ O i)
    (hsep : ∀ i j, i ≠ j → a j ∉ O i)
    (hisol : ∀ i x, x ∈ O i → x ∈ singularSet (n := n) W → x = a i) :
    ∃ (D : ι → Opens X) (Z : CMfd.{0} n) (Q : BlowupTower X Z),
      (∀ i, a i ∈ D i ∧ D i ≤ O i) ∧
      IsGeoTestTower (⟨univ,[],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) Q ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) Q ∧
      CentresOver (range a) Q ∧
      (∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) z ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (Q.proj z) ℓ) ∧
      ∀ i (y : openPreimage Q (D i)),
        (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y.val ℓ ≤
          hilbertSamuelAt (vanishingIdeal (n := n) W) (a i) ℓ) ∧
        ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y.val ℓ <
          hilbertSamuelAt (vanishingIdeal (n := n) W) (a i) ℓ := by
  have hProfile : ∀ i x, x ∈ O i → (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n) W) (a i) ℓ) → x = a i := by
    intro i x hx he
    exact hisol i x hx (entire_hs_equality_locus_subset_singularSet hW (ha i) he)
  obtain ⟨D,Y,T,Z,Q,hD,hTest,hStage,hFoot,hBound,hCompare,hDrop⟩ :=
    finite_isolated_profile_global_phase hn W hW a O ha haO hsep hProfile
  exact ⟨D,Z,Q,hD,hTest,hStage,hFoot,hBound,hDrop⟩

/-- A finite selection from a discrete singular locus internally supplies the
separated windows needed for one actual global singular-centred phase. -/
theorem finite_discrete_singular_global_phase {n : ℕ} (hn : 0<n)
    {X : CMfd.{0} n} {ι : Type} [Fintype ι] [DecidableEq ι]
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    [DiscreteTopology (singularSet (n := n) W)]
    (a : ι → X) (ha : ∀ i, a i ∈ singularSet (n := n) W) (hinj : Function.Injective a) :
    ∃ (D : ι → Opens X) (Z : CMfd.{0} n) (Q : BlowupTower X Z),
      (∀ i, a i ∈ D i) ∧
      IsGeoTestTower (⟨univ,[],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) Q ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) Q ∧
      CentresOver (range a) Q ∧
      (∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) z ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (Q.proj z) ℓ) ∧
      ∀ i (y : openPreimage Q (D i)),
        (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y.val ℓ ≤
          hilbertSamuelAt (vanishingIdeal (n := n) W) (a i) ℓ) ∧
        ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y.val ℓ <
          hilbertSamuelAt (vanishingIdeal (n := n) W) (a i) ℓ := by
  let O : ι → Opens X := fun i =>
    ⟨(discreteTopology_subtype_iff'.mp inferInstance (a i) (ha i)).choose,
      (discreteTopology_subtype_iff'.mp inferInstance (a i) (ha i)).choose_spec.1⟩
  have hO (i : ι) : (O i : Set X) ∩ singularSet (n := n) W = {a i} :=
    (discreteTopology_subtype_iff'.mp inferInstance (a i) (ha i)).choose_spec.2
  have haO (i : ι) : a i ∈ O i := by
    have h : a i ∈ (O i : Set X) ∩ singularSet (n := n) W := by rw [hO]; exact mem_singleton _
    exact h.1
  have hisol : ∀ i x, x ∈ O i → x ∈ singularSet (n := n) W → x = a i := by
    intro i x hx hs
    have h : x ∈ (O i : Set X) ∩ singularSet (n := n) W := ⟨hx,hs⟩
    rw [hO] at h
    exact h
  have hsep : ∀ i j, i ≠ j → a j ∉ O i := by
    intro i j hij hj
    have heq : a j = a i := hisol i (a j) hj (ha j)
    exact hij (hinj heq.symm)
  obtain ⟨D,Z,Q,hD,hTest,hStage,hFoot,hBound,hDrop⟩ :=
    finite_isolated_singular_global_phase hn W hW a O ha haO hsep hisol
  exact ⟨D,Z,Q,fun i => (hD i).1,hTest,hStage,hFoot,hBound,hDrop⟩
end
end Hironaka.HironakaG8FiniteIsolatedProfilePhase
