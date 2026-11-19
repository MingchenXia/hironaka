import Hironaka.Resolution.HironakaSmoothSubmersionOriginalCanonicalComposition
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalLocallyFiniteHistory
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionOrderedChoiceBaseChange
open ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
open ResolutionInvariantSeq (GrowingSeq)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

/-- Literal pulled centres give whole source counts bounded by actual target image counts. -/
theorem IsActualTowerPullback.countCentresMeeting_le_image
    (h : IsActualTowerPullback f Q T g) (K : Set Y) :
    countCentresMeeting K Q ≤ countCentresMeeting (f '' K) T := by
  classical
  induction h with
  | refl => exact le_refl 0
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    change countCentresMeeting K Q + (if ((g ⁻¹' C) ∩ Q.proj ⁻¹' K).Nonempty then 1 else 0) ≤
      countCentresMeeting (f '' K) T + (if (C ∩ T.proj ⁻¹' (f '' K)).Nonempty then 1 else 0)
    apply Nat.add_le_add ih
    by_cases hp : ((g ⁻¹' C) ∩ Q.proj ⁻¹' K).Nonempty
    · obtain ⟨z,hzC,hzK⟩ := hp
      have ht : (C ∩ T.proj ⁻¹' (f '' K)).Nonempty := by
        refine ⟨g z,hzC,?_⟩
        change T.proj (g z) ∈ f '' K
        exact ⟨Q.proj z,hzK,(h.proj_comm z).symm⟩
      rw [if_pos ⟨z,hzC,hzK⟩,if_pos ht]
    · rw [if_neg hp]
      exact Nat.zero_le _

/-- Every stage is the literal source tower computed from the corresponding whole target tower. -/
def actualSourceStage (β : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {D : CMfd.{u} n} (T : BlowupTower X D) : Σ D' : CMfd.{u} m, BlowupTower Y D' :=
  ⟨(chosenActualTower β hf T).1,(chosenActualTower β hf T).2.1⟩

/-- Primitive choices internally construct genuine successor compatibility, not unrelated finite prefixes. -/
def actualSourceGrowing (β : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (s : GrowingSeq X) : GrowingSeq Y where
  stage i := actualSourceStage β hf (s.stage i).2
  zero := by
    change (fun S : Σ D : CMfd.{u} n, BlowupTower X D => actualSourceStage β hf S.2) (s.stage 0) = _
    rw [s.zero]
    rfl
  succ i := by
    obtain ⟨C,π,hπ,hstep⟩ := s.succ i
    change ∃ (C' : Set (actualSourceStage β hf (s.stage i).2).1)
      (ρ : (actualSourceStage β hf (s.stage (i+1)).2).1 → (actualSourceStage β hf (s.stage i).2).1)
      (hρ : IsBlowupAlong m C' ρ),
      (actualSourceStage β hf (s.stage (i+1)).2).2 = .step (actualSourceStage β hf (s.stage i).2).2 C' ρ hρ
    rw [hstep]
    dsimp only [actualSourceStage,chosenActualTower]
    exact ⟨_,_,_,rfl⟩

/-- The constructed growing stage retains its actual Cartesian witness and original whole length. -/
theorem actualSourceGrowing_stage_data (β : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (s : GrowingSeq X) (i : ℕ) :
    let P := chosenActualTower β hf (s.stage i).2
    (actualSourceGrowing β hf s).stage i = ⟨P.1,P.2.1⟩ ∧
      IsActualTowerPullback f P.2.1 (s.stage i).2 P.2.2.val ∧ P.2.1.length = (s.stage i).2.length :=
  ⟨rfl,(chosenActualTower β hf (s.stage i).2).2.2.property,
    (chosenActualTower β hf (s.stage i).2).2.2.property.length_eq⟩

theorem actualSourceGrowing_isCanonical (β : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (s : GrowingSeq X)
    (hcan : ∀ i, IsCanonical M ((canonicalInvariant n).inv M) (s.stage i).2) :
    ∀ i, IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) ((actualSourceGrowing β hf s).stage i).2 := by
  intro i
  exact IsActualTowerPullback.original_ambient_canonical
    (chosenActualTower β hf (s.stage i).2).2.2.property M hM (hcan i)

/-- Original per-sequence finiteness at the compact image internally bounds every actual source stage. -/
theorem actualSourceGrowing_compact_count_bound (β : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (s : GrowingSeq X)
    (hcan : ∀ i, IsCanonical M ((canonicalInvariant n).inv M) (s.stage i).2)
    (K : Set Y) (hK : IsCompact K) :
    ∃ N : ℕ, ∀ i, countCentresMeeting K ((actualSourceGrowing β hf s).stage i).2 ≤ N := by
  obtain ⟨N,hN⟩ := (canonicalInvariant n).seqLocallyFinite M hM (f '' K)
    (hK.image hf.contMDiff.continuous) s hcan
  refine ⟨N,fun i => ?_⟩
  exact (IsActualTowerPullback.countCentresMeeting_le_image
    (chosenActualTower β hf (s.stage i).2).2.2.property K).trans (hN i)
/-- Original inputs construct ONE actual canonical source growing history and its per-compact-set count bounds. -/
theorem exists_original_actual_source_growing_canonical_locally_finite
    (β : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (s : GrowingSeq X)
    (hcan : ∀ i, IsCanonical M ((canonicalInvariant n).inv M) (s.stage i).2) :
    ∃ q : GrowingSeq Y,
      IsInvDomain m (markedPullback (m := m) f M) ∧
      (∀ i, q.stage i = actualSourceStage β hf (s.stage i).2) ∧
      (∀ i, IsCanonical (markedPullback (m := m) f M)
        ((canonicalInvariant m).inv (markedPullback (m := m) f M)) (q.stage i).2) ∧
      ∀ K : Set Y, IsCompact K → ∃ B : ℕ, ∀ i, countCentresMeeting K (q.stage i).2 ≤ B := by
  exact ⟨actualSourceGrowing β hf s,original_ambient_domain_pullback hf M hM,
    fun _ => rfl,actualSourceGrowing_isCanonical β hf M hM s hcan,
    fun K hK => actualSourceGrowing_compact_count_bound β hf M hM s hcan K hK⟩
end
end Hironaka.HironakaSmoothSubmersionOriginalLocallyFiniteHistory
