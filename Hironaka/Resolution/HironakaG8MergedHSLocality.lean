import Hironaka.Resolution.HironakaG8NativePhaseHSControl
import Hironaka.Resolution.HironakaG8FiniteSingularTowerMerge
import Hironaka.Resolution.HironakaG8LocallyConstantBennett
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8MergedHSLocality
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism RestrictEmptyTower
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance HironakaStageCenters
  HironakaG3EmptyAwareHistory HironakaNormalCrossingsSeparationChoiceComparison
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaResolutionSpaceLocal
  HironakaSmoothSubmersionOriginalGlobalFinite HironakaActualVanishingIntrinsicHSTransport
  HironakaG8NativePhaseHSControl HironakaG8FiniteSingularTowerMerge HironakaG8LocallyConstantBennett

/-- Exact centre profiles restrict to each actual open tower. -/
theorem stages_HS_profile_restrict {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (H : ℕ → ℕ) (U : Opens X) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => ∀ c ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n P.proj W)) c ℓ = H ℓ) T →
      StageCentres (fun P C => ∀ c ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n P.proj ((Subtype.val : U → X) ⁻¹' W))) c ℓ = H ℓ) (restrict U T)
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hs => by
      refine ⟨stages_HS_profile_restrict W H U T hs.1,?_⟩
      intro c hc ℓ
      rw [strictTransform_restricted_tower U T W,hilbertSamuelAt_vanishing_actual_open_any]
      exact hs.2 c.val hc ℓ

/-- Open-cover profile certificates imply local HS constancy at every centre,
provided the tower is supported over the covered footprint. -/
theorem locally_constant_stages_of_profiles {n : ℕ} {X : CMfd.{0} n} {ι : Type}
    (W F : Set X) (U : ι → Opens X) (H : ι → ℕ → ℕ)
    (hcover : ∀ x ∈ F, ∃ i, x ∈ U i) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), CentresOver F T →
      (∀ i, StageCentres (fun P C => ∀ c ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n P.proj ((Subtype.val : U i → X) ⁻¹' W))) c ℓ = H i ℓ) (restrict (U i) T)) →
      StageCentres (fun P C => ∀ x ∈ C, ∃ O : Opens _, x ∈ O ∧
        ∀ u ∈ C, u ∈ O → ∀ v ∈ C, v ∈ O → ∀ ℓ,
          hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) u ℓ =
            hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) v ℓ) T
  | _, .refl, _, _ => trivial
  | _, .step T C π hπ, ho, hs => by
      refine ⟨locally_constant_stages_of_profiles W F U H hcover T ho.1 (fun i => (hs i).1),?_⟩
      intro x hx
      obtain ⟨i,hi⟩ := hcover (T.proj x) (ho.2 hx)
      refine ⟨openPreimage T (U i),hi,?_⟩
      intro u hu huO v hv hvO ℓ
      let u' : openPreimage T (U i) := ⟨u,huO⟩
      let v' : openPreimage T (U i) := ⟨v,hvO⟩
      have huH := (hs i).2 u' (show u' ∈ (Subtype.val : openPreimage T (U i) → _) ⁻¹' C from hu) ℓ
      have hvH := (hs i).2 v' (show v' ∈ (Subtype.val : openPreimage T (U i) → _) ⁻¹' C from hv) ℓ
      rw [strictTransform_restricted_tower (U i) T W,hilbertSamuelAt_vanishing_actual_open_any] at huH hvH
      exact huH.trans hvH.symm
end
end Hironaka.HironakaG8MergedHSLocality
