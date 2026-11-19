import Hironaka.Resolution.HironakaG3UniverseLiftedTestHistory
import Hironaka.Invariant.CanonicalCentres
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseGenericCanonicalValues
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold
  G3UniverseLiftedTower HironakaG3UniverseLiftedMarkedHistory
  HironakaG3UniverseLiftedTestHistory G3UniverseMarkedCosupport ResolutionDriver
open ResolutionInvariantSpec (IsCanonical)
noncomputable section

/-- Explicit equality of two value functions at every actual recorded prefix. -/
def LiftedValuesAgree {n : ℕ} {Λ : Type} [LinearOrder Λ]
    (F₀ : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ)
    (Fᵤ : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    {X : CMfd.{0} n} (M : MarkedIdeal n X) : {Y : CMfd.{0} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T _ _ _ => LiftedValuesAgree F₀ Fᵤ M T ∧ ∀ z : liftCMfd.{u} _,
      (liftDiffeomorph.{u} _).symm z ∈ (geoTransformAlong M T).cosupp →
        Fᵤ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) z =
          F₀ M T ((liftDiffeomorph.{u} _).symm z)

/-- Prefix-value agreement carries actual maximum and empty centres under literal lift. -/
theorem liftTower_isCanonical_of_values_generic {n : ℕ} {Λ : Type} [LinearOrder Λ]
    (F₀ : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ)
    (Fᵤ : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    {X : CMfd.{0} n} (M : MarkedIdeal n X) (hM : M.IsWellFormed) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) → IsGeoTestTower M T →
    IsCanonical M (F₀ M) T → LiftedValuesAgree F₀ Fᵤ M T →
    IsCanonical (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      (Fᵤ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T)
  | _, .refl, _, _, _ => trivial
  | _, .step T C π hπ, hT, hcan, hval => by
    refine ⟨liftTower_isCanonical_of_values_generic F₀ Fᵤ M hM T hT.1 hcan.1 hval.1,?_⟩
    rcases hcan.2 with hC | hC
    · left
      rw [hC]
      exact preimage_empty
    · right
      rw [hC]
      have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT.1
      have hcos : (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
          (liftTower.{u} T)).cosupp = (liftDiffeomorph.{u} _).symm ⁻¹' (geoTransformAlong M T).cosupp := by
        rw [liftTower_geoTransformAlong M hM T hT.1,
          markedPullback_cosupp_diffeo (liftDiffeomorph.{u} _).symm _ hwf.isCoherent]
      rw [hcos]
      ext z
      constructor
      · rintro ⟨hz,hmax⟩
        refine ⟨hz,fun q hq => ?_⟩
        change Fᵤ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
          (liftTower.{u} T) q ≤ Fᵤ
            (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) z
        have hqv := hval.2 q hq
        have hzv := hval.2 z hz
        dsimp only at hqv hzv
        rw [hqv, hzv]
        exact hmax _ hq
      · rintro ⟨hz,hmax⟩
        refine ⟨hz,fun y hy => ?_⟩
        obtain ⟨q,hq⟩ := (liftDiffeomorph.{u} _).symm.surjective y
        subst y
        change F₀ M T ((liftDiffeomorph.{u} _).symm q) ≤
          F₀ M T ((liftDiffeomorph.{u} _).symm z)
        have hqv := hval.2 q hy
        have hzv := hval.2 z hz
        dsimp only at hqv hzv
        rw [← hqv, ← hzv]
        exact hmax q hy
end
end Hironaka.G3UniverseGenericCanonicalValues
