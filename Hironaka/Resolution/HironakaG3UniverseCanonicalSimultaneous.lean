import Hironaka.Resolution.HironakaG3UniverseGenericCanonicalValues
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseCanonicalSimultaneous
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaSmoothSubmersionCoefficientIdeals
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower G3UniverseGenericCanonicalValues
open ResolutionInvariantSpec (IsCanonical)
noncomputable section

/-- Given a local value bridge on pairs of actual canonical histories, the literal lifted
history is canonical and its previous recorded prefixes have the corresponding values. -/
theorem canonical_prefixes_of_local_bridge {n : ℕ} {Λ : Type} [LinearOrder Λ]
    (F₀ : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ)
    (Fᵤ : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    {X : CMfd.{0} n} (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hlocal : ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower M T →
      IsCanonical M (F₀ M) T →
      IsCanonical (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
        (Fᵤ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T) →
      ∀ z : liftCMfd.{u} Y, (liftDiffeomorph.{u} Y).symm z ∈ (geoTransformAlong M T).cosupp →
        Fᵤ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) z =
          F₀ M T ((liftDiffeomorph.{u} Y).symm z)) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) → IsGeoTestTower M T → IsCanonical M (F₀ M) T →
      LiftedValuesAgree F₀ Fᵤ M T ∧
      IsCanonical (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
        (Fᵤ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T)
  | _, .refl, _, _ => ⟨trivial,trivial⟩
  | _, .step T C π hπ, hT, hcan => by
    have ih := canonical_prefixes_of_local_bridge F₀ Fᵤ M hM hlocal T hT.1 hcan.1
    have hp : LiftedValuesAgree F₀ Fᵤ M (.step T C π hπ) := ⟨ih.1,hlocal T hT.1 hcan.1 ih.2⟩
    exact ⟨hp, liftTower_isCanonical_of_values_generic F₀ Fᵤ M hM _ hT hcan hp⟩

/-- The same local bridge also gives endpoint equality once the simultaneous induction has
established canonicality of the actual lifted tower. -/
theorem canonical_endpoint_of_local_bridge {n : ℕ} {Λ : Type} [LinearOrder Λ]
    (F₀ : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ)
    (Fᵤ : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    {X Y : CMfd.{0} n} (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hlocal : ∀ {Z : CMfd.{0} n} (T : BlowupTower X Z), IsGeoTestTower M T →
      IsCanonical M (F₀ M) T →
      IsCanonical (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
        (Fᵤ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T) →
      ∀ z : liftCMfd.{u} Z, (liftDiffeomorph.{u} Z).symm z ∈ (geoTransformAlong M T).cosupp →
        Fᵤ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) z =
          F₀ M T ((liftDiffeomorph.{u} Z).symm z))
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (hcan : IsCanonical M (F₀ M) T) :
    ∀ z : liftCMfd.{u} Y, (liftDiffeomorph.{u} Y).symm z ∈ (geoTransformAlong M T).cosupp →
      Fᵤ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) z =
        F₀ M T ((liftDiffeomorph.{u} Y).symm z) :=
  hlocal T hT hcan (canonical_prefixes_of_local_bridge F₀ Fᵤ M hM hlocal T hT hcan).2
end
end Hironaka.G3UniverseCanonicalSimultaneous
