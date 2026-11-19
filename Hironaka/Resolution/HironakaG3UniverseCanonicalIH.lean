import Hironaka.Resolution.HironakaG3UniverseLiftThenIso
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseCanonicalIH
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold
  G3UniverseLiftedTower HironakaG3UniverseCanonicalValues G3UniverseLiftThenIso
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section

/-- The precise lower-depth induction hypothesis: equality on canonical histories and their cosupports. -/
def CanonicalLiftValueIH {n : ℕ} (hn : 0 < n) (k : ℕ) : Prop :=
  ∀ {X Y : CMfd.{0} n} (M : MarkedIdeal n X), IsInvDomain k M →
    ∀ (T : BlowupTower X Y), IsCanonical M ((invFamily.{0} hn k).inv M) T →
    ∀ z : liftCMfd.{u} Y, (liftDiffeomorph.{u} Y).symm z ∈ (geoTransformAlong M T).cosupp →
      (invFamily.{u} hn k).inv (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) z =
        (invFamily.{0} hn k).inv M T ((liftDiffeomorph.{u} Y).symm z)

/-- The canonical-history IH supplies agreement on every actual recorded prefix. -/
theorem prefix_values_of_canonical_IH {n k : ℕ} (hn : 0 < n) (hIH : CanonicalLiftValueIH.{u} hn k)
    {X : CMfd.{0} n} (M : MarkedIdeal n X) (hM : IsInvDomain k M) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) → IsCanonical M ((invFamily.{0} hn k).inv M) T →
      LiftedOriginalValuesAgree.{u} (k := k) hn M T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
    refine ⟨prefix_values_of_canonical_IH hn hIH M hM T hcan.1, ?_⟩
    exact hIH M hM T hcan.1

/-- A lower-depth canonical-history IH supplies both inputs for lift-then-isomorphism transport. -/
theorem canonical_and_values_of_canonical_IH {n k : ℕ} (hn : 0 < n) (hIH : CanonicalLiftValueIH.{u} hn k)
    {X Y : CMfd.{0} n} (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y)
    (hcan : IsCanonical M ((invFamily.{0} hn k).inv M) T)
    {X' Y' : CMfd.{u} n} (β : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} X)
    (Q : BlowupTower X' Y') (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} Y)
    (hiso : IsTowerIso β Q (liftTower.{u} T) χ) :
    let ML := markedPullback (m := n) (liftDiffeomorph.{u} X).symm M
    IsCanonical (markedPullback (m := n) β ML) ((invFamily.{u} hn k).inv (markedPullback (m := n) β ML)) Q ∧
    ∀ p : Y', (liftDiffeomorph.{u} Y).symm (χ p) ∈ (geoTransformAlong M T).cosupp →
      (invFamily.{u} hn k).inv (markedPullback (m := n) β ML) Q p =
        (invFamily.{0} hn k).inv M T ((liftDiffeomorph.{u} Y).symm (χ p)) := by
  have htest := (invFamily.{0} hn k).isInvValue.isGeoTestTower_of_isCanonical hM T hcan
  exact canonical_and_values_of_lift_then_iso hn M hM T htest hcan
    (prefix_values_of_canonical_IH hn hIH M hM T hcan) (hIH M hM T hcan) β Q χ hiso
end
end Hironaka.G3UniverseCanonicalIH
