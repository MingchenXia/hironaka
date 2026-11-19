import Hironaka.Resolution.HironakaG3UniverseCanonicalValues
import Hironaka.Resolution.HironakaG3UniverseMarkedDomain
import Hironaka.Invariant.ExtSeqTransport
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseLiftThenIso
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold
  G3UniverseLiftedTower HironakaG3UniverseLiftedMarkedHistory
  HironakaG3UniverseCanonicalValues HironakaG3UniverseMarkedDomain G3UniverseMarkedCosupport
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section

/-- Prefix and endpoint value agreement lift canonicality and values through a further actual tower isomorphism. -/
theorem canonical_and_values_of_lift_then_iso {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hcan : IsCanonical M ((invFamily.{0} hn k).inv M) T)
    (hprefix : LiftedOriginalValuesAgree.{u} (k := k) hn M T)
    (hfinal : ∀ z : liftCMfd.{u} Y, (liftDiffeomorph.{u} Y).symm z ∈ (geoTransformAlong M T).cosupp →
      (invFamily.{u} hn k).inv (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) z =
        (invFamily.{0} hn k).inv M T ((liftDiffeomorph.{u} Y).symm z))
    {X' Y' : CMfd.{u} n} (β : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} X)
    (Q : BlowupTower X' Y') (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} Y)
    (hiso : IsTowerIso β Q (liftTower.{u} T) χ) :
    let ML := markedPullback (m := n) (liftDiffeomorph.{u} X).symm M
    IsCanonical (markedPullback (m := n) β ML) ((invFamily.{u} hn k).inv (markedPullback (m := n) β ML)) Q ∧
    ∀ p : Y', (liftDiffeomorph.{u} Y).symm (χ p) ∈ (geoTransformAlong M T).cosupp →
      (invFamily.{u} hn k).inv (markedPullback (m := n) β ML) Q p =
        (invFamily.{0} hn k).inv M T ((liftDiffeomorph.{u} Y).symm (χ p)) := by
  let ML := markedPullback (m := n) (liftDiffeomorph.{u} X).symm M
  have hdom : IsInvDomain k ML := transported_markedPullback_domain X (Homeomorph.ulift.symm : X ≃ₜ ULift.{u} X) M hM
  have hcanL : IsCanonical ML ((invFamily.{u} hn k).inv ML) (liftTower.{u} T) :=
    liftTower_isCanonical_of_values hn M hM.isWellFormed T hT hcan hprefix
  have hcanQ := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso (invFamily.{u} hn k) hdom β hiso hcanL
  refine ⟨hcanQ, ?_⟩
  intro p hp
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM.isWellFormed T hT
  have hcos : (geoTransformAlong ML (liftTower.{u} T)).cosupp =
      (liftDiffeomorph.{u} Y).symm ⁻¹' (geoTransformAlong M T).cosupp := by
    rw [liftTower_geoTransformAlong M hM.isWellFormed T hT,
      markedPullback_cosupp_diffeo (liftDiffeomorph.{u} Y).symm _ hwf.isCoherent]
  have hpL : χ p ∈ (geoTransformAlong ML (liftTower.{u} T)).cosupp := by rw [hcos]; exact hp
  exact ((invFamily.{u} hn k).isInvValue.towerIso β ML hdom Q (liftTower.{u} T) χ hiso hcanL p hpL).trans (hfinal (χ p) hp)
end
end Hironaka.G3UniverseLiftThenIso
