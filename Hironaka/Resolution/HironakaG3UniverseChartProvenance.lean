import Hironaka.Resolution.HironakaG3UniverseLiftedAtlas
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Resolution.HironakaG3UniverseDepthSucc
import Hironaka.Resolution.HironakaG3UniverseMarkedDomain
import Hironaka.Invariant.InvDomainTowerAlong
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseChartProvenance
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  BlowupTowerIsoTail MarkedIdealTowerTransport HironakaG3RTowerClass
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower G3UniverseOpenDiffeo
  G3UniverseChartTowerTransport G3UniverseLiftedChart G3UniverseLiftedAtlas
  G3UniverseCanonicalIH G3UniverseDepthSucc HironakaG3UniverseMarkedDomain
  HironakaSmoothSubmersionCoefficientIdeals MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section

/-- Retain a specific small class member and its stagewise isomorphism after lifting. -/
def liftedProvenanceClass {n : ℕ} {X : CMfd.{u} n} {X₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀)
    (𝒞 : LocalTowerClass X₀) : LocalTowerClass X :=
  fun U Y T => ∃ (U₀ : Opens X₀) (Y₀ : CMfd.{0} n)
    (T₀ : BlowupTower (CMfd.of (n := n) U₀) Y₀), 𝒞 U₀ Y₀ T₀ ∧
      ∃ hU : U = preimageOpens e U₀,
      ∃ χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ liftCMfd.{u} Y₀,
        IsTowerIso ((opensCongr hU).trans (baseLiftDiffeo e U₀)) T (liftTower.{u} T₀) χ

/-- Each literal lifted chart retains its original class member and tower isomorphism. -/
theorem lifted_chart_mem_provenance {n : ℕ} {X : CMfd.{u} n} {X₀ Y₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀)
    {P : Y₀ → X₀} {𝒞 : LocalTowerClass X₀} (c : TowerChart 𝒞 Y₀ P) :
    liftedProvenanceClass e 𝒞 (liftedTowerChart e c).U (liftedTowerChart e c).Y
      (liftedTowerChart e c).T := by
  refine ⟨c.U,c.Y,c.T,c.mem,rfl,(chartTowerTransport e c.U c.T).back,?_⟩
  have hβ : (opensCongr (rfl : preimageOpens e c.U = preimageOpens e c.U)).trans
      (baseLiftDiffeo e c.U) = baseLiftDiffeo e c.U := by
    ext x
    rfl
  change IsTowerIso ((opensCongr (rfl : preimageOpens e c.U = preimageOpens e c.U)).trans
      (baseLiftDiffeo e c.U)) (chartTowerTransport e c.U c.T).tower
      (liftTower.{u} c.T) (chartTowerTransport e c.U c.T).back
  rw [hβ]
  exact transport_isTowerIso (baseLiftDiffeo e c.U) (liftTower.{u} c.T)

/-- Canonical small-class witnesses yield canonical records on each actual provenance tower. -/
theorem provenance_is_canonical {n r : ℕ} (hn : 0 < n) {X : CMfd.{u} n} {X₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀) (𝒞 : LocalTowerClass X₀)
    (hcan : ∀ (U₀ : Opens X₀) (Y₀ : CMfd.{0} n) (T₀ : BlowupTower (CMfd.of (n := n) U₀) Y₀), 𝒞 U₀ Y₀ T₀ →
      ∃ M : MarkedIdeal n (CMfd.of (n := n) U₀), IsInvDomain r M ∧
        IsCanonical M ((invFamily.{0} hn r).inv M) T₀)
    {U : Opens X} {Y : CMfd.{u} n} {T : BlowupTower (CMfd.of (n := n) U) Y}
    (hT : liftedProvenanceClass e 𝒞 U Y T) :
    ∃ M : MarkedIdeal n (CMfd.of (n := n) U), IsInvDomain r M ∧
      IsCanonical M ((invFamily.{u} hn r).inv M) T := by
  obtain ⟨U₀,Y₀,T₀,hT₀,hU,χ,hiso⟩ := hT
  obtain ⟨M,hM,hc⟩ := hcan U₀ Y₀ T₀ hT₀
  let β := (opensCongr hU).trans (baseLiftDiffeo e U₀)
  let ML := markedPullback (m := n) (liftDiffeomorph.{u} (CMfd.of (n := n) U₀)).symm M
  have hML : IsInvDomain r ML := transported_markedPullback_domain _
    (Homeomorph.ulift.symm : CMfd.of (n := n) U₀ ≃ₜ ULift.{u} (CMfd.of (n := n) U₀)) M hM
  have hdom : IsInvDomain r (markedPullback (m := n) β ML) :=
    InvDomainTowerAlong.isInvDomain_pullback β hML
  have h := canonical_and_values_of_canonical_IH hn (canonicalLiftValueIH_all hn r) M hM T₀ hc β T χ hiso
  exact ⟨_,hdom,h.1⟩

/-- A supplied glued atlas retains its original class provenance after literal lifting. -/
theorem lifted_provenance_atlas {n : ℕ} {X : CMfd.{u} n} {X₀ Y₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀)
    {P : Y₀ → X₀} {𝒞 : LocalTowerClass X₀} (hG : IsGluedFrom 𝒞 Y₀ P) :
    IsGluedFrom (liftedProvenanceClass e 𝒞) (liftCMfd.{u} Y₀)
      (e.symm ∘ P ∘ (liftDiffeomorph.{u} Y₀).symm) := by
  have h := lifted_universal_atlas e hG
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  intro x
  obtain ⟨c,hx⟩ := hG.2.2.2 (e x)
  let c' := liftedTowerChart e c
  exact ⟨⟨c'.U,c'.Y,c'.T,lifted_chart_mem_provenance e c,c'.V,c'.V_eq,c'.φ,c'.proj_φ⟩,hx⟩
end
end Hironaka.G3UniverseChartProvenance
