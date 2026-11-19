import Hironaka.Resolution.HironakaG3UniverseLiftedMarkedHistory
import Hironaka.Resolution.HironakaG3UniverseCarrierGeometry
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.MonomialPartEtale
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeMonomial
import Hironaka.Resolution.HironakaG3UniverseSubmersionConjugate
import Hironaka.Blowup.BlowupBiholomorphismLift
import Hironaka.Resolution.HironakaG3UniverseVanishingIdeal
import Hironaka.Resolution.HironakaG3UniversePullbackPowers
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3UniverseMonomialVanishing
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers IdealWeightPowers G3UniverseVanishingIdeal HironakaG3UniversePullbackPowers
noncomputable section

/-- Literal centre vanishing ideal pullback for a cross-universe biholomorphism. -/
theorem pullback_vanishingIdeal_diffeo {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (H : Set X)
    (hPre : (vanishingIdeal (n := n) (e ⁻¹' H)).IsCoherent) :
    GermIdeal.pullback (m := n) e (vanishingIdeal (n := n) H) = vanishingIdeal (n := n) (e ⁻¹' H) := by
  have h := G3UniverseVanishingIdeal.pullback_vanishingIdeal_preimage e.contMDiff e.symm.contMDiff
    e.apply_symm_apply e.symm_apply_apply (g := (id : Y → Y)) contMDiff_id H
  rw [BlowupControlledTransform.pullback_id hPre] at h
  simpa only [Function.comp_id] using h.symm

/-- Literal pullback of an arbitrary coherent boundary vanishing power. -/
theorem pullback_vanishingPower_diffeo {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (H : Set X)
    (hH : (vanishingIdeal (n := n) H).IsCoherent)
    (hPre : (vanishingIdeal (n := n) (e ⁻¹' H)).IsCoherent) (q : ℕ) :
    GermIdeal.pullback (m := n) e (idealPow (vanishingIdeal (n := n) H) q) =
      idealPow (vanishingIdeal (n := n) (e ⁻¹' H)) q := by
  rw [HironakaG3UniversePullbackPowers.pullback_idealPow e.contMDiff hH,
    pullback_vanishingIdeal_diffeo e H hPre]
end
end Hironaka.HironakaG3UniverseMonomialVanishing


namespace Hironaka.HironakaG3UniverseMonomialPart
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  IdealWeightPowers RestrictedIdealExtension MonomialPartAlong MonomialPartEtale
  BlowupBiholomorphismLift HironakaSmoothSubmersionRelativeMonomial
  G3UniverseSubmersionConjugate HironakaG3UniverseMonomialVanishing DivisorExponentAlong
  GermIdealPullbackCalculus RelativePrincipalizationSpan
noncomputable section

/-- Memberwise whole monomial-part transport under an actual cross-universe biholomorphism. -/
theorem pullback_monomialPartAlong_diffeo {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (N : Set X) (I : GermIdeal n X) (E : List (Set X)) (hI : I.IsCoherent)
    (hMono : (monomialPartAlong n N I E).IsCoherent)
    (hH : ∀ H ∈ E, (vanishingIdeal (n := n) H).IsCoherent)
    (hPre : ∀ H ∈ E, (vanishingIdeal (n := n) (e ⁻¹' H)).IsCoherent) :
    GermIdeal.pullback (m := n) e (monomialPartAlong n N I E) =
      monomialPartAlong n (e ⁻¹' N) (GermIdeal.pullback (m := n) e I) (E.map (e ⁻¹' ·)) := by
  have hf := diffeo_isSubmersion (A := CMfd.of (n := n) X) (B := CMfd.of (n := n) Y) e
  have hexp (H : Set X) (y : Y) :
      divExpAlong n (e ⁻¹' N) (GermIdeal.pullback (m := n) e I) (e ⁻¹' H) y =
        divExpAlong n N I H (e y) :=
    divExpAlong_preimage_eq (X := X) (Y := Y) (f := e) hf hI N H y
  ext y F
  rw [mem_pullback_diffeo_iff e hMono, monomialPartAlong_mem_iff', monomialPartAlong_mem_iff']
  constructor
  · rintro ⟨hF,hall⟩
    have hFy : HolomorphicAt n F y := by
      have hh := holomorphicAt_comp_diffeo e hF
      have heq : (F ∘ e.symm) ∘ e = F := funext fun x => by simp
      rwa [heq] at hh
    refine ⟨hFy,?_⟩
    intro H' hH' hyN hyH
    obtain ⟨H,hHE,rfl⟩ := List.mem_map.mp hH'
    let q := divExpAlong n N I H (e y)
    have hspan := hall H hHE hyN hyH
    have hrest := (mem_restrictOn_pullback_diffeo_iff e
      (isCoherent_idealPow (hH H hHE) q)).mpr ⟨hF,hspan⟩
    rw [hexp H y]
    change IsInSpanOnAt (n := n) (e ⁻¹' N)
      ((idealPow (vanishingIdeal (n := n) (e ⁻¹' H)) q).mem y) y F
    rw [← pullback_vanishingPower_diffeo e H (hH H hHE) (hPre H hHE) q]
    exact hrest.2
  · rintro ⟨hF,hall⟩
    have hFx : HolomorphicAt n (F ∘ e.symm) (e y) := holomorphicAt_comp_diffeo_symm e hF
    refine ⟨hFx,?_⟩
    intro H hHE hyN hyH
    let q := divExpAlong n N I H (e y)
    have hspan := hall (e ⁻¹' H) (List.mem_map_of_mem hHE) hyN hyH
    rw [hexp H y] at hspan
    change IsInSpanOnAt (n := n) (e ⁻¹' N)
      ((idealPow (vanishingIdeal (n := n) (e ⁻¹' H)) q).mem y) y F at hspan
    rw [← pullback_vanishingPower_diffeo e H (hH H hHE) (hPre H hHE) q] at hspan
    have hrest := (mem_restrictOn_pullback_diffeo_iff e
      (isCoherent_idealPow (hH H hHE) q)).mp ⟨hF,hspan⟩
    exact hrest.2
end
end Hironaka.HironakaG3UniverseMonomialPart


namespace Hironaka.HironakaG3UniverseNonmonomialPart
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals HironakaSmoothSubmersionCoefficientIdeals GermIdealOrder
  RestrictedIdealQuotient MonomialPartAlong BlowupBiholomorphismLift
  HironakaSmoothSubmersionRelativeOrder G3UniverseSubmersionConjugate
  HironakaG3UniverseMonomialPart NonmonomialOrderLocal
noncomputable section

/-- Whole nonmonomial-part transport, with actual coherence inputs explicit. -/
theorem pullback_nonmonomialPartAlong_diffeo {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (N : Set X) (I : GermIdeal n X) (E : List (Set X)) (hI : I.IsCoherent)
    (hMono : (monomialPartAlong n N I E).IsCoherent)
    (hNonmono : (nonmonomialPartAlong n N I E).IsCoherent)
    (hH : ∀ H ∈ E, (vanishingIdeal (n := n) H).IsCoherent)
    (hPre : ∀ H ∈ E, (vanishingIdeal (n := n) (e ⁻¹' H)).IsCoherent) :
    GermIdeal.pullback (m := n) e (nonmonomialPartAlong n N I E) =
      nonmonomialPartAlong n (e ⁻¹' N) (GermIdeal.pullback (m := n) e I) (E.map (e ⁻¹' ·)) := by
  unfold nonmonomialPartAlong at hNonmono ⊢
  rw [← pullback_monomialPartAlong_diffeo e N I E hI hMono hH hPre,
    colonAlong_pullback_diffeo e hI hMono hNonmono]

/-- Every actual nonmonomial-order threshold pulls back literally. -/
theorem ordGe_markedPullback_diffeo {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent)
    (hMono : (monomialPartAlong n M.N M.ideal M.E).IsCoherent)
    (hNonmono : (nonmonomialPartAlong n M.N M.ideal M.E).IsCoherent)
    (hH : ∀ H ∈ M.E, (vanishingIdeal (n := n) H).IsCoherent)
    (hPre : ∀ H ∈ M.E, (vanishingIdeal (n := n) (e ⁻¹' H)).IsCoherent) (q : ℕ) :
    ordGe (M := CMfd.of (n := n) Y) (markedPullback (m := n) e M) q =
      e ⁻¹' ordGe (M := CMfd.of (n := n) X) M q := by
  change cosupport n (e ⁻¹' M.N)
    (nonmonomialPartAlong n (e ⁻¹' M.N) (GermIdeal.pullback (m := n) e M.ideal)
      (M.E.map (e ⁻¹' ·))) q = _
  rw [← pullback_nonmonomialPartAlong_diffeo e M.N M.ideal M.E hI hMono hNonmono hH hPre]
  exact cosupport_preimage_eq (X := X) (Y := Y) (f := e)
    (diffeo_isSubmersion (A := CMfd.of (n := n) X) (B := CMfd.of (n := n) Y) e) hNonmono M.N q

/-- Literal nonmonomial order under a cross-universe biholomorphism. -/
theorem nmOrd_markedPullback_diffeo {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent)
    (hMono : (monomialPartAlong n M.N M.ideal M.E).IsCoherent)
    (hNonmono : (nonmonomialPartAlong n M.N M.ideal M.E).IsCoherent)
    (hH : ∀ H ∈ M.E, (vanishingIdeal (n := n) H).IsCoherent)
    (hPre : ∀ H ∈ M.E, (vanishingIdeal (n := n) (e ⁻¹' H)).IsCoherent) (y : Y) :
    nmOrd (M := CMfd.of (n := n) Y) (markedPullback (m := n) e M) y =
      nmOrd (M := CMfd.of (n := n) X) M (e y) := by
  unfold nmOrd
  congr 1
  ext q
  change (y ∉ ordGe (M := CMfd.of (n := n) Y) (markedPullback (m := n) e M) (q+1)) ↔
    (e y ∉ ordGe (M := CMfd.of (n := n) X) M (q+1))
  rw [ordGe_markedPullback_diffeo e M hI hMono hNonmono hH hPre]
  rfl
end
end Hironaka.HironakaG3UniverseNonmonomialPart


namespace Hironaka.HironakaG3UniverseLiftedNmOrd
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold
  HironakaG3UniverseCarrierGeometry G3UniverseLiftedTower HironakaG3UniverseLiftedMarkedHistory
  HironakaG3UniverseNonmonomialPart MonomialPartAlong NonmonomialOrderLocal
noncomputable section

/-- A literal universe lift preserves the nonmonomial order of a record in the invariant domain. -/
theorem nmOrd_lifted_record {n k : ℕ} (hn : 0 < n) (X : CMfd.{0} n)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (y : liftCMfd.{u} X) :
    nmOrd (M := liftCMfd.{u} X) (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) y =
      nmOrd (M := X) M ((liftDiffeomorph.{u} X).symm y) := by
  have hm := isCoherent_monomialPartAlong hn hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isSNCDivisor hM.isWellFormed.isTransverse hM.isWellFormed.isCoherent hM.isNonzeroAlongAt
  have hnn := isCoherent_nonmonomialPartAlong hn hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isSNCDivisor hM.isWellFormed.isTransverse hM.isWellFormed.isCoherent hM.isNonzeroAlongAt
  have hH : ∀ H ∈ M.E, (vanishingIdeal (n := n) H).IsCoherent := by
    intro H hH
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    exact VanishingIdealCoherent.isCoherent_vanishingIdeal
      (MonomialPart.isClosedSubmanifold_get hn hM.isWellFormed.isSNCDivisor i)
  have hPre : ∀ H ∈ M.E, (vanishingIdeal (n := n) ((liftDiffeomorph.{u} X).symm ⁻¹' H)).IsCoherent := by
    intro H hH
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    exact VanishingIdealCoherent.isCoherent_vanishingIdeal
      (transported_closedSubmanifold (Homeomorph.ulift.symm : X ≃ₜ ULift.{u} X) _
        (MonomialPart.isClosedSubmanifold_get hn hM.isWellFormed.isSNCDivisor i))
  exact nmOrd_markedPullback_diffeo (liftDiffeomorph.{u} X).symm M hM.isWellFormed.isCoherent hm hnn hH hPre y

/-- The actual nonmonomial order at a lifted test-tower endpoint agrees. -/
theorem nmOrd_lifted_test_endpoint {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (y : liftCMfd.{u} Y) :
    nmOrd (M := liftCMfd.{u} Y)
      (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T)) y =
      nmOrd (M := Y) (geoTransformAlong M T) ((liftDiffeomorph.{u} Y).symm y) := by
  rw [liftTower_geoTransformAlong M hM.isWellFormed T hT]
  exact nmOrd_lifted_record hn Y _ (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT) y
end
end Hironaka.HironakaG3UniverseLiftedNmOrd
