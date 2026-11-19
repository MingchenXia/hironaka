import Hironaka.Resolution.HironakaG8NativeBoundaryComparison
import Hironaka.Resolution.HironakaG8NativeHSEmptyFreeTowerComparison
import Hironaka.Resolution.HironakaG3EmptyAwareCanonicalTransport
import Hironaka.Resolution.HironakaG8HSTowerStateStrictTransform
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport

/-! Physical compatibility of terminal native histories on the full boundary. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8FullBoundaryTerminalOverlap

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism HironakaG3EmptyAwareHistory HironakaEmbeddedAnalytic
  HironakaHolomorphicJetChartInvariance HironakaG11PresLineState HironakaG11PresTowerState
  HironakaNormalCrossingsSeparationChoiceComparison
  HironakaG8HSTowerStateStrictTransform HironakaActualVanishingIntrinsicHSTransport
  HironakaG8NativeBoundaryComparison HironakaG8NativeHSEmptyFreeTowerComparison
  G3EmptyAwareCanonicalCompression
  ResolutionInvariantSpec CanonicalCentres HironakaG11InvTransport HironakaG8LocalHistory
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealTowerTransport MarkedIdealRestrictOpen
  HironakaOriginalTerminalOverlapComparison MaxLocusLocal

private theorem resolution_of_native_projection_comparison {n : ℕ} {X Y Z : CMfd.{0} n}
    (P : MarkedIdeal n X) {W : Set X} {H : ℕ → ℕ} (hState : NativeHSState P W H)
    (S : BlowupTower X Y) (T : BlowupTower X Z) (hS : IsGeoTestTower P S)
    (hT : IsGeoResolution P T)
    (χ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z)
    (hχ : ∀ y, T.proj (χ y) = S.proj y) : IsGeoResolution P S := by
  have hW := hState.2.1.isClosed
  have hSS := hsTowerState_strictAlong_eq_strictTransform P hW hState.hsTowerState S hS
  have hTS := hsTowerState_strictAlong_eq_strictTransform P hW hState.hsTowerState T hT.1
  have hST : strictTransform n S.proj W = χ ⁻¹' strictTransform n T.proj W := by
    simpa only [Diffeomorph.coe_refl, preimage_id, id_eq] using
      (strictTransform_preimage_of_square (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞)
        χ S.contMDiff_proj T.contMDiff_proj W hW hχ)
  refine ⟨hS, eq_empty_iff_forall_notMem.mpr fun y hy => ?_⟩
  have hY := (hState.hsTowerState S hS).2.2.2.1 y
  have hZ := (hState.hsTowerState T hT.1).2.2.2.1 (χ y)
  rw [hSS, hST] at hY
  rw [hTS] at hZ
  have hHit := hZ.mpr fun ℓ => by
    rw [← hilbertSamuelAt_vanishing_actual_biholomorphic_any χ (strictTransform n T.proj W) y ℓ]
    exact hY.mp hy ℓ
  rw [hT.2] at hHit
  exact hHit

/-- The actual native terminal towers on a common ambient space are
empty-aware isomorphic whenever their full boundary agrees and no incident
member is contained as a germ in the carrier at the cut. -/
theorem native_terminal_emptyAware_of_common_boundary {n k : ℕ} (hn : 0 < n)
    {X Y Z : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    {W : Set X} {H : ℕ → ℕ} (hSP : NativeHSState P W H) (hSQ : NativeHSState Q W H)
    (hE : P.E = Q.E)
    (hNot : ∀ D ∈ P.E, ∀ x ∈ P.cosupp, x ∈ D →
      ¬ ∀ᶠ y in 𝓝 x, y ∈ D → y ∈ W)
    (TP : BlowupTower X Y) (TQ : BlowupTower X Z)
    (hCanP : IsCanonical P ((invFamily hn k).inv P) TP)
    (hCanQ : IsCanonical Q ((invFamily hn k).inv Q) TQ)
    (hResP : IsGeoResolution P TP) (hResQ : IsGeoResolution Q TQ) :
    ∃ χ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞) TQ TP χ := by
  let e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X :=
    Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞
  have heP : MarkedIdeal.pullback e P = P := ContactCanonicalAlong.pullback_id P hP.isWellFormed.isCoherent
  have heQ : MarkedIdeal.pullback e Q = Q := ContactCanonicalAlong.pullback_id Q hQ.isWellFormed.isCoherent
  have hBound : (MarkedIdeal.pullback e P).E = (MarkedIdeal.pullback e Q).E := by
    rw [heP, heQ, hE]
  have hNoncontainment : ∀ D ∈ (MarkedIdeal.pullback e P).E,
      ∀ x ∈ (MarkedIdeal.pullback e P).cosupp, x ∈ D → ¬ ∀ᶠ y in 𝓝 x, y ∈ D → y ∈ e ⁻¹' W := by
    simpa only [heP, show e ⁻¹' W = W from rfl] using hNot
  obtain ⟨hEq, _, _, _, _, hIff⟩ :=
    native_boundary_comparison hn e e P Q hP hQ hSP hSQ rfl hBound hNoncontainment
  rw [heP, heQ] at hEq hIff
  have hCanQP := (hIff TQ).mpr hCanQ
  have hTestQP := (hEq.wEquiv.2 TQ).1.mpr hResQ.1
  have hResQP : IsGeoResolution P TQ := ⟨hTestQP, ((hEq.wEquiv.2 TQ).2 hTestQP).trans hResQ.2⟩
  obtain ⟨Y', SP, eP, hNeP, _, hPhysP, hCanP'⟩ :=
    original_family_compress_empty_iff hn k P hP TP
  obtain ⟨Z', SQ, eQ, hNeQ, _, hPhysQ, hCanQ'⟩ :=
    original_family_compress_empty_iff hn k P hP TQ
  have hcP := hCanP'.mpr hCanP
  have hcQ := hCanQ'.mpr hCanQP
  have hRP := resolution_of_native_projection_comparison P hSP SP TP
    ((invFamily hn k).isInvValue.isGeoTestTower_of_isCanonical hP SP hcP) hResP eP
    (fun y => by simpa only [Diffeomorph.coe_refl, id_eq] using emptyAware_proj_comm hPhysP y)
  have hRQ := resolution_of_native_projection_comparison P hSP SQ TQ
    ((invFamily hn k).isInvValue.isGeoTestTower_of_isCanonical hP SQ hcQ) hResQP eQ
    (fun y => by simpa only [Diffeomorph.coe_refl, id_eq] using emptyAware_proj_comm hPhysQ y)
  have hSame : RestrictEquiv (MarkedIdeal.pullback e P) P := by
    rw [heP]
    exact RestrictEquiv.refl hP.isWellFormed.isCoherent
  obtain ⟨η, hη⟩ := resolving_canonicalSegments_isTowerIso (invFamily hn k) e hP hP hSame SQ SP
    (segment_of_canonical_of_nonempty_centres P ((invFamily hn k).inv P) SQ hNeQ hcQ)
    (segment_of_canonical_of_nonempty_centres P ((invFamily hn k).inv P) SP hNeP hcP) hRQ hRP
  refine ⟨eQ.symm.trans (η.trans eP), ?_⟩
  have h := HironakaG3EmptyAwareComposition.trans (HironakaG3EmptyAwareSymmetry.symm hPhysQ)
    (HironakaG3EmptyAwareComposition.trans (emptyAware_of_isTowerIso hη) hPhysP)
  have he : e.symm = e := by ext x; rfl
  simpa only [he, e, Diffeomorph.refl_trans, Diffeomorph.trans_refl] using h

/-- Independent native resolving charts give a physical comparison on the
actual overlap, with the entire restricted boundary in the input records. -/
theorem native_terminal_overlap_emptyAware_of_full_boundary {n k : ℕ} (hn : 0 < n)
    {X Y Z : CMfd.{0} n} {U V O : Opens X} (hOU : O ≤ U) (hOV : O ≤ V)
    (P : MarkedIdeal n (CMfd.of (n := n) U)) (Q : MarkedIdeal n (CMfd.of (n := n) V))
    (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    {W : Set X} {H : ℕ → ℕ}
    (hSP : NativeHSState P ((Subtype.val : U → X) ⁻¹' W) H)
    (hSQ : NativeHSState Q ((Subtype.val : V → X) ⁻¹' W) H)
    (TP : BlowupTower (CMfd.of (n := n) U) Y) (TQ : BlowupTower (CMfd.of (n := n) V) Z)
    (hCanP : IsCanonical P ((invFamily hn k).inv P) TP)
    (hCanQ : IsCanonical Q ((invFamily hn k).inv Q) TQ)
    (hResP : IsGeoResolution P TP) (hResQ : IsGeoResolution Q TQ)
    (hBoundary :
      (MarkedIdeal.pullback (Subtype.val : nestedOpens U O → U) P).E =
      (MarkedIdeal.pullback (overlapBaseEquiv hOU hOV)
        (MarkedIdeal.pullback (Subtype.val : nestedOpens V O → V) Q)).E)
    (hNot :
      ∀ D ∈ (MarkedIdeal.pullback (Subtype.val : nestedOpens U O → U) P).E,
        ∀ x ∈ (MarkedIdeal.pullback (Subtype.val : nestedOpens U O → U) P).cosupp,
          x ∈ D → ¬ ∀ᶠ y in 𝓝 x, y ∈ D → (y.val.val : X) ∈ W) :
    ∃ χ : CMfd.of (n := n) (openPreimage TP (nestedOpens U O))
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage TQ (nestedOpens V O)),
      EmptyAwareTowerIso (overlapBaseEquiv hOU hOV)
        (restrict (nestedOpens U O) TP) (restrict (nestedOpens V O) TQ) χ := by
  let UO := nestedOpens U O
  let VO := nestedOpens V O
  let φ := overlapBaseEquiv hOU hOV
  let A := MarkedIdeal.pullback (Subtype.val : UO → U) P
  let R := MarkedIdeal.pullback (Subtype.val : VO → V) Q
  let B := MarkedIdeal.pullback φ R
  let S := restrict UO TP
  let T := restrict VO TQ
  have hA : IsInvDomain k A := InvDomainTowerAlong.isInvDomain_pullback_val UO hP
  have hR : IsInvDomain k R := InvDomainTowerAlong.isInvDomain_pullback_val VO hQ
  have hB : IsInvDomain k B := InvDomainTowerAlong.isInvDomain_pullback φ hR
  have hEq : (Subtype.val : UO → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' W) =
      φ ⁻¹' ((Subtype.val : VO → V) ⁻¹' ((Subtype.val : V → X) ⁻¹' W)) := by
    ext x
    change x.val.val ∈ W ↔ ((overlapBaseEquiv hOU hOV x).val).val ∈ W
    rw [overlapBaseEquiv_point]
  have hSA := hSP.restrict UO
  have hSB : NativeHSState B ((Subtype.val : UO → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' W)) H := by
    rw [hEq]
    exact (hSQ.restrict VO).pullback φ
  have hCanA := Seq.ResolutionInvariantExt.isCanonical_restrict (invFamily hn k) hP UO TP hCanP
  have hCanR := Seq.ResolutionInvariantExt.isCanonical_restrict (invFamily hn k) hQ VO TQ hCanQ
  have hResA := MarkedIdealRestrictOpen.isGeoResolution_restrict UO
    hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent hResP
  have hResR := MarkedIdealRestrictOpen.isGeoResolution_restrict VO
    hQ.isWellFormed.isClosedSubmanifold_N hQ.isWellFormed.isCoherent hResQ
  have hCanB := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso (invFamily hn k)
    hR φ (transport_isTowerIso φ T) hCanR
  have hResB := (isGeoResolution_transport_iff φ hR.isWellFormed.isCoherent T).mpr hResR
  obtain ⟨η, hη⟩ := native_terminal_emptyAware_of_common_boundary hn B A hB hA hSB hSA
    hBoundary.symm (by
      intro D hD x hx hxD
      apply hNot D (hBoundary.symm ▸ hD) x ?_ hxD
      rw [hSA.cosupp_eq, ← hSB.cosupp_eq]
      exact hx) (transport φ T).tower S hCanB hCanA hResB hResA
  refine ⟨η.trans (transport φ T).back, ?_⟩
  simpa only [Diffeomorph.refl_trans] using
    HironakaG3EmptyAwareComposition.trans hη (emptyAware_of_isTowerIso (transport_isTowerIso φ T))

end
end Hironaka.HironakaG8FullBoundaryTerminalOverlap
