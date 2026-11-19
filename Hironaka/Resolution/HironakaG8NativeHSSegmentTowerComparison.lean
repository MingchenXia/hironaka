import Hironaka.Resolution.HironakaG8NativeHSIndependentTerminal
import Hironaka.Resolution.HironakaG11InvTransport
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8NativeHSSegmentTowerComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres ResolutionDriver
  ResolutionInvariantDriver HironakaG11InvTransport MarkedIdealOperationsAlong.MarkedIdeal
  HironakaG8LocalHistory HironakaG11InvBMClass DivisorExponentAlong
  HironakaG11PresLineState HironakaG11PresLineStable HironakaG1OriginalUnequalMarkCanonical

/-- A canonical history is a nonempty segment when the same literal tower
already is such a segment for another record and invariant. -/
theorem segment_of_canonical_of_segment {n : ℕ} {X : CMfd.{0} n}
    {Λ Λ' : Type} [LinearOrder Λ] [LinearOrder Λ'] (P Q : MarkedIdeal n X)
    (f : ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ)
    (g : ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ') :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      IsCanonicalSegment P f T → IsCanonical Q g T → IsCanonicalSegment Q g T
  | _, .refl, _, _ => trivial
  | _, .step T C π hπ, hS, hC => by
    refine ⟨segment_of_canonical_of_segment P Q f g T hS.1 hC.1,hS.2.1,?_⟩
    exact hC.2.resolve_left (fun h => hS.2.1.ne_empty h)

/-- Independent resolving native HS canonical segments on the same ambient
are isomorphic as entire blowup towers, not only at their final spaces. -/
theorem native_hs_independent_terminal_segments_tower_iso {n k : ℕ} (hn : 0<n)
    {X Y Z : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (hEP : P.E = []) (hEQ : Q.E = [])
    {W : Set X} {H : ℕ → ℕ} (hSP : NativeHSState P W H) (hSQ : NativeHSState Q W H)
    (TP : BlowupTower X Y) (TQ : BlowupTower X Z)
    (hSegP : IsCanonicalSegment P ((invFamily hn k).inv P) TP)
    (hSegQ : IsCanonicalSegment Q ((invFamily hn k).inv Q) TQ)
    (hResP : IsGeoResolution P TP) (hResQ : IsGeoResolution Q TQ) :
    ∃ η : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      IsTowerIso (Diffeomorph.refl _ _ _) TQ TP η := by
  have hL := locWPEquiv_native hSP hSQ (hEQ.trans hEP.symm)
  have hD := SameCarrierDim.of_N_eq (hSP.2.2.1.trans hSQ.2.2.1.symm)
  have hI : ∀ D ∈ P.E, ∀ x ∈ P.cosupp, x ∈ D →
      Q.d * divExpAlong n P.N P.ideal D x = P.d * divExpAlong n Q.N Q.ideal D x := by
    intro D hD; rw [hEP] at hD; exact (List.not_mem_nil hD).elim
  have hCanQ := isCanonical_of_isCanonicalSegment ((invFamily hn k).inv Q) TQ hSegQ
  have hCanQP := (invFamily_isCanonical_iff_of_local hn P Q hP hQ hL hD hI TQ).mpr hCanQ
  have hSegQP := segment_of_canonical_of_segment Q P ((invFamily hn k).inv Q)
    ((invFamily hn k).inv P) TQ hSegQ hCanQP
  have hT : IsGeoTestTower P TQ := (hL.wEquiv.2 TQ).1.mpr hResQ.1
  have hResQP : IsGeoResolution P TQ := by
    refine ⟨hT, ?_⟩
    rw [(hL.wEquiv.2 TQ).2 hT, hResQ.2]
  let e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X := Diffeomorph.refl _ _ _
  have he : MarkedIdeal.pullback e P = P := by
    change MarkedIdeal.pullback id P = P
    exact ContactCanonicalAlong.pullback_id P hP.isWellFormed.isCoherent
  have hEq : RestrictEquiv (MarkedIdeal.pullback e P) P := by
    rw [he]
    exact RestrictEquiv.refl hP.isWellFormed.isCoherent
  exact resolving_canonicalSegments_isTowerIso (invFamily hn k) e hP hP hEq TQ TP hSegQP hSegP hResQP hResP
end
end Hironaka.HironakaG8NativeHSSegmentTowerComparison
