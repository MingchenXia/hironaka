import Hironaka.Resolution.HironakaG8NativeHSSegmentTowerComparison
import Hironaka.Resolution.HironakaOriginalFiniteEmptyCompression
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8NativeHSEmptyFreeTowerComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres ResolutionDriver
  HironakaStageCenters HironakaG11PresLineState HironakaG8NativeHSSegmentTowerComparison
  HironakaOriginalFiniteEmptyCompression

/-- A canonical tower with every centre nonempty is a canonical segment. -/
theorem segment_of_canonical_of_nonempty_centres {n : ℕ} {X : CMfd.{0} n}
    {Λ : Type} [LinearOrder Λ] (P : MarkedIdeal n X)
    (f : ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun _ C => C.Nonempty) T → IsCanonical P f T → IsCanonicalSegment P f T
  | _, .refl, _, _ => trivial
  | _, .step T C π hπ, hNE, hC => by
    exact ⟨segment_of_canonical_of_nonempty_centres P f T hNE.1 hC.1,hNE.2,
      hC.2.resolve_left (fun h => hNE.2.ne_empty h)⟩

/-- Independently supplied native terminal towers, with arbitrary empty steps,
have empty-free canonical compressions that are isomorphic as entire towers. -/
theorem native_hs_terminal_towers_have_common_compression {n k : ℕ} (hn : 0<n)
    {X Y Z : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (hEP : P.E = []) (hEQ : Q.E = [])
    {W : Set X} {H : ℕ → ℕ} (hSP : NativeHSState P W H) (hSQ : NativeHSState Q W H)
    (TP : BlowupTower X Y) (TQ : BlowupTower X Z)
    (hCanP : IsCanonical P ((invFamily hn k).inv P) TP)
    (hCanQ : IsCanonical Q ((invFamily hn k).inv Q) TQ)
    (hResP : IsGeoResolution P TP) (hResQ : IsGeoResolution Q TQ) :
    ∃ (Y' Z' : CMfd.{0} n) (SP : BlowupTower X Y') (SQ : BlowupTower X Z')
      (eP : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
      (eQ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z)
      (e : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y'),
        IsCanonicalSegment P ((invFamily hn k).inv P) SP ∧ IsGeoResolution P SP ∧
        IsCanonicalSegment Q ((invFamily hn k).inv Q) SQ ∧ IsGeoResolution Q SQ ∧
        (∀ y, TP.proj (eP y) = SP.proj y) ∧ (∀ z, TQ.proj (eQ z) = SQ.proj z) ∧
        IsTowerIso (Diffeomorph.refl _ _ _) SQ SP e := by
  obtain ⟨Y',SP,eP,_,hNEP,_,hCanP',hProjP,_,_,hResP'⟩ :=
    original_recursive_family_empty_free_compression hn k P hP TP hCanP
  obtain ⟨Z',SQ,eQ,_,hNEQ,_,hCanQ',hProjQ,_,_,hResQ'⟩ :=
    original_recursive_family_empty_free_compression hn k Q hQ TQ hCanQ
  have hSegP := segment_of_canonical_of_nonempty_centres P ((invFamily hn k).inv P) SP hNEP hCanP'
  have hSegQ := segment_of_canonical_of_nonempty_centres Q ((invFamily hn k).inv Q) SQ hNEQ hCanQ'
  have hRP := hResP'.mp hResP
  have hRQ := hResQ'.mp hResQ
  obtain ⟨e,he⟩ := native_hs_independent_terminal_segments_tower_iso hn P Q hP hQ hEP hEQ hSP hSQ
    SP SQ hSegP hSegQ hRP hRQ
  exact ⟨Y',Z',SP,SQ,eP,eQ,e,hSegP,hRP,hSegQ,hRQ,hProjP,hProjQ,he⟩
end
end Hironaka.HironakaG8NativeHSEmptyFreeTowerComparison
