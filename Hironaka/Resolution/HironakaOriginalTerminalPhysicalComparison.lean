import Hironaka.Resolution.HironakaOriginalTerminalChoiceComparison
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareAlgebra
import Hironaka.Resolution.HironakaG8DisjointPhaseMerge

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalTerminalPhysicalComparison

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism CanonicalCentres
  HironakaStageCenters HironakaOriginalTerminalChoiceComparison HironakaOriginalFiniteEmptyCompression
  HironakaOriginalActualEmptyNormalization HironakaOriginalInteriorEmptyHistory G3UniverseEmptyAwareCore
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- Compress a terminal original-family history, preserving its actual stage comparison. -/
theorem original_family_terminal_physical_compression {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{u} n} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (T : BlowupTower X Y) (hCan : IsCanonical M ((invFamily hn k).inv M) T)
    (hRes : IsGeoResolution M T) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower X Z)
      (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y),
      StageCentres (fun _ C => C.Nonempty) Q ∧ Q.length ≤ T.length ∧
      IsCanonical M ((invFamily hn k).inv M) Q ∧ IsGeoResolution M Q ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) Q T χ := by
  classical
  generalize hlen : T.length = length
  induction length using Nat.strong_induction_on generalizing Y with
  | h length ih =>
    by_cases hNonempty : StageCentres (fun _ C => C.Nonempty) T
    · exact ⟨Y,T,Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞,hNonempty,hlen.le,hCan,hRes,
        emptyAware_of_isTowerIso (IsTowerIso.refl_self T)⟩
    obtain ⟨A,B,H,π,hπ,S,hSplit⟩ := exists_actual_empty_step_split T hNonempty
    subst T
    obtain ⟨Y',S',χD,hLength,hIso,hCanD,_,_,hResIff⟩ :=
      original_recursive_family_actual_empty_deletion hn k M hM H π hπ S hCan
    have hShort : (H.append S').length < length := by
      rw [BlowupTower.length_append,hLength]
      rw [BlowupTower.length_append] at hlen
      change H.length + 1 + S.length = length at hlen
      omega
    obtain ⟨Z,Q,χ,hQ,hLengthQ,hCanQ,hResQ,hCompare⟩ :=
      ih _ hShort (H.append S') hCanD (hResIff.mp hRes) rfl
    have hInsert : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        H (H.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty)
        (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞) := by
      simpa only [Diffeomorph.symm_refl,Diffeomorph.refl_trans] using
        (EmptyAwareTowerIso.rightEmpty (emptyAware_of_isTowerIso (IsTowerIso.refl_self H))
          BlowupExistenceCodimOne.isBlowupAlong_id_empty
          (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞) (fun _ => rfl))
    have hAligned : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        (H.append S') (interiorEmptyHistory H S') (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y' ∞) :=
      HironakaG8DisjointPhaseMerge.emptyAware_append hInsert (emptyAware_of_isTowerIso (IsTowerIso.refl_self S'))
    have hDelete : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        (H.append S') ((H.step ∅ π hπ).append S) χD := by
      simpa only [Diffeomorph.refl_trans] using G3UniverseEmptyAwareCore.trans hAligned (emptyAware_of_isTowerIso hIso)
    refine ⟨Z,Q,χ.trans χD,hQ,hLengthQ.trans hShort.le,hCanQ,hResQ,?_⟩
    simpa only [Diffeomorph.refl_trans] using G3UniverseEmptyAwareCore.trans hCompare hDelete

/-- Terminal histories of a marked record and its literal pullback have an actual empty-aware comparison. -/
theorem original_terminal_histories_emptyAware_over_pullback {n k : ℕ} (hn : 0 < n)
    {X X' Y Y' : CMfd.{u} n} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (T' : BlowupTower X' Y') (T : BlowupTower X Y)
    (hCan' : IsCanonical (MarkedIdeal.pullback Φ M)
      ((invFamily hn k).inv (MarkedIdeal.pullback Φ M)) T')
    (hCan : IsCanonical M ((invFamily hn k).inv M) T)
    (hRes' : IsGeoResolution (MarkedIdeal.pullback Φ M) T') (hRes : IsGeoResolution M T) :
    ∃ η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y, EmptyAwareTowerIso Φ T' T η := by
  have hM' := InvDomainTowerAlong.isInvDomain_pullback Φ hM
  obtain ⟨Z',Q',χ',hNonempty',_,hCanQ',hResQ',hCompare'⟩ :=
    original_family_terminal_physical_compression hn (MarkedIdeal.pullback Φ M) hM' T' hCan' hRes'
  obtain ⟨Z,Q,χ,hNonempty,_,hCanQ,hResQ,hCompare⟩ :=
    original_family_terminal_physical_compression hn M hM T hCan hRes
  have hSeg' := isCanonicalSegment_of_actual_nonempty_centres (MarkedIdeal.pullback Φ M)
    ((invFamily hn k).inv (MarkedIdeal.pullback Φ M)) Q' hCanQ' hNonempty'
  have hSeg := isCanonicalSegment_of_actual_nonempty_centres M ((invFamily hn k).inv M) Q hCanQ hNonempty
  obtain ⟨ψ,hIso⟩ := CanonicalResolution.exists_isTowerIso_of_isGeoResolution
    (invFamily hn k) hM Φ Q' Q hSeg' hSeg hResQ' hResQ
  refine ⟨χ'.symm.trans (ψ.trans χ),?_⟩
  simpa only [Diffeomorph.symm_refl,Diffeomorph.refl_trans,Diffeomorph.trans_refl] using
    G3UniverseEmptyAwareCore.trans (G3UniverseEmptyAwareCore.symm hCompare')
      (G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso hIso) hCompare)

/-- Two terminal canonical histories of the same literal record compare on their common ambient. -/
theorem original_terminal_histories_emptyAware_same_record {n k : ℕ} (hn : 0 < n)
    {X Y Y' : CMfd.{u} n} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (T' : BlowupTower X Y') (T : BlowupTower X Y)
    (hCan' : IsCanonical M ((invFamily hn k).inv M) T')
    (hCan : IsCanonical M ((invFamily hn k).inv M) T)
    (hRes' : IsGeoResolution M T') (hRes : IsGeoResolution M T) :
    ∃ η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T' T η := by
  let Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  have hPull : MarkedIdeal.pullback Φ M = M := ContactCanonicalAlong.pullback_id M hM.isWellFormed.isCoherent
  exact original_terminal_histories_emptyAware_over_pullback hn M hM Φ T' T
    (by rw [hPull]; exact hCan') hCan (by rw [hPull]; exact hRes') hRes

end
end Hironaka.HironakaOriginalTerminalPhysicalComparison
