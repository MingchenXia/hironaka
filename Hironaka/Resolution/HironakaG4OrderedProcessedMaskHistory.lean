import Hironaka.Resolution.HironakaG4NativeProcessedMaskReindex
import Hironaka.Resolution.HironakaG4ProcessedMaskFilteredPrefix

/-! A prescribed list of original mask labels supports an actual physical
comparison of the appended original histories, phase by phase. -/

set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4OrderedProcessedMaskHistory

noncomputable section

open Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings HironakaG3EmptyAwareHistory HironakaG4ProcessedMaskFilteredPrefix
  HironakaActualProcessedMaskControlledSum HironakaG4CompactWholeMonomialMaskPhase
  HironakaG4NativeProcessedMaskReindex HironakaG4ZeroMaskFixedQFold
  HironakaG4ZeroMaskSameGammaHistory HomogenizedGlueingTower CanonicalCentres
  HironakaSharpActualFiniteChronologicalHistory
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X X' Y Y' A : CMfd.{u} n} {ι : Type v}

private theorem nativeMaskMarked_congr {N N' : Set Y} {O O' B B' : List (Set Y)}
    {P : Finset (Fin O.length)} {P' : Finset (Fin O'.length)}
    (hN : N = N') (hO : O = O') (hB : B = B')
    (hP : P.map (finCongr (congrArg List.length hO)).toEmbedding = P') :
    nativeMaskMarked N O B P = nativeMaskMarked N' O' B' P' := by
  subst N' O' B'
  simpa using congrArg (nativeMaskMarked N O B) hP

/-- The native mask obtained after another actual phase is exactly the
recomputed original mask on the appended original prefix. -/
theorem current_native_mask_eq_original (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) (Q : BlowupTower Y A) (P : Finset (Fin E.length)) :
    let N := strictAlong T W
    let O := E.map (strictAlong T)
    let B := (geoTransformAlong (geometricTemplate W []) T).E
    currentNativeMask N O B Q (P.map (oldEquiv E T).toEmbedding) =
      processedMaskMarked W E (T.append Q) P := by
  intro N O B
  let e := oldEquiv E T
  let R := T.append Q
  let eR := oldEquiv E R
  let PR := P.map eR.toEmbedding
  have hR := (native_processed_mask_eq (W := W) E R PR).2
  change processedMaskMarked W E R (PR.map eR.symm.toEmbedding) =
    nativeMaskMarked (strictAlong R W) (E.map (strictAlong R))
      (geoTransformAlong (geometricTemplate W []) R).E PR at hR
  have hOrig : processedMaskMarked W E R P =
      nativeMaskMarked (strictAlong R W) (E.map (strictAlong R))
        (geoTransformAlong (geometricTemplate W []) R).E PR := by
    simpa [PR,Finset.map_map] using hR
  rw [hOrig]
  have hN : strictAlong Q N = strictAlong R W :=
    (MemberInterLocusAlong.strictAlong_append T W Q).symm
  have hO : O.map (strictAlong Q) = E.map (strictAlong R) := by
    rw [show O = E.map (strictAlong T) from rfl,List.map_map]
    congr 1
    funext H
    exact (MemberInterLocusAlong.strictAlong_append T H Q).symm
  have hB : (geoTransformAlong (geometricTemplate N B) Q).E =
      (geoTransformAlong (geometricTemplate W []) R).E := by
    unfold R
    rw [geoTransformAlong_append,
      show geoTransformAlong (geometricTemplate W []) T = geometricTemplate N B from template_current W [] T]
  have hP : (((P.map e.toEmbedding).map (oldEquiv O Q).toEmbedding).map
      (finCongr (congrArg List.length hO)).toEmbedding) = PR := by
    unfold PR
    rw [Finset.map_map,Finset.map_map]
    congr 1
  exact nativeMaskMarked_congr hN hO hB hP

/-- A label records an actual terminal canonical phase of the corresponding
original mask. A new phase appends to the tower and prepends its label. -/
inductive OrderedProcessedMaskHistory (hn : 0 < n) (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) (mask : ι → Finset (Fin E.length)) :
    {Z : CMfd.{u} n} → BlowupTower Y Z → List ι → Prop
  | nil : OrderedProcessedMaskHistory hn W E T mask (.refl : BlowupTower Y Y) []
  | snoc {A Z : CMfd.{u} n} {Q : BlowupTower Y A} {L : List ι}
      (label : ι) (S : BlowupTower A Z)
      (hQ : OrderedProcessedMaskHistory hn W E T mask Q L)
      (hS : let M := processedMaskMarked W E (T.append Q) (mask label)
        IsInvDomain (n+1) M ∧ IsCanonical M ((invFamily hn (n+1)).inv M) S ∧
          IsGeoResolution M S) :
      OrderedProcessedMaskHistory hn W E T mask (Q.append S) (label :: L)

/-- Native zero-residual labels are read on the same original appended
history using the original chronological row positions. -/
theorem native_history_to_ordered_processed (hn : 0 < n) (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) (mask : ι → Finset (Fin E.length)) :
    ∀ (L : List ι) {Z : CMfd.{u} n} (Q : BlowupTower Y Z),
      let N := strictAlong T W
      let O := E.map (strictAlong T)
      let B := (geoTransformAlong (geometricTemplate W []) T).E
      OrderedNativeMaskHistory hn N O B Q (L.map (fun a => (mask a).map (oldEquiv E T).toEmbedding)) →
      OrderedProcessedMaskHistory hn W E T mask Q L := by
  dsimp only
  intro L
  induction L with
  | nil =>
    intro Z Q hQ
    cases hQ
    exact .nil
  | cons label L ih =>
    intro Z Q hQ
    cases hQ with
    | snoc _ S hPrev hBlock =>
      apply OrderedProcessedMaskHistory.snoc label S (ih _ hPrev)
      dsimp only at hBlock
      rw [current_native_mask_eq_original] at hBlock
      exact hBlock

set_option maxHeartbeats 650000 in
/-- Two original processed histories with the same chronological mask
choices align on the nose as physical towers up to empty blowup stages. -/
theorem ordered_processed_histories_emptyAware (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X}
    (T : BlowupTower X Y) (T' : BlowupTower X' Y')
    {ψ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : EmptyAwareTowerIso φ T' T ψ) (mask : ι → Finset (Fin E.length)) :
    ∀ (L : List ι) {Z Z' : CMfd.{u} n} (Q : BlowupTower Y Z) (Q' : BlowupTower Y' Z'),
      let E' := E.map (φ ⁻¹' ·)
      let e : Fin E.length ≃ Fin E'.length := finCongr (List.length_map _).symm
      IsGeoTestTower (geometricTemplate W []) (T.append Q) →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) →
      OrderedProcessedMaskHistory hn W E T mask Q L →
      OrderedProcessedMaskHistory hn (φ ⁻¹' W) E' T' (fun a => (mask a).map e.toEmbedding) Q' L →
      ∃ χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Z,
        EmptyAwareTowerIso φ (T'.append Q') (T.append Q) χ := by
  dsimp only
  intro L
  induction L with
  | nil =>
    intro Z Z' Q Q' _hQTest _hQFull hQ hQ'
    cases hQ
    cases hQ'
    exact ⟨ψ,hIso⟩
  | cons label L ih =>
    intro Z Z' Q Q' hQTest hQFull hQ hQ'
    cases hQ with
    | snoc _ S hPrev hBlock =>
      cases hQ' with
      | snoc _ S' hPrev' hBlock' =>
        rw [←BlowupTower.append_assoc] at hQTest hQFull
        have hPrevTest := ((isGeoTestTower_append_iff _ _ S).mp hQTest).1
        have hPrevFull := ((isGeoTestTower_append_iff _ _ S).mp hQFull).1
        obtain ⟨χ,hχ⟩ := ih _ _ hPrevTest hPrevFull hPrev hPrev'
        simpa only [BlowupTower.append_assoc] using
          processed_mask_append_emptyAware hn hW hE hdense _ hPrevTest hPrevFull hχ
            (mask label) S' S hBlock.1 hBlock'.2.1 hBlock.2.1 hBlock'.2.2 hBlock.2.2

end
end Hironaka.HironakaG4OrderedProcessedMaskHistory
