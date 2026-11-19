import Hironaka.Resolution.HironakaG4PaddedProcessedMaskHistory
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareJoin

/-! The physical comparison of two independently padded processed
histories uses their common projected sequence of live masks. -/

set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4PairedProcessedMaskHistory

noncomputable section

open Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaSharpActualFiniteChronologicalHistory
  HironakaG4OrderedProcessedMaskHistory HironakaG4ProcessedMaskFilteredPrefix
  HironakaG4PaddedProcessedMaskHistory HironakaG3EmptyAwareHistory

variable {n : ℕ} {X X' Y Y' : CMfd.{u} n} {ι κ μ : Type v}

private inductive PhaseAlignment (f : ι → Option μ) (g : κ → Option μ) :
    List ι → List κ → Prop
  | nil : PhaseAlignment f g [] []
  | skipFirst {L : List ι} {L' : List κ} (a : ι)
      (h : f a = none) (hL : PhaseAlignment f g L L') : PhaseAlignment f g (a :: L) L'
  | skipSecond {L : List ι} {L' : List κ} (b : κ)
      (h : g b = none) (hL : PhaseAlignment f g L L') : PhaseAlignment f g L (b :: L')
  | pair {L : List ι} {L' : List κ} (a : ι) (b : κ) (c : μ)
      (ha : f a = some c) (hb : g b = some c) (hL : PhaseAlignment f g L L') :
      PhaseAlignment f g (a :: L) (b :: L')

private theorem phaseAlignment_of_filterMap_eq (f : ι → Option μ) (g : κ → Option μ)
    (L : List ι) (L' : List κ) (h : L.filterMap f = L'.filterMap g) :
    PhaseAlignment f g L L' := by
  induction L generalizing L' with
  | nil =>
    induction L' with
    | nil => exact .nil
    | cons b L' ih =>
      cases hb : g b with
      | none =>
        rw [List.filterMap_cons_none hb] at h
        exact .skipSecond b hb (ih h)
      | some c =>
        simp [List.filterMap_cons_some hb] at h
  | cons a L ih =>
    cases ha : f a with
    | none =>
      rw [List.filterMap_cons_none ha] at h
      exact .skipFirst a ha (ih L' h)
    | some c =>
      induction L' with
      | nil =>
        simp [List.filterMap_cons_some ha] at h
      | cons b L' ih' =>
        cases hb : g b with
        | none =>
          rw [List.filterMap_cons_none hb] at h
          exact .skipSecond b hb (ih' h)
        | some c' =>
          rw [List.filterMap_cons_some ha,List.filterMap_cons_some hb] at h
          obtain ⟨rfl,hTail⟩ := List.cons.inj h
          exact .pair a b c ha hb (ih L' hTail)

set_option maxHeartbeats 1400000 in
/-- Compare the same two actual appended towers while each old list
contains its own absent rows. Common labels compare their canonical
phases and each unilateral absent phase consists of empty blowups. -/
theorem paired_processed_histories_emptyAware (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (E' : List (Set X')) (hE' : IsSNCDivisor n E')
    (hdense' : φ ⁻¹' W ⊆ closure (φ ⁻¹' W \ ⋃ H ∈ E',H))
    (T : BlowupTower X Y) (T' : BlowupTower X' Y')
    {ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hIso : EmptyAwareTowerIso φ T' T ψ)
    (e : μ ↪ Fin E.length) (e' : μ ↪ Fin E'.length)
    (hSlots : ∀ i,E'.get (e' i) = φ ⁻¹' E.get (e i))
    (mask : ι → Finset (Fin E.length)) (mask' : κ → Finset (Fin E'.length))
    (active : ι → Option (Finset μ)) (active' : κ → Option (Finset μ))
    (hMode : ∀ a, match active a with
      | some P => mask a = P.map e
      | none => ∃ i ∈ mask a,E.get i = ∅)
    (hMode' : ∀ b, match active' b with
      | some P => mask' b = P.map e'
      | none => ∃ i ∈ mask' b,E'.get i = ∅)
    (L : List ι) (L' : List κ) (hSame : L.filterMap active = L'.filterMap active') :
    ∀ {Z Z' : CMfd.{u} n} (Q : BlowupTower Y Z) (Q' : BlowupTower Y' Z'),
      IsGeoTestTower (geometricTemplate W []) (T.append Q) →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) →
      IsGeoTestTower (geometricTemplate (φ ⁻¹' W) []) (T'.append Q') →
      IsGeoTestTower (geometricTemplate (univ : Set X') E') (T'.append Q') →
      OrderedProcessedMaskHistory hn W E T mask Q L →
      OrderedProcessedMaskHistory hn (φ ⁻¹' W) E' T' mask' Q' L' →
      ∃ χ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
        EmptyAwareTowerIso φ (T'.append Q') (T.append Q) χ := by
  have hW' := (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff φ).mpr hW
  have hAlign := phaseAlignment_of_filterMap_eq active active' L L' hSame
  clear hSame
  induction hAlign with
  | nil =>
    intro Z Z' Q Q' _hTest _hFull _hTest' _hFull' hQ hQ'
    cases hQ
    cases hQ'
    exact ⟨ψ,hIso⟩
  | skipFirst a ha _ ih =>
    intro Z Z' Q Q' hTest hFull hTest' hFull' hQ hQ'
    cases hQ with
    | @snoc A Z P _ _ S hPrev hBlock =>
      rw [←BlowupTower.append_assoc] at hTest hFull
      have hPrevTest := ((isGeoTestTower_append_iff _ _ S).mp hTest).1
      have hPrevFull := ((isGeoTestTower_append_iff _ _ S).mp hFull).1
      obtain ⟨χ,hχ⟩ := ih P Q' hPrevTest hPrevFull hTest' hFull' hPrev hQ'
      have h := hMode a
      rw [ha] at h
      obtain ⟨σ,hσ⟩ := append_absent_mask_emptyAware hn hW hE hdense
        (T.append P) hPrevTest hPrevFull (mask a) h S hBlock.1 hBlock.2.1 hBlock.2.2.1
      exact ⟨χ.trans σ.symm,by
        simpa only [BlowupTower.append_assoc,Diffeomorph.symm_refl,Diffeomorph.trans_refl]
          using G3UniverseEmptyAwareCore.trans hχ (G3UniverseEmptyAwareCore.symm hσ)⟩
  | skipSecond b hb _ ih =>
    intro Z Z' Q Q' hTest hFull hTest' hFull' hQ hQ'
    cases hQ' with
    | @snoc A' Z' P' _ _ S' hPrev' hBlock' =>
      rw [←BlowupTower.append_assoc] at hTest' hFull'
      have hPrevTest' := ((isGeoTestTower_append_iff _ _ S').mp hTest').1
      have hPrevFull' := ((isGeoTestTower_append_iff _ _ S').mp hFull').1
      obtain ⟨χ,hχ⟩ := ih Q P' hTest hFull hPrevTest' hPrevFull' hQ hPrev'
      have h := hMode' b
      rw [hb] at h
      obtain ⟨σ,hσ⟩ := append_absent_mask_emptyAware hn hW' hE' hdense'
        (T'.append P') hPrevTest' hPrevFull' (mask' b) h S' hBlock'.1 hBlock'.2.1 hBlock'.2.2.1
      exact ⟨σ.trans χ,by simpa only [BlowupTower.append_assoc,Diffeomorph.refl_trans]
        using G3UniverseEmptyAwareCore.trans hσ hχ⟩
  | pair a b P ha hb _ ih =>
    intro Z Z' Q Q' hTest hFull hTest' hFull' hQ hQ'
    cases hQ with
    | snoc _ S hPrev hBlock =>
      cases hQ' with
      | snoc _ S' hPrev' hBlock' =>
        rw [←BlowupTower.append_assoc] at hTest hFull hTest' hFull'
        have hPrevTest := ((isGeoTestTower_append_iff _ _ S).mp hTest).1
        have hPrevFull := ((isGeoTestTower_append_iff _ _ S).mp hFull).1
        have hPrevTest' := ((isGeoTestTower_append_iff _ _ S').mp hTest').1
        have hPrevFull' := ((isGeoTestTower_append_iff _ _ S').mp hFull').1
        obtain ⟨χ,hχ⟩ := ih _ _ hPrevTest hPrevFull hPrevTest' hPrevFull' hPrev hPrev'
        have hA := hMode a
        have hB := hMode' b
        rw [ha] at hA
        rw [hb] at hB
        dsimp only at hBlock hBlock'
        rw [hA] at hBlock
        rw [hB] at hBlock'
        simpa only [BlowupTower.append_assoc] using
          processed_mask_append_emptyAware_of_two_row_embeddings hn hW hE hdense _
            hPrevTest hPrevFull hχ E' e e' hSlots P S' S
            hBlock.1 hBlock'.2.1 hBlock.2.1 hBlock'.2.2 hBlock.2.2

end
end Hironaka.HironakaG4PairedProcessedMaskHistory
