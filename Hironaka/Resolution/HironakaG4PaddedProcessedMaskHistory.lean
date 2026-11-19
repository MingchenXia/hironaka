import Hironaka.Resolution.HironakaG4EmptyOldMaskPhase
import Hironaka.Resolution.HironakaG3AppendEmptyTailComparison

/-! Empty old slots can add labels to an ordered mask history without
changing the physical comparison of the genuinely matched phases. -/

set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4PaddedProcessedMaskHistory

noncomputable section

open Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaActualProcessedMaskControlledSum
  HironakaG4OrderedProcessedMaskHistory HironakaG4ProcessedMaskFilteredPrefix
  HironakaG4EmptyOldMaskPhase HironakaG3EmptyAwareHistory HironakaG3AppendEmptyTailComparison
open ResolutionInvariantSpec (IsCanonical IsInvDomain)
open CanonicalCentres
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X X' Y Y' : CMfd.{u} n} {ι κ : Type v}

private theorem empty_tower_of_empty_canonical {Λ : Type v} [LinearOrder Λ]
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hEmpty : M.cosupp = ∅)
    (inv : ∀ {A : CMfd.{u} n}, BlowupTower X A → A → Λ) :
    ∀ {A : CMfd.{u} n} (T : BlowupTower X A), IsGeoTestTower M T →
      IsCanonical M inv T → IsEmptyTower T
  | _,.refl,_,_ => trivial
  | _,.step T C π hπ,hTest,hCan => by
    have hTest₀ := ((isGeoTestTower_step_iff M T C π hπ).mp hTest).1
    refine ⟨empty_tower_of_empty_canonical M hM hEmpty inv T hTest₀ hCan.1,?_⟩
    rcases hCan.2 with hC | hC
    · exact hC
    · apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      rw [hC] at hx
      have hx' := TransformOffCentre.cosupp_geoTransformAlong_subset M
        hM.isClosedSubmanifold_N hM.isCoherent T hTest₀ hx.1
      rw [hEmpty,preimage_empty] at hx'
      exact notMem_empty _ hx'

/-- A resolving phase for a mask selecting an absent old row compares to
the reflexive extension of precisely the same original prefix. -/
theorem append_absent_mask_emptyAware (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hTest : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (P : Finset (Fin E.length)) (hAbsent : ∃ i ∈ P,E.get i = ∅)
    {Z : CMfd.{u} n} (S : BlowupTower Y Z) :
    let M := processedMaskMarked W E T P
    IsInvDomain (n+1) M → IsCanonical M ((invFamily hn (n+1)).inv M) S → IsGeoTestTower M S →
    ∃ χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) (T.append S) T χ := by
  intro M hDom hCan hS
  obtain ⟨i,hi,hEmpty⟩ := hAbsent
  have hCos : M.cosupp = ∅ := processed_mask_cosupp_eq_empty_of_empty_old_row
    hn hW hE hdense T hTest hFull hi hEmpty
  exact emptyAware_append_empty_tail T S
    (empty_tower_of_empty_canonical M hDom.isWellFormed hCos _ S hS hCan)

set_option maxHeartbeats 1000000 in
/-- Follow the common active phases of two actual ordered histories, skipping
a label on the larger old list only when its mask contains a literally
empty old row. The smaller history must be the indicated projection of
the larger label schedule. -/
theorem padded_processed_histories_emptyAware (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (E' : List (Set X')) (hE' : IsSNCDivisor n E')
    (hdense' : φ ⁻¹' W ⊆ closure (φ ⁻¹' W \ ⋃ H ∈ E',H))
    (T : BlowupTower X Y) (T' : BlowupTower X' Y')
    {ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hIso : EmptyAwareTowerIso φ T' T ψ)
    (e : Fin E.length ↪ Fin E'.length) (hSlots : ∀ i, E'.get (e i) = φ ⁻¹' E.get i)
    (mask : ι → Finset (Fin E.length)) (mask' : κ → Finset (Fin E'.length))
    (active : κ → Option ι)
    (hAlign : ∀ b, match active b with
      | some a => mask' b = (mask a).map e
      | none => ∃ i ∈ mask' b, E'.get i = ∅) :
    ∀ (L' : List κ) {Z Z' : CMfd.{u} n} (Q : BlowupTower Y Z) (Q' : BlowupTower Y' Z'),
      IsGeoTestTower (geometricTemplate W []) (T.append Q) →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) →
      IsGeoTestTower (geometricTemplate (φ ⁻¹' W) []) (T'.append Q') →
      IsGeoTestTower (geometricTemplate (univ : Set X') E') (T'.append Q') →
      OrderedProcessedMaskHistory hn W E T mask Q (L'.filterMap active) →
      OrderedProcessedMaskHistory hn (φ ⁻¹' W) E' T' mask' Q' L' →
      ∃ χ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
        EmptyAwareTowerIso φ (T'.append Q') (T.append Q) χ := by
  have hW' := (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff φ).mpr hW
  intro L'
  induction L' with
  | nil =>
    intro Z Z' Q Q' _hTest _hFull _hTest' _hFull' hQ hQ'
    cases hQ
    cases hQ'
    exact ⟨ψ,hIso⟩
  | cons label L' ih =>
    intro Z Z' Q Q' hTest hFull hTest' hFull' hQ hQ'
    cases hQ' with
    | @snoc A' Z' P' _ _ S' hPrev' hBlock' =>
      rw [←BlowupTower.append_assoc] at hTest' hFull'
      have hPrevTest' := ((isGeoTestTower_append_iff _ _ S').mp hTest').1
      have hPrevFull' := ((isGeoTestTower_append_iff _ _ S').mp hFull').1
      have hLabel := hAlign label
      cases ha : active label with
      | none =>
        have hRight : OrderedProcessedMaskHistory hn W E T mask Q (L'.filterMap active) := by
          simpa only [List.filterMap_cons_none ha] using hQ
        rw [ha] at hLabel
        obtain ⟨χ,hχ⟩ := ih Q P' hTest hFull hPrevTest' hPrevFull' hRight hPrev'
        obtain ⟨σ,hσ⟩ := append_absent_mask_emptyAware hn hW' hE' hdense'
          (T'.append P') hPrevTest' hPrevFull' (mask' label) hLabel S'
          hBlock'.1 hBlock'.2.1 hBlock'.2.2.1
        exact ⟨σ.trans χ,by simpa only [BlowupTower.append_assoc,Diffeomorph.refl_trans]
          using G3UniverseEmptyAwareCore.trans hσ hχ⟩
      | some a =>
        have hRight : OrderedProcessedMaskHistory hn W E T mask Q (a :: L'.filterMap active) := by
          simpa only [List.filterMap_cons_some ha] using hQ
        cases hRight with
        | snoc _ S hPrev hBlock =>
          rw [←BlowupTower.append_assoc] at hTest hFull
          have hPrevTest := ((isGeoTestTower_append_iff _ _ S).mp hTest).1
          have hPrevFull := ((isGeoTestTower_append_iff _ _ S).mp hFull).1
          obtain ⟨χ,hχ⟩ := ih _ P' hPrevTest hPrevFull hPrevTest' hPrevFull' hPrev hPrev'
          rw [ha] at hLabel
          dsimp only at hBlock'
          rw [hLabel] at hBlock'
          simpa only [BlowupTower.append_assoc] using
            processed_mask_append_emptyAware_of_row_embedding hn hW hE hdense _ hPrevTest hPrevFull hχ
              E' e hSlots (mask a) S' S hBlock.1 hBlock'.2.1 hBlock.2.1 hBlock'.2.2 hBlock.2.2

end
end Hironaka.HironakaG4PaddedProcessedMaskHistory
