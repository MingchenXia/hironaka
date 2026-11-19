import Hironaka.Resolution.HironakaG4OrderedProcessedMaskHistory
import Hironaka.Resolution.HironakaG4ProcessedStateRestriction

/-! Physical base changes retain the same ordered canonical mask phases and
their true marked ideals at every phase boundary. -/

set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4OrderedProcessedMaskRebase

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealTowerTransport MarkedIdealRestrictOpen
  HomogenizedGlueingTower NormalCrossings NormalCrossingsInvariance
  HironakaG34NonPureLowDim HironakaSharpActualFiniteChronologicalHistory
  HironakaG3EmptyAwareHistory HironakaG4ProcessedMaskFilteredPrefix
  HironakaG4ProcessedMaskRestriction HironakaG4OrderedProcessedMaskHistory
  HironakaActualProcessedMaskControlledSum HironakaOriginalBoundaryEmptyFilterComparison
  CanonicalCentres InvDomainTowerAlong
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X X' Y Y' : CMfd.{u} n} {ι : Type v}

/-- A literal tower isomorphism preserves the entire marked mask, including
the full chronological born list. -/
theorem processed_mask_pullback_of_isTowerIso (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    {T' : BlowupTower X' Y'} {ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hIso : IsTowerIso φ T' T ψ) (P : Finset (Fin E.length)) :
    let E' := E.map (φ ⁻¹' ·)
    let e : Fin E.length ≃ Fin E'.length := finCongr (List.length_map _).symm
    let M' := processedMaskMarked (φ ⁻¹' W) E' T' (P.map e.toEmbedding)
    let M := processedMaskMarked W E T P
    M' = MarkedIdeal.pullback ψ M := by
  intro E' e M' M
  have hFilter := processed_mask_eq_after_filter_of_emptyAware hn hW hE hdense T hT hFull
    (emptyAware_of_isTowerIso hIso) P
  have hWhole := IsTowerIso.geoTransformAlong_eq φ hW IdealWeightPowers.isCoherent_unitIdeal hIso hT
  rw [template_pullback,List.map_nil] at hWhole
  have hN := congrArg (fun M₀ : MarkedIdeal n Y' => M₀.N) hFilter
  have hE' := congrArg (fun M₀ : MarkedIdeal n Y' => M₀.E) hWhole
  have hIdeal := congrArg (fun M₀ : MarkedIdeal n Y' => M₀.ideal) hFilter
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN hE' hIdeal rfl

/-- Transport a complete ordered continuation through an actual initial
prefix isomorphism, keeping every physical phase. -/
theorem ordered_processed_rebase (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (T : BlowupTower X Y) (T' : BlowupTower X' Y')
    {ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hIso : IsTowerIso φ T' T ψ) (mask : ι → Finset (Fin E.length)) :
    ∀ (L : List ι) {Z : CMfd.{u} n} (Q : BlowupTower Y Z),
      let E' := E.map (φ ⁻¹' ·)
      let e : Fin E.length ≃ Fin E'.length := finCongr (List.length_map _).symm
      IsGeoTestTower (geometricTemplate W []) (T.append Q) →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) →
      OrderedProcessedMaskHistory hn W E T mask Q L →
      ∃ (Z' : CMfd.{u} n) (Q' : BlowupTower Y' Z')
        (χ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z),
        IsTowerIso φ (T'.append Q') (T.append Q) χ ∧
        OrderedProcessedMaskHistory hn (φ ⁻¹' W) E' T' (fun a => (mask a).map e.toEmbedding) Q' L := by
  dsimp only
  intro L
  induction L with
  | nil =>
    intro Z Q _hTest _hFull hQ
    cases hQ
    exact ⟨Y',.refl,ψ,hIso,.nil⟩
  | cons label L ih =>
    intro Z Q hTest hFull hQ
    cases hQ with
    | snoc _ S hPrev hBlock =>
      rw [←BlowupTower.append_assoc] at hTest hFull
      have hPrevTest := ((isGeoTestTower_append_iff _ _ S).mp hTest).1
      have hPrevFull := ((isGeoTestTower_append_iff _ _ S).mp hFull).1
      obtain ⟨A',P',χ,hχ,hHist⟩ := ih _ hPrevTest hPrevFull hPrev
      have hEq := processed_mask_pullback_of_isTowerIso hn hW hE hdense _ hPrevTest hPrevFull hχ (mask label)
      let S' := transport χ S
      have hSiso := transport_isTowerIso χ S
      have hDom := isInvDomain_pullback χ hBlock.1
      have hCan := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
        (invFamily hn (n+1)) hBlock.1 χ hSiso hBlock.2.1
      have hRes := (IsTowerIso.isGeoResolution_iff χ hBlock.1.isWellFormed.isClosedSubmanifold_N
        hBlock.1.isWellFormed.isCoherent hSiso).mpr hBlock.2.2
      refine ⟨S'.target,P'.append S'.tower,S'.back,?_,OrderedProcessedMaskHistory.snoc label _ hHist ?_⟩
      · simpa only [BlowupTower.append_assoc] using hχ.append hSiso
      · dsimp only at hEq ⊢
        rw [hEq]
        exact ⟨hDom,hCan,hRes⟩

/-- Concatenation retains the exact current mask of every chronological
phase in the two continuations. -/
theorem ordered_processed_append (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (T : BlowupTower X Y) {Z : CMfd.{u} n} (Q : BlowupTower Y Z)
    (mask : ι → Finset (Fin E.length)) (L : List ι)
    (hQ : OrderedProcessedMaskHistory hn W E T mask Q L) :
    ∀ {A : CMfd.{u} n} (S : BlowupTower Z A) (L' : List ι),
      OrderedProcessedMaskHistory hn W E (T.append Q) mask S L' →
      OrderedProcessedMaskHistory hn W E T mask (Q.append S) (L' ++ L) := by
  intro A S L' hS
  induction hS with
  | nil => exact hQ
  | snoc label R _ hBlock ih =>
    rw [←BlowupTower.append_assoc]
    exact OrderedProcessedMaskHistory.snoc label R ih
      (by simpa only [BlowupTower.append_assoc] using hBlock)

end
end Hironaka.HironakaG4OrderedProcessedMaskRebase
