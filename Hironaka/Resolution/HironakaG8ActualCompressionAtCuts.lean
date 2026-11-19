import Hironaka.Resolution.HironakaG8CompressionAtCuts
import Hironaka.Resolution.HironakaG8EmptyAwareTestTransport

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8ActualCompressionAtCuts

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  MarkedIdealTowerTransport MarkedIdealOpenBiholomorphism
  BlowupTowerIsomorphism G3UniverseEmptyAwareCore HironakaStageCenters
  HironakaG8EmptyAwareTestTransport HironakaG8CompressionAtCuts

variable {n : ℕ} {B X Y Z : CMfd.{0} n}

/-- The exact cut witnesses of a compression that retains the middle
occupied history as a strict transport. -/
structure ActualCompressionAtCuts (M : MarkedIdeal n B)
    (P : BlowupTower B X) (L : BlowupTower X Y) (S : BlowupTower Y Z) where
  X' : CMfd.{0} n
  Y' : CMfd.{0} n
  Z' : CMfd.{0} n
  head : BlowupTower B X'
  middle : BlowupTower X' Y'
  tail : BlowupTower Y' Z'
  headMap : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X
  middleMap : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y
  terminalMap : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z
  headComparison : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) B ∞) head P headMap
  middleComparison : IsTowerIso headMap middle L middleMap
  tailComparison : EmptyAwareTowerIso middleMap tail S terminalMap
  headOccupied : StageCentres (fun _ C => C.Nonempty) head
  middleOccupied : StageCentres (fun _ C => C.Nonempty) middle
  tailOccupied : StageCentres (fun _ C => C.Nonempty) tail
  test : IsGeoTestTower M ((head.append middle).append tail)

private theorem occupied_of_iso {A B Y₁ Y₂ : CMfd.{0} n}
    {α : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {β : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    {T : BlowupTower A Y₁} {S : BlowupTower B Y₂} (h : IsTowerIso α T S β)
    (hS : StageCentres (fun _ C => C.Nonempty) S) :
    StageCentres (fun _ C => C.Nonempty) T := by
  induction h with
  | refl => trivial
  | @step K₁ K₂ W₁ W₂ T₁ T₂ e h C₁ π₁ hπ₁ C₂ π₂ hπ₂ f hc hC ih =>
    refine ⟨ih hS.1,?_⟩
    rw [← hC]
    exact hS.2.preimage e.surjective

/-- Compress the head and the suffix of an actual TEST and keep its
occupied middle as a genuine strictly compared history. -/
theorem exists_actual_compression_at_cuts (M : MarkedIdeal n B) (hM : M.IsWellFormed)
    (P : BlowupTower B X) (L : BlowupTower X Y) (S : BlowupTower Y Z)
    (hL : StageCentres (fun _ C => C.Nonempty) L)
    (hTest : IsGeoTestTower M ((P.append L).append S)) :
    Nonempty (ActualCompressionAtCuts M P L S) := by
  let idB := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) B ∞
  obtain ⟨X',P',p,hPO,_,hP,_⟩ := test_empty_free_compression M hM P
  let V := transport (X' := X') p L
  have hV := transport_isTowerIso (X' := X') p L
  let M' := geoTransformAlong M (P.append L)
  have hTestHead := ((isGeoTestTower_append_iff (𝔪 := M) (P.append L) S).mp hTest).1
  have hM' : M'.IsWellFormed := isWellFormed_geoTransformAlong hM _ hTestHead
  obtain ⟨Z',S',s,hSO,_,hS,_⟩ := test_empty_free_compression M' hM' S
  let K := transport (X' := V.target) V.back S'
  have hK := transport_isTowerIso (X' := V.target) V.back S'
  have hc := G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso hK) hS
  have hBase : V.back.trans (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞) = V.back := by ext x; rfl
  rw [hBase] at hc
  have hWhole := append_emptyAware (append_emptyAware hP (emptyAware_of_isTowerIso hV)) hc
  have hIff := isGeoTestTower_iff_of_emptyAware M hM idB hWhole
  have hId : MarkedIdeal.pullback idB M = M := ContactCanonicalAlong.pullback_id M hM.isCoherent
  rw [hId] at hIff
  exact ⟨⟨X',V.target,K.target,P',V.tower,K.tower,p,V.back,K.back.trans s,
    hP,hV,hc,hPO,occupied_of_iso hV hL,occupied_of_iso hK hSO,hIff.mpr hTest⟩⟩

end Hironaka.HironakaG8ActualCompressionAtCuts
