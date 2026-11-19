import Hironaka.Resolution.HironakaG3UniverseEmptyAwareNonempty
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareAlgebra
import Hironaka.Resolution.HironakaG8FirstFootprintOrder
import Hironaka.Resolution.HironakaSharpActualCurveFiniteRecipeComparison

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CompressionAtCuts

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism G3UniverseEmptyAwareCore G3UniverseEmptyAwareNonempty
  HironakaStageCenters HironakaSharpActualCurveFiniteRecipeComparison

variable {n : ℕ} {A B X Y Z W F G : CMfd.{0} n}

/-- Empty-aware comparison composes across literal concatenation and
keeps the specified maps at the cut and at the terminal stage. -/
theorem append_emptyAware
    {φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    {P : BlowupTower A X} {Q : BlowupTower B Y}
    (hP : EmptyAwareTowerIso φ P Q e)
    {S : BlowupTower X Z} {T : BlowupTower Y W}
    {f : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ W}
    (hS : EmptyAwareTowerIso e S T f) :
    EmptyAwareTowerIso φ (P.append S) (Q.append T) f := by
  induction hS with
  | refl => exact hP
  | step _ hπ hρ χ hComm hC ih => exact .step ih hπ hρ χ hComm hC
  | leftEmpty _ hπ χ hχ ih => exact .leftEmpty ih hπ χ hχ
  | rightEmpty _ hπ χ hχ ih => exact .rightEmpty ih hπ χ hχ

/-- Any two chosen empty-free compressions of a given empty-aware
comparison have a strict comparison, with its exact conjugated map. -/
theorem strict_between_chosen_compressions
    {P : BlowupTower A X} {Q : BlowupTower B Y} {S : BlowupTower A Z} {T : BlowupTower B W}
    {φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    {α : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {β : W ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (h : EmptyAwareTowerIso φ P Q e)
    (hS : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞) S P α)
    (hT : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) B ∞) T Q β)
    (hSO : StageCentres (fun _ C => C.Nonempty) S) (hTO : StageCentres (fun _ C => C.Nonempty) T) :
    IsTowerIso φ S T ((α.trans e).trans β.symm) := by
  have hAlt := G3UniverseEmptyAwareCore.trans (G3UniverseEmptyAwareCore.trans hS h)
    (G3UniverseEmptyAwareCore.symm hT)
  have hBase : ((Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞).trans φ).trans
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) B ∞).symm = φ := by ext z; rfl
  rw [hBase] at hAlt
  exact isTowerIso_of_emptyAware_nonempty hAlt hSO hTO

/-- Concatenation of two empty-free actual histories stays empty-free. -/
theorem stageCentres_nonempty_append
    {P : BlowupTower A X} {S : BlowupTower X Z}
    (hP : StageCentres (fun _ C => C.Nonempty) P)
    (hS : StageCentres (fun _ C => C.Nonempty) S) :
    StageCentres (fun _ C => C.Nonempty) (P.append S) := by
  induction S with
  | refl => exact hP
  | step S C π hπ ih => exact ⟨ih hS.1,hS.2⟩

/-- A complete compression can be compared directly to one built by
compressing the head and tail while carrying the actual occupied pair.
The strict map is unique and has the exact conjugated endpoint. -/
theorem strict_compression_at_two_cuts
    {φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {P : BlowupTower B X} {L : BlowupTower X Z} {S : BlowupTower Z F}
    {P' : BlowupTower B Y} {L' : BlowupTower Y W} {S' : BlowupTower W G}
    {C₀ C₁ : CMfd.{0} n} {T : BlowupTower A C₀} {T' : BlowupTower A C₁}
    {e : C₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ F}
    {α : C₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ C₀}
    {p : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {l : W ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    {s : G ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ F}
    (h : EmptyAwareTowerIso φ T ((P.append L).append S) e)
    (hT : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞) T' T α)
    (hP : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) B ∞) P' P p)
    (hL : IsTowerIso p L' L l) (hS : EmptyAwareTowerIso l S' S s)
    (hTO : StageCentres (fun _ C => C.Nonempty) T')
    (hPO : StageCentres (fun _ C => C.Nonempty) P')
    (hLO : StageCentres (fun _ C => C.Nonempty) L')
    (hSO : StageCentres (fun _ C => C.Nonempty) S') :
    IsTowerIso φ T' ((P'.append L').append S') ((α.trans e).trans s.symm) ∧
      ∀ χ, IsTowerIso φ T' ((P'.append L').append S') χ → χ = ((α.trans e).trans s.symm) := by
  have hBuilt := append_emptyAware (append_emptyAware hP (emptyAware_of_isTowerIso hL)) hS
  have hOcc := stageCentres_nonempty_append (stageCentres_nonempty_append hPO hLO) hSO
  have hh := strict_between_chosen_compressions h hT hBuilt hTO hOcc
  exact ⟨hh,fun _ hc => actual_tower_comparison_unique hc hh⟩

end Hironaka.HironakaG8CompressionAtCuts
