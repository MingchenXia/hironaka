/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveStoppedPrefixOpenNaturality

/-! True matching terminal opens and actual whole-history comparisons
precede the chosen stopped-stage/terminal atlas transition square. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveStoppedAtlasTransition
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail BlowupTowerSplitIso
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformPrefixRestriction
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveComparisonRestriction
  HironakaSharpActualCurveStoppedStageTerminalRanges HironakaSharpActualCurveFiniteRecipeComparison
  HironakaSharpActualCurveStoppedPrefixOpenNaturality HironakaSharpActualCurveExactTerminalRepadding
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

private theorem stopped_terminal_open_eq (T : BlowupTower X Y) (U : Opens X)
    (k : ℕ) (hk : T.length≤k) :
    (openPreimage (uniformPrefix T k).2 U : Set (uniformPrefix T k).1)=
      (stoppedPrefixBiholomorphism T k hk) ⁻¹' (openPreimage T U : Set Y) := by
  ext z
  change (uniformPrefix T k).2.proj z∈U ↔ T.proj (stoppedPrefixBiholomorphism T k hk z)∈U
  rw [stoppedPrefixBiholomorphism_projection]

def stoppedTerminalOpenBiholomorphism (T : BlowupTower X Y) (U : Opens X)
    (k : ℕ) (hk : T.length≤k) :
    CMfd.of (n := n) (openPreimage (uniformPrefix T k).2 U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T U) :=
  openRestriction (stoppedPrefixBiholomorphism T k hk)
    (openPreimage (uniformPrefix T k).2 U) (openPreimage T U) (stopped_terminal_open_eq T U k hk)

theorem stoppedTerminalOpenBiholomorphism_val (T : BlowupTower X Y) (U : Opens X)
    (k : ℕ) (hk : T.length≤k) (z : openPreimage (uniformPrefix T k).2 U) :
    (stoppedTerminalOpenBiholomorphism T U k hk z).val=stoppedPrefixBiholomorphism T k hk z.val := rfl

theorem stoppedTerminalOpenBiholomorphism_flattening (T : BlowupTower X Y) (U : Opens X)
    (k : ℕ) (hk : T.length≤k)
    (f : (uniformPrefix (restrict U T) k).1
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (uniformPrefix T k).2 U))
    (hf : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      (uniformPrefix (restrict U T) k).2 (restrict U (uniformPrefix T k).2) f)
    (z : (uniformPrefix (restrict U T) k).1) :
    stoppedTerminalOpenBiholomorphism T U k hk (f z)=
      stoppedPrefixBiholomorphism (restrict U T) k (by rw [length_restrict];exact hk) z :=
  Subtype.ext (stoppedPrefix_open_terminal_square T U k hk f hf z)

/-- The terminal and stage maps here are genuine full comparisons, not
assumed point squares or arbitrary maps over an original projection. -/
theorem stopped_restricted_comparison_square (T' : BlowupTower X' Y') (T : BlowupTower X Y)
    (U' : Opens X') (U : Opens X)
    {Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U}
    {χ : CMfd.of (n := n) (openPreimage T' U')
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T U)}
    (r' r k : ℕ)
    (hPadded : IsTowerIso Φ ((restrict U' T').append (identityEmptyTail (CMfd.of (n := n) (openPreimage T' U')) r'))
      ((restrict U T).append (identityEmptyTail (CMfd.of (n := n) (openPreimage T U)) r)) χ)
    (hk' : T'.length≤k) (hk : T.length≤k)
    (ψ : CMfd.of (n := n) (openPreimage (uniformPrefix T' k).2 U')
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (uniformPrefix T k).2 U))
    (hψ : IsTowerIso Φ (restrict U' (uniformPrefix T' k).2) (restrict U (uniformPrefix T k).2) ψ)
    (z : openPreimage (uniformPrefix T' k).2 U') :
    stoppedTerminalOpenBiholomorphism T U k hk (ψ z)=χ (stoppedTerminalOpenBiholomorphism T' U' k hk' z) := by
  obtain ⟨f',hf',_hfUnique'⟩ := exists_unique_uniformPrefix_open_restriction T' U' k
  obtain ⟨f,hf,_hfUnique⟩ := exists_unique_uniformPrefix_open_restriction T U k
  let Ψ := f'.trans (ψ.trans f.symm)
  have hComposite := hf'.trans (hψ.trans hf.symm)
  have hΨ := BlowupTowerSplitIso.IsTowerIso.congr_base hComposite (Φ' := Φ) (fun _ => rfl)
  let z' := f'.symm z
  have hFull := stopped_chosen_comparison_terminal_square (restrict U' T') (restrict U T) r' r k hPadded
    (by rw [length_restrict];exact hk') (by rw [length_restrict];exact hk) Ψ hΨ z'
  have hSrc := stoppedTerminalOpenBiholomorphism_flattening T' U' k hk' f' hf' z'
  have hSrc' : stoppedPrefixBiholomorphism (restrict U' T') k (by rw [length_restrict];exact hk') z'=
      stoppedTerminalOpenBiholomorphism T' U' k hk' z :=
    hSrc.symm.trans (congrArg (stoppedTerminalOpenBiholomorphism T' U' k hk') (f'.apply_symm_apply z))
  have hTarget : f (Ψ z')=ψ z :=
    (f.apply_symm_apply (ψ (f' z'))).trans (congrArg ψ (f'.apply_symm_apply z))
  calc
    stoppedTerminalOpenBiholomorphism T U k hk (ψ z)=
        stoppedTerminalOpenBiholomorphism T U k hk (f (Ψ z')) :=
      congrArg (stoppedTerminalOpenBiholomorphism T U k hk) hTarget.symm
    _=stoppedPrefixBiholomorphism (restrict U T) k (by rw [length_restrict];exact hk) (Ψ z') :=
      stoppedTerminalOpenBiholomorphism_flattening T U k hk f hf (Ψ z')
    _=χ (stoppedPrefixBiholomorphism (restrict U' T') k (by rw [length_restrict];exact hk') z') := hFull
    _=χ (stoppedTerminalOpenBiholomorphism T' U' k hk' z) := congrArg χ hSrc'

open HironakaSharpActualCurveUniformStageAtlas HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveEndpointGeometry HironakaSharpActualCurveOriginalRecipeAtlas
  HironakaSharpActualCurveOverlapMaps HironakaSharpActualCurveCommonOpenCocycle
  HironakaSharpActualCurveChosenOverlapCocycle MaxLocusLocal

private theorem refl_padded_stagewise (U V : Opens X)
    {Yi Yj : CMfd.{u} n}
    (Pi : BlowupTower (CMfd.of (n := n) U) Yi)
    (Pj : BlowupTower (CMfd.of (n := n) V) Yj)
    (e : localEndpoint U (U⊓V) Pi .refl
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ localEndpoint V (U⊓V) Pj .refl)
    (he : IsTowerIso (commonOpenBase U V (U⊓V) inf_le_left inf_le_right)
      (localPaddedHistory U (U⊓V) Pi .refl 0) (localPaddedHistory V (U⊓V) Pj .refl 0) e) :
    IsTowerIso (commonOpenBase U V (U⊓V) inf_le_left inf_le_right)
      (restrict (nestedOpens U (U⊓V)) Pi) (restrict (nestedOpens V (U⊓V)) Pj) e := he

/-- Domain membership follows from the actual stopped original projection. -/
theorem stoppedPoint_overlap_mem {J : Type u} (A : ActualEndpointHistories X J)
    (i j : J) (k : ℕ) (hki : ((A.prefixTower i).append (A.tail i)).length≤k)
    (z : overlapOpen (uniformStageHistories A k) i j) :
    stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hki z.val∈overlapOpen A i j := by
  have hp := congrArg Subtype.val
    (stoppedPrefixBiholomorphism_projection ((A.prefixTower i).append (A.tail i)) k hki z.val)
  rw [BlowupTower.proj_append] at hp
  change (A.prefixTower i).proj ((A.tail i).proj
    (stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hki z.val))∈
      (Subtype.val : A.openSet i → X) ⁻¹' (A.openSet j : Set X)
  have hz : (((uniformPrefix ((A.prefixTower i).append (A.tail i)) k).2.proj z.val) : X)∈A.openSet j :=
    z.property
  change (((A.prefixTower i).proj ((A.tail i).proj
    (stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hki z.val))) : X)∈A.openSet j
  change (((A.prefixTower i).proj ((A.tail i).proj
    (stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hki z.val))) : X)=
    (((uniformPrefix ((A.prefixTower i).append (A.tail i)) k).2.proj z.val) : X) at hp
  rw [hp]
  exact hz

/-- SAME already chosen stage and terminal transitions, on EVERY actual overlap point. -/
theorem stoppedAtlasTransition_square {J : Type u} (A : ActualEndpointHistories X J)
    (i j : J) (k : ℕ) (hki : ((A.prefixTower i).append (A.tail i)).length≤k)
    (hkj : ((A.prefixTower j).append (A.tail j)).length≤k)
    (z : overlapOpen (uniformStageHistories A k) i j) :
    stoppedPrefixBiholomorphism ((A.prefixTower j).append (A.tail j)) k hkj
        (transition (uniformStageHistories A k) i j z).val=
      (transition A i j ⟨stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hki z.val,
        stoppedPoint_overlap_mem A i j k hki z⟩).val := by
  let Ui := nestedOpens (A.openSet i) (A.openSet i⊓A.openSet j)
  let Uj := nestedOpens (A.openSet j) (A.openSet i⊓A.openSet j)
  let Ti := (A.prefixTower i).append (A.tail i)
  let Tj := (A.prefixTower j).append (A.tail j)
  let ri := A.cut i j-(A.tail i).length
  let rj := A.cut i j-(A.tail j).length
  let fi := opensCongr (n := n) (openPreimage_append (A.prefixTower i) (A.tail i) Ui).symm
  let fj := opensCongr (n := n) (openPreimage_append (A.prefixTower j) (A.tail j) Uj).symm
  have hfi := (isTowerIso_restrict_append Ui (A.prefixTower i) (A.tail i)).append
    (identityEmptyTail_isTowerIso fi ri)
  have hfj := (isTowerIso_restrict_append Uj (A.prefixTower j) (A.tail j)).append
    (identityEmptyTail_isTowerIso fj rj)
  have hOld := A.stagewise i j
  dsimp only [localPaddedHistory,paddedHistory] at hOld
  rw [←BlowupTower.append_assoc,←BlowupTower.append_assoc] at hOld
  simp only [length_restrict] at hOld
  have hCanonical := hfi.trans (hOld.trans hfj.symm)
  have hPadded := BlowupTowerSplitIso.IsTowerIso.congr_base hCanonical
    (Φ' := commonOpenBase (A.openSet i) (A.openSet j) (A.openSet i⊓A.openSet j) inf_le_left inf_le_right)
    (fun _ => rfl)
  let Ak := uniformStageHistories A k
  have hStage := refl_padded_stagewise (A.openSet i) (A.openSet j)
    (uniformPrefix Ti k).2 (uniformPrefix Tj k).2 (Ak.comparison i j) (Ak.stagewise i j)
  let q := opensCongr (n := n) (endpointOverlapOpen_eq_pair (A.openSet i) (A.openSet j)
    (uniformPrefix Ti k).2 .refl) z
  have hRaw := stopped_restricted_comparison_square Ti Tj Ui Uj ri rj k hPadded hki hkj
    (Ak.comparison i j) hStage q
  let qOld := opensCongr (n := n) (endpointOverlapOpen_eq_pair (A.openSet i) (A.openSet j)
    (A.prefixTower i) (A.tail i))
    ⟨stoppedPrefixBiholomorphism Ti k hki z.val,stoppedPoint_overlap_mem A i j k hki z⟩
  have hOldArg : fi (stoppedTerminalOpenBiholomorphism Ti Ui k hki q)=qOld := Subtype.ext rfl
  have hPoint := congrArg Subtype.val hRaw
  change stoppedPrefixBiholomorphism Tj k hkj (transition Ak i j z).val=
    (A.comparison i j (fi (stoppedTerminalOpenBiholomorphism Ti Ui k hki q))).val at hPoint
  rw [hOldArg] at hPoint
  exact hPoint

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- ONLY original geometry internally supplies BOTH actual histories and the SAME chosen maps. -/
theorem originalStoppedAtlasTransition_square (x y : X) (r : ℕ) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let Li := ((A.prefixTower x).append (A.tail x)).length
    let Lj := ((A.prefixTower y).append (A.tail y)).length
    let k := Li+Lj+r
    ∀ z : overlapOpen (uniformStageHistories A k) x y,
      stoppedPrefixBiholomorphism ((A.prefixTower y).append (A.tail y)) k (by omega)
          (transition (uniformStageHistories A k) x y z).val=
        (transition A x y ⟨stoppedPrefixBiholomorphism ((A.prefixTower x).append (A.tail x)) k (by omega) z.val,
          stoppedPoint_overlap_mem A x y k (by omega) z⟩).val := by
  dsimp only
  intro z
  exact stoppedAtlasTransition_square (originalEndpointHistories hn hW hE hdense hr) x y _
    (by omega) (by omega) z

end OriginalInput

end
end Hironaka.HironakaSharpActualCurveStoppedAtlasTransition
